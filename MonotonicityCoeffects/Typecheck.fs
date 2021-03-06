﻿module Typecheck

open PCF
open Ast
open Kindcheck
open CheckComputation

module P = PCF

type ValueEnvironment = Map<string, Ty>
type PrimValueEnvironment = Map<string, Ty * P.Term>
type Context = { tenv : TypeEnvironment ; venv : ValueEnvironment ; bvenv : PrimValueEnvironment ; src : string }

type CoeffectMap = Map<string, Coeffect>

type typeCheckResult =
    | Success of Ty * Map<string, Coeffect>
    | Failure of List<string*Range>

/// Vector/vector coeffect contraction
let contr (a : Map<string, Coeffect>) (b : Map<string, Coeffect>) : Map<string, Coeffect> =
    assert (a.Count = b.Count)
    let foldCoeffectA (acc : Map<string, Coeffect>) (id : string) (q : Coeffect) =
        match b.TryFind id with
        | Some(r) ->
            acc.Add(id, q ++ r)
        | None ->
            failwith "unreachable"
    Map.fold foldCoeffectA Map.empty a

/// Scalar/vector coeffect composition
let comp (q : Coeffect) (a : Map<string, Coeffect>) : Map<string, Coeffect> =
    Map.map (fun k r -> (q %% r)) a


/// Gets the substring of source code which expr was parsed from
let getSource (ctxt : Context) (expr : Expr) : string =
    let (lo, hi) = expr.GetRange()
    ctxt.src.Substring(lo.AbsoluteOffset, hi.AbsoluteOffset - lo.AbsoluteOffset)

let foundHole : Ref< Option<Context * Range> > = ref None
    
let rec typeCheck (ctxt : Context) (expr : Expr) : Check<Ty * CoeffectMap * P.Term> =
    let tenv,venv = ctxt.tenv, ctxt.venv
    let tyVarEnv, tyBaseEnv = tenv.tyVarEnv, tenv.tyBaseEnv
    let errorMsg = "Expression not well-typed:\n\n" + (getSource ctxt expr) + "\n\n"
    match expr with
    | Int(n, rng) ->
        if n >= 0 then
            Result (TyId("Nat", noRange), Map.map (fun k v -> Coeffect.Ign) venv, P.PrimNatVal(n))
        else
            Error ["Negative integer constants not allowed", rng]
    | UInt(n , rng) ->
        if n >= 0 then
            Result (TyId("NatU", noRange), Map.map (fun k v -> Coeffect.Ign) venv, P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n)))
        else
            Error ["Negative integer constants not allowed", rng]        
    | Prop(b,rng) ->
        Result (TyId("Prop", noRange), Map.map (fun k v -> Coeffect.Ign) venv, makePcfProp b)
    | Forall(tyVarId, pk, body, rng) ->
        check {
            let tyVarEnv' = 
                match pk with 
                | Semilattice ->
                    let env' = Map.add tyVarId pk tyVarEnv
                    Map.add (tyVarId + "Delta") Poset env'
                | _ ->
                    Map.add tyVarId pk tyVarEnv
            let tenv' = { tenv with tyVarEnv = tyVarEnv' }
            let! ty, qs, term = withError (errorMsg + ": body is not well-typed") rng (typeCheck { ctxt with tenv = tenv' } body)
            let term2 = 
                let pTyVar = P.TyVar("$" + tyVarId)
                match pk with
                | Poset ->
                    P.Forall("$" + tyVarId, term)
                | Toset ->
                    P.Forall("$" + tyVarId, P.Abs("$" + tyVarId + "_comp", P.Fun(pTyVar, P.Fun(pTyVar, P.pBoolTy)), term))
                | Semilattice ->
                     P.Forall("$" + tyVarId,
                        P.Abs("$" + tyVarId + "_bot", pTyVar, 
                            P.Abs("$" + tyVarId + "_join", P.Fun(pTyVar, P.Fun(pTyVar, pTyVar)), 
                                P.Forall("$" + tyVarId + "Delta", 
                                    P.Abs("$" + tyVarId + "_iso", P.Fun(pTyVar, P.List(P.TyVar("$" + tyVarId + "Delta"))), 
                                        P.Abs("$" + tyVarId + "_prom", P.Fun(P.TyVar("$" + tyVarId + "Delta"), pTyVar), term))))))

            return (ForallTy(tyVarId, pk, ty, noRange), qs, term2)
        }
    | ForallApp(forallExpr, tyArg, rng) ->
        check {
            let! tyForall, qsForall, termForall = withError (errorMsg + ": left-hand side not well-typed") rng (typeCheck ctxt forallExpr)
            let! id, body, pkExpected = 
                match tyForall with
                | ForallTy(id,pk,body,_) ->
                    Result (id, body, pk) 
                | _ ->
                    Error [errorMsg + ": " + tyForall.ToString() + " is not a forall type", rng]
            let ty' = Ty.subst tyArg id body
            match pkExpected with
            | Poset ->
                let! pTy = withError errorMsg rng (kCheckProset ctxt.tenv tyArg)
                let term' = P.TyApp(termForall, pTy)
                return (ty', qsForall,  term')
            | Toset ->
                let! pTy, pComp = withError errorMsg rng (kCheckToset ctxt.tenv tyArg)
                let term' = P.TyApp(termForall, pTy)
                let term'' = P.App(term', pComp)
                return (ty', qsForall, term'')
            | Semilattice ->
                let! pTy, pBot, pJoin, deltaTy, pIso, pProm = withError errorMsg rng (kCheckSemilattice ctxt.tenv tyArg)
                let term1 = P.TyApp(termForall, pTy)
                let term2 = P.App(term1, pBot)
                let term3 = P.App(term2, pJoin)
                let! pDeltaTy = kCheckProset ctxt.tenv deltaTy
                let term4 = P.TyApp(term3, pDeltaTy)
                let term5 = P.App(term4, pIso)
                let term6 = P.App(term5, pProm)
                return (ty', qsForall, term6)
        }
    | Hom(var, semilatTy, ascribedDeltaTy, body, rng) ->
        check {
            let! pSemilatTy, _, _, computedDeltaTy, pIso, pDelta = 
                withError ("type annotation " + semilatTy.ToString() + " is not a well-formed semilattice type") 
                          rng 
                         (kCheckSemilattice ctxt.tenv semilatTy)
            do! withError (errorMsg + "ascribed delta type " + ascribedDeltaTy.ToString() + " does not match the delta type " 
                           + computedDeltaTy.ToString() + " of " + semilatTy.ToString())
                          rng
                          (Ty.IsEquiv ctxt.tenv.tyAliasEnv ascribedDeltaTy computedDeltaTy)
            let! pComputedDeltaTy = kCheckProset ctxt.tenv computedDeltaTy
            let venv' = Map.add var computedDeltaTy venv
            let! targetTy,qs,term = withError (errorMsg + ": body not well-typed") rng (typeCheck { ctxt with venv = venv' } body)
            let! pTargetTy, pTargetBot, pTargetJoin, _, _, _ = 
                withError 
                    ("homomorphism codomains must be semilattice types, but computed codomain " + targetTy.ToString() + 
                     " is not") 
                    rng
                    (kCheckSemilattice ctxt.tenv targetTy)
            match qs.TryFind(var) with // None case unreachable
            | Some(q) ->
                let ty' = FunTy(semilatTy, q, targetTy, noRange)
                let qs' = if ctxt.venv.ContainsKey(var) then Map.add var CoeffectRobust qs else Map.remove var qs                
                let pMapDelta = P.Abs(var, pComputedDeltaTy, term)
                let pDeltas = P.App(pIso, P.Var("!x"))
                let pMappedDeltas = forEach pComputedDeltaTy pTargetTy pMapDelta pDeltas
                let pResult = P.fold pTargetTy pTargetTy pTargetJoin pMappedDeltas pTargetBot
                let pHom = P.Abs("!x", pSemilatTy, pResult)
                return ty', qs', pHom
        }
    | Abs(var, varTy, body, rng) ->
        check {
            let! kVar = withError ("type annotation " + varTy.ToString() + " is not well-kinded") rng (kSynth ctxt.tenv varTy)
            let! pTyVar,_,_,_ = getProper "argument type" kVar 
            let venv' = Map.add var varTy venv
            let! ty,qs,term = withError (errorMsg + ": body not well-typed") rng (typeCheck { ctxt with venv = venv' } body)
            match qs.TryFind(var) with // None case unreachable
            | Some(q) ->
                let ty' = FunTy(varTy, q, ty, noRange)
                let qs' = if ctxt.venv.ContainsKey(var) then Map.add var CoeffectRobust qs else Map.remove var qs
                let term' = P.Abs(var, pTyVar, term)
                return ty', qs', term'
        }
    | App(fn,arg,rng) ->
        check {
            let! tyFun, qsFun, termFun = withError (errorMsg + ": function position ill-typed") rng (typeCheck ctxt fn)
            let! tyArg, qsArg, termArg = withError (errorMsg + ": argument position ill-typed") rng (typeCheck ctxt arg)
            let! codTy, qs, term =
                match tyFun with
                | FunTy(domTy, q, codTy, _) ->
                    check {
                        do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv tyArg domTy)
                        let qs = contr qsFun (comp q qsArg)
                        let term = P.App(termFun, termArg)
                        return (codTy, qs, term)
                    }
                | _ ->
                    Error [errorMsg + ": " + (getSource ctxt fn) + " has type " + tyFun.ToString() + " and cannot be applied ",rng]
            return codTy, qs, term
        }
    | Var(name,rng) ->
        match venv.TryFind name with
        | Some(ty) ->
            let nameOnlyMono = Map.map (fun k v -> if k = name then Coeffect.Use else Coeffect.Ign) venv
            Result (ty, nameOnlyMono, P.Var(name)) 
        | None ->
            match ctxt.bvenv.TryFind name with
            | Some(ty, pTerm) ->
                Result (ty, Map.map (fun k _ -> Coeffect.Ign) venv, pTerm)
            | _ ->
                Error [errorMsg + ": identifier " + name.ToString() + " undeclared",rng]
    | Bot(ty,rng) ->
        check {
            let! _, pBot, _,_,_,_ = withError errorMsg rng (kCheckSemilattice tenv ty)
            let qsAllIgn = Map.map (fun k v -> Coeffect.Ign) venv
            return ty, qsAllIgn, pBot
        }
    | Join(ty, e1, e2, rng) ->
        check {
            let! _, _, pJoin,_,_,_ = withError errorMsg rng (kCheckSemilattice tenv ty)
            let! ty1, qs1, pTerm1 = withError errorMsg rng (typeCheck ctxt e1)
            let! ty2, qs2, pTerm2 = withError errorMsg rng (typeCheck ctxt e2)
            do! withError errorMsg rng (Ty.IsEquiv ctxt.tenv.tyAliasEnv ty1 ty)
            do! withError errorMsg rng (Ty.IsEquiv ctxt.tenv.tyAliasEnv ty2 ty)
            let term = P.App(P.App(pJoin, pTerm1), pTerm2)
            return ty, contr qs1 qs2, term
        }
    | LessThan(e1, e2, rng) ->
        check {
            let! ty1, Q1, pTerm1 = withError errorMsg rng (typeCheck ctxt e1)
            let! _, pLessThan = withError errorMsg rng (kCheckToset ctxt.tenv ty1)
            let! ty2, Q2, pTerm2 = withError errorMsg rng (typeCheck ctxt e2)
            do! withError (errorMsg + ": left operand type does not match that of right operand type") rng (Ty.IsEquiv ctxt.tenv.tyAliasEnv ty2 ty1)
            let term = P.App(P.App(pLessThan, pTerm1), pTerm2)
            return Sum(TyId("Unit", noRange), TyId("Unit", noRange), noRange), (comp CoeffectAny (contr Q1 Q2)), term
        }
    | Promote(tySemilat, tyDelta, eDelta, rng) ->
        check {
            let! _, _, _, _, _, pProm = withError errorMsg rng (kCheckSemilattice ctxt.tenv tySemilat)
            let! ty, Q, pTerm = withError errorMsg rng (typeCheck ctxt eDelta)
            do! Ty.IsSubtype ctxt.tenv.tyAliasEnv ty tyDelta
            return tySemilat, Q, P.App(pProm, pTerm)
        }
    | Extract(targetTy, key, value, acc, dict, body, rng) ->
        check {
            let! pTargetTy, pTargetBot, pTargetJoin, _, _, _ = 
                withError errorMsg rng (kCheckSemilattice tenv targetTy)
            let! dictTy, dictQ, pDictTerm = 
                withError errorMsg rng (typeCheck ctxt dict)
            let! keyTy, valTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, dictTy) with
                | Dictionary(domTy, codTy, _) ->
                    Result (domTy, codTy)
                | _ ->
                    let errorMsg' = ": dictionary expected for type of " + (getSource ctxt dict) + ", but " + dictTy.ToString() + " computed" 
                    Error [errorMsg + errorMsg',rng]
            let! pKeyTy, pKeyComp = kCheckToset ctxt.tenv keyTy
            let! pValTy = kCheckProset ctxt.tenv valTy
            let venv' = venv.Add(key, keyTy)
            let venv'' = venv'.Add(value, valTy)
            let venv''' = venv''.Add(acc, targetTy)
            let! bodyTy, bodyQ, pBodyTerm = 
                withError errorMsg rng (typeCheck { ctxt with venv = venv''' } body)
            do! Ty.IsSubtype ctxt.tenv.tyAliasEnv bodyTy targetTy
            do! if (Coeffect.LessThan bodyQ.[value] CoeffectMonotone) then
                    Result ()
                else
                    Error ["Expected monotone usage of " + value + " but found " + bodyQ.[value].ToString(), rng]
            do! if (Coeffect.LessThan bodyQ.[acc] CoeffectMonotone) then
                    Result ()
                else
                    Error ["Expected monotone usage of " + acc + " but found " + bodyQ.[acc].ToString(), rng]            
            let resQ = contr dictQ (bodyQ.Remove(acc).Remove(key).Remove(value))
            // pDictTerm, pBodyTerm, pKeyComp, pKeyTy, pValTy, pTargetTy
            let pBodyFun = P.Abs(key, pKeyTy, P.Abs(value, pValTy, P.Abs(acc, pTargetTy, pBodyTerm)))
            let pElemTy = P.Prod(pKeyTy, pValTy)
            let pDictTy = P.List pElemTy
            let pIncTerm = P.App(P.App(P.App(pBodyFun, P.Proj1(P.Var("!h"))), P.Proj2(P.Var("!h"))), P.Var("!acc"))
            let pElim = 
                P.LetRec("!f", "!d", pDictTy, P.Fun(pTargetTy, pTargetTy), P.Abs("!acc", pTargetTy,
                        P.ListCase(
                            P.Var("!d"),
                            pTargetBot,
                            P.Abs("!h",  pElemTy, P.Abs("!t", pDictTy, 
                                P.App(P.App(pTargetJoin, pIncTerm), P.App(P.App(P.Var("!f"), P.Var("!t")), pIncTerm)))))))
            let pResTerm = P.App(P.App(pElim , pDictTerm), pTargetBot)
            return (targetTy, resQ, pResTerm)
        }
    | Cons(e1, e2, e3, rng) ->
        check {
            let! keyTy, keyQ, pKeyTerm = withError errorMsg rng (typeCheck ctxt e1)
            let! valTy, valQ, pValTerm = withError errorMsg rng (typeCheck ctxt e2)
            let! dictTy, dictQ, pDictTerm = withError errorMsg rng (typeCheck ctxt e3)
            let! dKeyTy, dValTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, dictTy) with
                | Dictionary(domTy, codTy,_) ->
                    Result (domTy, codTy)
                | _ ->
                    let errorMsg' = ": type of " + (getSource ctxt e3) + " expected to be dictionary type, but computed " + dictTy.ToString()
                    Error [errorMsg + errorMsg',rng]
            do! withError 
                    (errorMsg + ": key type " + keyTy.ToString() + " is not a subtype of dictionary domain type " + dKeyTy.ToString()) 
                    rng 
                    (Ty.IsSubtype ctxt.tenv.tyAliasEnv keyTy dKeyTy)
            do! withError 
                    (errorMsg + ": value " + (getSource ctxt e2) + "'s type is not a subtype of dictionary codomain " + dValTy.ToString())
                    rng
                    (Ty.IsSubtype ctxt.tenv.tyAliasEnv valTy dValTy)
            let! _, pDictBot, pDictJoin,_,_,_ = kCheckSemilattice ctxt.tenv dictTy
            let resQ = contr (contr (comp CoeffectAny keyQ) valQ) dictQ
            let! pKeyTy = withError errorMsg rng (kCheckProset ctxt.tenv keyTy)
            let! pValTy, _, _, valDeltaTy, pValIso,_ = withError errorMsg rng (kCheckSemilattice ctxt.tenv valTy)
            let! pValDeltaTy = kCheckProset ctxt.tenv valDeltaTy
            //maybe we need a more sophisticated method for accomplishing this?
            let sng = P.Cons(P.Pair(pKeyTerm,pValTerm), P.EmptyList(P.Prod(pKeyTy, pValTy)))
            let pResTerm = 
               P.ListCase(
                 P.App(pValIso, pValTerm),
                 pDictTerm,
                 P.Abs("!h", pValDeltaTy, P.Abs("!t", P.List(pValDeltaTy), P.App(P.App(pDictJoin, sng), pDictTerm))))
            return dictTy, resQ, pResTerm
        }
    | Fst(ePair,rng) ->
        check {
            let! pairTy, pairQ, pPairTerm = withError errorMsg rng (typeCheck ctxt ePair)
            let! resTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, pairTy) with
                | Prod(tyL,_,_) ->
                    Result tyL
                | _ ->
                    Error [errorMsg + ": expected product type, but got " + pairTy.ToString(),rng]
            return resTy, pairQ, P.Proj1(pPairTerm)
        }
    | Snd(ePair,rng) ->
        check {
            let! pairTy, pairQ, pPairTerm = withError errorMsg rng (typeCheck ctxt ePair)
            let! resTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, pairTy) with
                | Prod(_,tyR,_) ->
                    Result tyR
                | _ ->
                    Error [errorMsg + ": expected product type, but got " + pairTy.ToString(),rng]
            return resTy, pairQ, P.Proj2(pPairTerm)
        }
    | LFst(ePair,rng) ->
        check {
            let! pairTy, pairQ, pPairTerm = withError errorMsg rng (typeCheck ctxt ePair)
            let! resTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, pairTy) with
                | LexProd(tyL,_,_) ->
                    Result tyL
                | _ ->
                    Error [errorMsg + ": expected lexicographical product type, but got " + pairTy.ToString(),rng]
            return resTy, pairQ, P.Proj1(pPairTerm)
        }
    | LSnd(ePair,rng) ->
        check {
            let! pairTy, pairQ, pPairTerm = withError errorMsg rng (typeCheck ctxt ePair)
            let! resTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, pairTy) with
                | LexProd(_,tyR,_) ->
                    Result tyR
                | _ ->
                    Error [errorMsg + ": expected lexicographical product type, but got " + pairTy.ToString(),rng]
            return resTy, comp CoeffectAny pairQ, P.Proj2(pPairTerm)
        }
    | Pair(eFst, eSnd, rng) ->
        check {
            let! fstTy, fstQ, pFstTerm = withError errorMsg rng (typeCheck ctxt eFst)
            let! sndTy, sndQ, pSndTerm = withError errorMsg rng (typeCheck ctxt eSnd)
            return Prod(fstTy, sndTy, noRange), contr fstQ sndQ, P.Pair(pFstTerm, pSndTerm)
        }
    | LexPair(eFst, eSnd, rng) ->
        check {
            let! fstTy, fstQ, pFstTerm = withError errorMsg rng (typeCheck ctxt eFst)
            let! sndTy, sndQ, pSndTerm = withError errorMsg rng (typeCheck ctxt eSnd)
            return LexProd(fstTy, sndTy, noRange), contr fstQ sndQ, P.Pair(pFstTerm, pSndTerm)
        }        
    | Case(eScrut, targetTy, lName, lElim, rName, rElim,rng) ->
        check {
            let! scrutTy, scrutQ, pScrutTerm = withError errorMsg rng (typeCheck ctxt eScrut)
            let! lTy, rTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, scrutTy) with
                | Sum(lTy, rTy, _) ->
                    Result (lTy, rTy)
                | _ ->
                    Error [errorMsg + ": case scrutinee should have sum type, but instead found" + scrutTy.ToString(), rng]
            let! pTyL = kCheckProset ctxt.tenv lTy
            let! pTyR = kCheckProset ctxt.tenv rTy
            let venvL = venv.Add(lName, lTy)
            let ctxtL = { ctxt with venv = venvL }
            let! lTy, lQ, plTerm = withError errorMsg rng (typeCheck ctxtL lElim)
            let venvR = venv.Add(rName, rTy)
            let ctxtR = { ctxt with venv = venvR }
            let! rTy, rQ, prTerm = withError errorMsg rng (typeCheck ctxtR rElim)
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv lTy targetTy)
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv rTy targetTy)
            let lQ' = if venv.ContainsKey lName then lQ.Add(lName, CoeffectRobust) else lQ.Remove(lName)
            let rQ' = if venv.ContainsKey rName then rQ.Add(rName, CoeffectRobust) else rQ.Remove(rName)
            return targetTy, contr (contr (comp (lQ.[lName] ++ rQ.[rName]) scrutQ) lQ') rQ', P.SumCase(pScrutTerm, P.Abs(lName, pTyL, plTerm), P.Abs(rName, pTyR, prTerm)) 
        }
    | Inl(lty, rty, expr, rng) ->
        check {
            let! exprTy, exprQ, pExprTerm = withError errorMsg rng (typeCheck ctxt expr)
            let! pTyL = withError errorMsg rng (kCheckProset ctxt.tenv lty)
            let! pTyR = withError errorMsg rng (kCheckProset ctxt.tenv rty)
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv exprTy lty)
            return Sum(lty,rty,noRange), exprQ, P.In1(pTyL, pTyR, pExprTerm)
        }
    | Inr(lty, rty, expr, rng) ->
        check {
            let! exprTy, exprQ, pExprTerm = withError errorMsg rng (typeCheck ctxt expr)
            let! pTyL = withError errorMsg rng (kCheckProset ctxt.tenv lty)
            let! pTyR = withError errorMsg rng (kCheckProset ctxt.tenv rty)
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv exprTy rty)
            return Sum(lty,rty,noRange), exprQ, P.In2(pTyL, pTyR, pExprTerm)
        }
    | Cap(q, e, rng) ->
        check {
            let! eTy, eQ, eTerm = withError errorMsg rng (typeCheck ctxt e)
            return Capsule(eTy, q, noRange), (comp q eQ), eTerm
        }
    | Uncap(q, varId, capsule, body, rng) ->
        check {
            let! capsuleTy, capsuleQ, capsuleTerm = 
                withError errorMsg rng (typeCheck ctxt capsule)
            let! contentsTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, capsuleTy) with
                | Capsule(contentsTy, s, _) when s = q ->
                    Result contentsTy
                | Capsule(_,s,_) ->
                    Error [errorMsg + ": expected a capsule " + q.ToString() + " expression in the binding position, but got a capsule " + s.ToString(), rng]
                | _ ->
                    Error [errorMsg + ": expected an expression of capsule type in the binding position, but got an expression of type " + capsuleTy.ToString(), rng]
            let! pContentsTy = kCheckProset ctxt.tenv contentsTy
            let venv' = venv.Add(varId, contentsTy)
            let! bodyTy, bodyQ, bodyTerm = withError errorMsg rng (typeCheck { ctxt with venv = venv' } body)
            do! 
                match Coeffect.LessThan bodyQ.[varId] q with
                | true ->
                    Result ()
                | false ->
                    Error [(errorMsg + ": " + varId + " has coeffect " + bodyQ.[varId].ToString() + " but coeffect more restrictive than " 
                           + q.ToString() + " expected", rng)]
            return bodyTy, contr capsuleQ (bodyQ.Remove(varId)), P.App(P.Abs(varId, pContentsTy, bodyTerm), capsuleTerm)  
        }
    | ISet(expr, rng) ->
        check {
            let! contentsTy, contentsQ, pContentsTerm = withError errorMsg rng (typeCheck ctxt expr)
            let tosetErrorMsg =
                (errorMsg + ": computed type " + contentsTy.ToString() + " for " + (getSource ctxt expr))
            let! _, _ = withError tosetErrorMsg rng (kCheckToset ctxt.tenv contentsTy)
            let! pContentsTy = withError errorMsg rng (kCheckProset ctxt.tenv contentsTy)
            return IVar(contentsTy, noRange), comp CoeffectAny contentsQ, P.Cons(pContentsTerm, P.EmptyList(pContentsTy))
        }
    | IGet(varId, ivar, body, rng) ->
        check {
            let! ivarTy, ivarQ, pIvarTerm = withError errorMsg rng (typeCheck ctxt ivar)
            let! tyContents =
                match Ty.normalize(ctxt.tenv.tyAliasEnv, ivarTy) with
                | IVar(tyContents,_) ->
                    Result tyContents
                | _ ->
                    Error [errorMsg + ": " + (getSource ctxt expr) + " expected to have ivar type, but type " + ivarTy.ToString() + " was computed.", rng]
            let! pTyContents = kCheckProset ctxt.tenv tyContents
            let venv' = venv.Add(varId, tyContents)
            let! bodyTy, bodyQ, pBodyTerm = withError errorMsg rng (typeCheck { ctxt with venv = venv' } body)
            let! pBodyTy, pBodyBot, _,_,_,_ = kCheckSemilattice ctxt.tenv bodyTy
            let pIvarTy = P.List pTyContents
            let resTerm = 
                P.ListCase(
                    pIvarTerm, 
                    pBodyBot,
                    P.Abs("!hi", pTyContents, P.Abs("!ti", pIvarTy, 
                        P.ListCase(
                            P.Var("!ti"),
                            P.In1(pBodyTy, P.Unit, P.App(P.Abs(varId, pTyContents, pBodyTerm), P.Var("!hi"))),
                            P.Abs("_", pTyContents, P.Abs("_", pIvarTy, P.In2(pBodyTy, P.Unit, P.PrimUnitVal)))))))
            return Exception(bodyTy, noRange), contr ivarQ (bodyQ.Remove(varId)), resTerm
        }
    | Let(varId, bindExpr, bodyExpr, rng) ->
        check {
            let! bindTy, bindQ, pBindTerm = withError errorMsg rng (typeCheck ctxt bindExpr)
            let! pBindTy = kCheckProset ctxt.tenv bindTy
            let venv' = venv.Add(varId, bindTy)
            let! bodyTy, bodyQ, pBodyTerm = withError errorMsg rng (typeCheck { ctxt with venv = venv' } bodyExpr)
            let resTerm = P.App(P.Abs(varId, pBindTy, pBodyTerm), pBindTerm)
            return bodyTy, contr (comp bodyQ.[varId] bindQ) (bodyQ.Remove(varId)), resTerm
        }
    | MLet(varId, exceptionalComputationExpr, bodyExpr, rng) ->
        check {
            let! exceptionalCompTy, exceptionalCompQ, pExceptionalCompTerm =
                withError errorMsg rng (typeCheck ctxt exceptionalComputationExpr)
            let! bindTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, exceptionalCompTy) with
                | Exception(bindTy,_) ->
                    Result bindTy
                | _ ->
                    Error [errorMsg + ": monadic let expected a exceptional computation in body position, but instead got " + exceptionalCompTy.ToString(),rng]
            let! pBindTy = kCheckProset ctxt.tenv bindTy
            let venv' = venv.Add(varId, bindTy)
            let! bodyTy, bodyQ, pBodyTerm = withError errorMsg rng (typeCheck { ctxt with venv = venv' } bodyExpr)
            let! contentsTy = 
                match bodyTy with
                | Exception(contentsTy, _) ->
                    Result contentsTy
                | _ ->
                    Error [errorMsg + ": " + (getSource ctxt bodyExpr) + " expected to be a monotonically exceptional computation, but has type " + bodyTy.ToString() + " instead.", rng]
            let! pContentsTy = kCheckProset ctxt.tenv contentsTy
            do!
                match Coeffect.LessThan bodyQ.[varId] CoeffectMonotone with
                | true ->
                    Result ()
                | false ->
                    Error ["Expected monotone (+) usage of " + varId + " but computed " + bodyQ.[varId].ToString(), rng]
            let pBodyFun = P.Abs(varId, pBindTy, pBodyTerm)
            let resTerm = P.SumCase(
                            pExceptionalCompTerm, 
                            P.Abs("!l", pBindTy, P.App(pBodyFun, P.Var("!l"))),
                            P.Abs("!r", P.Unit, P.In2(pContentsTy, P.Unit, P.PrimUnitVal)))
            return bodyTy, contr exceptionalCompQ (bodyQ.Remove(varId)), resTerm
        }
    | MRet(expr,rng) ->
        check {
            let! exprTy, exprQ, pExprTerm = withError errorMsg rng (typeCheck ctxt expr)
            let! pExprTy = withError errorMsg rng (kCheckProset ctxt.tenv exprTy)
            return Exception(exprTy, noRange), exprQ, P.In1(pExprTy, P.Unit, pExprTerm)
        } 
    | CoeffectAscription(assertions, expr, rng) ->
        let checkAssertion (exprQ : CoeffectMap) (q : Coeffect, x : string) =
            if not (ctxt.venv.ContainsKey(x)) then
                Error ["coeffect ascription provided for undeclared variable " + x, rng]
            else if not (Coeffect.LessThan exprQ.[x] q) then
                Error ["Scalar " + exprQ.[x].ToString() + " computed for variable " + x + ", which is not more precise than the ascribed scalar " + q.ToString(), rng]
            else
                Result ()
        check {
            let! exprTy, exprQ, exprTerm = withError errorMsg rng (typeCheck ctxt expr)
            do! sequence (List.map (checkAssertion exprQ) assertions)
            return exprTy, exprQ, exprTerm  
        }
    | TypeAscription(ty, expr, rng) ->
        check {
            let! exprTy, exprQ, exprTerm = withError errorMsg rng (typeCheck ctxt expr)
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv exprTy ty)
            return ty, exprQ, exprTerm
        }
    | Hole(rng) ->
        foundHole := Some(ctxt, rng)
        Error []

type ProgCheckResult =
    | CheckResult of Check<Ty * CoeffectMap * P.Term * TypeEnvironment>
    | FoundHole of Context * Range

let progCheck (ctxt : Context) (p : Prog) : ProgCheckResult = 
    let foldAlias (acc : Check<TypeEnvironment>) ((n,ty) : string * Ty) =
        match acc with
        | Error(stack) ->
            Error(stack)
        | Result(tenv) ->
            match kSynth tenv ty with
            | Result k ->
                Result { tenv with tyAliasEnv = tenv.tyAliasEnv.Add(n,ty) }
            | Error(stack) ->
                Error(stack)
    foundHole := None
    let tyCheckRes =
        check {
            let tenvCheck = Result ctxt.tenv
            let! tenv = List.fold foldAlias tenvCheck p.typeAliases
            let! ty,R,pTerm = typeCheck { ctxt with tenv = tenv } p.body
            let! _ = P.typeCheck { venv = Map.empty ; tenv = Set.empty } pTerm        
            return ty,R,pTerm,tenv
        }
    match foundHole.Value with
    | Some(ctxt, rng) ->
        FoundHole(ctxt, rng)
    | None ->
        CheckResult(tyCheckRes)