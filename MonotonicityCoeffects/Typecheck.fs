module Typecheck

open PCF
open Ast
open Kindcheck
open System
open CheckComputation
open System.Security.Cryptography
open System.Reflection.Metadata

module P = PCF

type ValueEnvironment = Map<string, Ty>
type PrimValueEnvironment = Map<string, Ty * P.Term>
type Context = { tenv : TypeEnvironment ; venv : ValueEnvironment ; bvenv : PrimValueEnvironment }

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
    
let rec typeCheck (ctxt : Context) (expr : Expr) : Check<Ty * CoeffectMap * P.Term> =
    let tenv,venv = ctxt.tenv, ctxt.venv
    let tyVarEnv, tyBaseEnv = tenv.tyVarEnv, tenv.tyBaseEnv
    let errorMsg = "Expression " + expr.ToString() + " not well-typed"
    match expr with
    | Int(n, rng) ->
        if n >= 0 then
            Result (TyId("Nat", noRange), Map.map (fun k v -> Coeffect.Ign) venv, P.PrimNatVal(n))
        else
            Error ["Negative integer constants not allowed", rng]
    | Bool(b,rng) ->
        Result (TyId("Bool", noRange), Map.map (fun k v -> Coeffect.Ign) venv, P.PrimBoolVal(b))
    | Forall(tyVarId, pk, body, rng) ->
        check {
            let tyVarEnv' = Map.add tyVarId pk tyVarEnv
            let tenv' = { tenv with tyVarEnv = tyVarEnv' }
            let! ty, qs, term = withError (errorMsg + ": body is not well-typed") rng (typeCheck { ctxt with tenv = tenv' } body)
            let term' = 
                let pTyVar = P.TyVar("$" + tyVarId)
                match pk with
                | Poset ->
                    P.Forall("$" + tyVarId, term)
                | Toset ->
                    P.Forall("$" + tyVarId, P.Abs("$" + tyVarId + "_comp", P.Fun(pTyVar, P.Fun(pTyVar, P.BB)), term))
                | Semilattice ->
                     P.Forall("$" + tyVarId,
                        P.Abs("$" + tyVarId + "_bot", pTyVar, 
                            P.Abs("$" + tyVarId + "_join", P.Fun(pTyVar, P.Fun(pTyVar, pTyVar)), term)))
            
            // TODO: this should be a forall type rather than a tyOp
            return (ForallTy(tyVarId, pk, ty, noRange), qs, term')
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
                let! pTy, pBot, pJoin = withError errorMsg rng (kCheckSemilattice ctxt.tenv tyArg)
                let term' = P.TyApp(termForall, pTy)
                let term'' = P.App(term', pBot)
                let term''' = P.App(term'', pJoin)
                return (ty', qsForall, term''')
        }
    | Abs(var, varTy, body, rng) ->
        check {
            let! kVar = withError ("type annotation " + varTy.ToString() + " is not well-kinded") rng (kSynth ctxt.tenv varTy)
            let! pTyVar,_,_ = getProper "argument type" kVar 
            let venv' = Map.add var varTy venv
            let! ty,qs,term = withError (errorMsg + ": body not well-typed") rng (typeCheck { ctxt with venv = venv' } body)
            match qs.TryFind(var) with // None case unreachable
            | Some(q) ->
                let ty' = FunTy(varTy, q, ty, noRange)
                let qs' = qs.Remove(var)
                let term' = P.Abs(var, pTyVar, term)
                return ty', qs', term'
        }
    | App(fn,arg,rng) ->
        check {
            let! tyFun, qsFun, termFun = withError (errorMsg + ": function position ill-typed") rng (typeCheck ctxt fn)
            let! tyArg, qsArg, termArg = withError (errorMsg + ": argument position ill-typed") rng (typeCheck ctxt arg)
            let! codTy, qs, term =
                match tyFun with
                | FunTy(domTy, q, codTy, rng) ->
                    check {
                        do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv tyArg domTy)
                        let qs = contr qsFun (comp q qsArg)
                        let term = P.App(termFun, termArg)
                        return (codTy, qs, term)
                    }
                | _ ->
                    Error [errorMsg + ": " + fn.ToString() + " has type " + tyFun.ToString() + " and cannot be applied ",rng]
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
            let! _, pBot, _ = withError errorMsg rng (kCheckSemilattice tenv ty)
            let qsAllIgn = Map.map (fun k v -> Coeffect.Ign) venv
            return ty, qsAllIgn, pBot
        }
    | Join(ty, e1, e2, rng) ->
        check {
            let! _, _, pJoin = withError errorMsg rng (kCheckSemilattice tenv ty)
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
            return TyId("Bool", noRange), contr (comp CoeffectAntitone Q1) Q2, term
        }
    | Extract(targetTy, key, value, acc, dict, body, rng) ->
        check {
            let! pTargetTy, pTargetBot, pTargetJoin = 
                withError errorMsg rng (kCheckSemilattice tenv targetTy)
            let! dictTy, dictQ, pDictTerm = 
                withError errorMsg rng (typeCheck ctxt dict)
            let! keyTy, valTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, dictTy) with
                | Dictionary(domTy, codTy, _) ->
                    Result (domTy, codTy)
                | _ ->
                    let errorMsg' = ": dictionary expected for type of " + dict.ToString() + ", but " + dictTy.ToString() + " computed" 
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
                    Error ["Expected monotone usage of " + acc + " but found " + bodyQ.[value].ToString(), rng]            
            let resQ = contr dictQ (bodyQ.Remove(acc).Remove(key).Remove(value))
            // pDictTerm, pBodyTerm, pKeyComp, pKeyTy, pValTy, pTargetTy
            let pBodyFun = P.Abs(key, pKeyTy, P.Abs(value, pValTy, P.Abs(acc, pTargetTy, pBodyTerm)))
            let pElemTy = P.Prod(pKeyTy, pValTy)
            let pDictTy = P.List pElemTy
            let pIncTerm = P.App(P.App(P.App(pBodyFun, P.Proj1(P.Var("!h"))), P.Proj2(P.Var("!h"))), P.Var("!acc"))
            let pElim = 
                P.LetRec("!f", "!d", pDictTy, pTargetTy, P.Abs("!acc", pTargetTy,
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
                    let errorMsg' = ": type of " + e3.ToString() + " expected to be dictionary type, but computed " + dictTy.ToString()
                    Error [errorMsg + errorMsg',rng]
            do! withError 
                    (errorMsg + ": key type " + keyTy.ToString() + " is not a subtype of dictionary domain type " + dKeyTy.ToString()) 
                    rng 
                    (Ty.IsSubtype ctxt.tenv.tyAliasEnv keyTy dKeyTy)
            do! withError 
                    (errorMsg + ": value " + e2.ToString() + " is not a subtype of dictionary codomain " + dValTy.ToString())
                    rng
                    (Ty.IsSubtype ctxt.tenv.tyAliasEnv valTy dValTy)
            let resQ = contr (contr (comp CoeffectAny keyQ) valQ) dictQ
            let pResTerm = P.Cons(P.Pair(pKeyTerm, pValTerm), pDictTerm)
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
    | Pair(eFst, eSnd, rng) ->
        check {
            let! fstTy, fstQ, pFstTerm = withError errorMsg rng (typeCheck ctxt eFst)
            let! sndTy, sndQ, pSndTerm = withError errorMsg rng (typeCheck ctxt eSnd)
            return Prod(fstTy, sndTy, noRange), contr fstQ sndQ, P.Pair(pFstTerm, pSndTerm)
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
            let venvL = venv.Add(lName, lTy)
            let ctxtL = { ctxt with venv = venvL }
            let! lTy, lQ, plTerm = withError errorMsg rng (typeCheck ctxtL lElim)
            let! pTyL = kCheckProset ctxt.tenv lTy
            let venvR = venv.Add(rName, rTy)
            let ctxtR = { ctxt with venv = venvR }
            let! rTy, rQ, prTerm = withError errorMsg rng (typeCheck ctxtR rElim)
            let! pTyR = kCheckProset ctxt.tenv rTy
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv lTy targetTy)
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv rTy targetTy)
            return targetTy, contr (contr scrutQ lQ) rQ, P.SumCase(pScrutTerm, P.Abs(lName, pTyL, plTerm), P.Abs(rName, pTyR, prTerm)) 
        }
    | Inl(lty, rty, expr, rng) ->
        check {
            let! exprTy, exprQ, pExprTerm = withError errorMsg rng (typeCheck ctxt expr)
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv exprTy lty)
            return Sum(lty,rty,noRange), exprQ, P.In1(pExprTerm)
        }
    | Inr(lty, rty, expr, rng) ->
        check {
            let! exprTy, exprQ, pExprTerm = withError errorMsg rng (typeCheck ctxt expr)
            do! withError errorMsg rng (Ty.IsSubtype ctxt.tenv.tyAliasEnv exprTy rty)
            return Sum(lty,rty,noRange), exprQ, P.In2(pExprTerm)
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
                (errorMsg + ": computed type " + contentsTy.ToString() + " for " + expr.ToString())
            let! _, _ = withError tosetErrorMsg rng (kCheckToset ctxt.tenv contentsTy)
            return IVar(contentsTy, noRange), comp CoeffectAny contentsQ, P.Cons(pContentsTerm, P.EmptyList)
        }
    | IGet(varId, ivar, body, rng) ->
        check {
            let! ivarTy, ivarQ, pIvarTerm = withError errorMsg rng (typeCheck ctxt ivar)
            let! tyContents =
                match Ty.normalize(ctxt.tenv.tyAliasEnv, ivarTy) with
                | IVar(tyContents,_) ->
                    Result tyContents
                | _ ->
                    Error [errorMsg + ": " + expr.ToString() + " expected to have ivar type, but type " + ivarTy.ToString() + " was computed.", rng]
            let! pTyContents = kCheckProset ctxt.tenv tyContents
            let venv' = venv.Add(varId, tyContents)
            let! bodyTy, bodyQ, pBodyTerm = withError errorMsg rng (typeCheck { ctxt with venv = venv' } body)
            let! pBodyTy, pBodyBot, pBodyJoin = kCheckSemilattice ctxt.tenv bodyTy
            let pIvarTy = P.List pTyContents
            let resTerm = 
                P.ListCase(
                    pIvarTerm, 
                    pBodyBot,
                    P.Abs("!hi", pTyContents, P.Abs("!ti", pIvarTy, 
                        P.ListCase(
                            P.Var("!ti"),
                            P.In1(P.App(P.Abs(varId, pTyContents, pBodyTerm), P.Var("!hi"))),
                            P.Abs("_", pTyContents, P.Abs("_", pIvarTy, P.In2(P.PrimUnitVal)))))))
            return Partial(bodyTy, noRange), contr ivarQ (bodyQ.Remove(varId)), resTerm
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
    | MLet(varId, partialComputationExpr, bodyExpr, rng) ->
        check {
            let! partialCompTy, partialCompQ, pPartialCompTerm =
                withError errorMsg rng (typeCheck ctxt partialComputationExpr)
            let! bindTy = 
                match Ty.normalize(ctxt.tenv.tyAliasEnv, partialCompTy) with
                | Partial(bindTy,_) ->
                    Result bindTy
                | _ ->
                    Error [errorMsg + ": monadic let expected a partial computation in body position, but instead got " + partialCompTy.ToString(),rng]
            let! pBindTy = kCheckProset ctxt.tenv bindTy
            let venv' = venv.Add(varId, bindTy)
            let! bodyTy, bodyQ, pBodyTerm = withError errorMsg rng (typeCheck { ctxt with venv = venv' } bodyExpr)
            do!
                match Coeffect.LessThan bodyQ.[varId] CoeffectMonotone with
                | true ->
                    Result ()
                | false ->
                    Error ["Expected monotone (+) usage of " + varId + " but computed " + bodyQ.[varId].ToString(), rng]
            let pBodyFun = P.Abs(varId, pBindTy, pBodyTerm)
            let resTerm = P.SumCase(
                            pPartialCompTerm, 
                            P.Abs("!l", pBindTy, P.In1(P.App(pBodyFun, P.Var("!r")))),
                            P.Abs("!r", P.Unit, P.In2(P.PrimUnitVal)))
            return Partial(bodyTy, noRange), contr partialCompQ (bodyQ.Remove(varId)), resTerm
        }
    | MRet(expr,rng) ->
        check {
            let! exprTy, exprQ, pExprTerm = withError errorMsg rng (typeCheck ctxt expr)
            return Partial(exprTy, noRange), exprQ, P.In1(pExprTerm)
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
            return exprTy, exprQ, exprTerm
        }
    
  
// type TypeEnvironment = { tyVarEnv : Map<string, Kind> ; tyBaseEnv : Map<string, Kind> }
// type ValueEnvironment = Map<string, Ty>
// type Context = { tenv : TypeEnvironment ; venv : ValueEnvironment }

let progCheck (ctxt : Context) (p : Prog) : Check<Ty * CoeffectMap * P.Term> = 
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

    check {
        let tenvCheck = Result ctxt.tenv
        let! tenv = List.fold foldAlias tenvCheck p.typeAliases
        let! ty,R,pTerm = typeCheck { ctxt with tenv = tenv } p.body
        return ty,R,pTerm
    }