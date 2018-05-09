module Typecheck

open Ast
open Kindcheck
open System
open CheckComputation

type ValueEnvironment = Map<string, Ty>
type Context = { tenv : TypeEnvironment ; venv : ValueEnvironment }

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
    
let rec typeCheck (ctxt : Context) (expr : Expr) =
    let tenv,venv = ctxt.tenv, ctxt.venv
    let tyVarEnv, tyBaseEnv = tenv.tyVarEnv, tenv.tyBaseEnv
    let errorMsg = "Expression " + expr.ToString() + " not well-typed"
    match expr with
    | Int(n, rng) ->
        if n >= 0 then
            Success (BaseTy("Nat", noRange), Map.map (fun k v -> Coeffect.Ign) venv)
        else
            Failure(["Negative integer constants not allowed", rng])
    | Forall(tyVarId, kind, body, rng) ->
        let tyVarEnv' = Map.add tyVarId (KProper(Set [kind], noRange)) tyVarEnv
        let tenv' = { tenv with tyVarEnv = tyVarEnv' }
        match typeCheck { ctxt with tenv = tenv' } body with
        | Success(ty, coeffect) ->
            Success(ForallTy(tyVarId, kind, ty, noRange), coeffect)
        | Failure(stack) ->
            Failure((errorMsg + ": body not well-typed", rng) :: stack)
    | ForallApp(forallExpr, tyArg, rng) ->
        match typeCheck ctxt forallExpr with
        | Success(ForallTy(id,kind,tyBody,_), R) ->
            let kCheckResult =
                match kind with
                | Toset ->
                    kCheckToset ctxt.tenv tyArg
                | Semilattice ->
                    kCheckSemilattice ctxt.tenv tyArg
                | Proset ->
                    kCheckProset ctxt.tenv tyArg
            match kCheckResult with
            | Some(stack) ->
                Failure((errorMsg + ": " + tyArg.ToString() + " does not have expected kind " + kind.ToString(),rng) :: stack)
            | None ->
                Success(Ty.subst tyBody id tyArg, R)
        | Success(tyForall, _) ->
            Failure [errorMsg + ": " + tyForall.ToString() + " is not a type abstraction", rng]
        | Failure(stack) ->
            Failure((errorMsg + ": body not well-typed", rng) :: stack)
    | Abs(var, varTy, body, rng) ->
        let venv' = Map.add var varTy venv
        match typeCheck { ctxt with venv = venv' } body with
        | Success(tyBody, coeffect) ->
            match coeffect.TryFind var with
            | Some(q) ->
                Success(FunTy(varTy, q, tyBody, noRange), coeffect.Remove var)
            | None ->
                failwith "unreachable"
        | Failure(stack) ->
            Failure( (errorMsg + ": body not well-typed", rng) :: stack )
    | App(fn,arg,rng) ->
        match typeCheck ctxt fn with
        | Success(FunTy(domTy,q,codTy,rng), R) ->
            match typeCheck ctxt arg with
            | Success(argTy, S) -> //todo: we need to make a subtyping relation and overload Ty's = in terms of it
                match Ty.IsSubtype argTy domTy with
                | SubtypeResult.Success ->
                    Success(codTy,contr R (comp q S))
                | SubtypeResult.Failure(stack) ->
                    Failure((errorMsg,rng) :: (List.map (fun msg -> (msg,noRange)) stack))
            | Failure(stack) ->
                Failure( (errorMsg + ": argument ill-typed", rng) :: stack)
        | Success(ty, R) ->
            Failure [errorMsg + ": " + fn.ToString() + " has type " + ty.ToString() + " and cannot be applied ",rng]
        | Failure(stack) ->
            Failure( (errorMsg + ": function ill-typed", rng) :: stack )
    // | Const(name,rng) -> there is no reason to have constants - we are just going to add entries to the base venv instead
    | Var(name,rng) ->
        match venv.TryFind name with
        | Some(ty) ->
            Success(ty, Map.map (fun k v -> if k = name then Coeffect.Use else Coeffect.Ign) venv)
        | None ->
            Failure [errorMsg + ": identifier " + name.ToString() + "undeclared",rng]
    | Bot(ty,rng) ->
        match kCheckSemilattice tenv ty with
        | None ->
            Success(ty, Map.map (fun k v -> Coeffect.Ign) venv)
        | Some(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Join(ty, e1, e2, rng) ->
        match kCheckSemilattice tenv ty with
        | None ->
            match typeCheck ctxt e1 with
            | Success(ty1, R1) ->
                match typeCheck ctxt e2 with
                | Success(ty1, R2) ->
                    Success(ty,contr R1 R2)
                | Failure(stack) ->
                    Failure((errorMsg,rng) :: stack)
            | Failure(stack) ->
                Failure((errorMsg,rng) :: stack)
        | Some(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Extract(targetTy, key, value, acc, dict, body, rng) ->
        match kCheckSemilattice tenv targetTy with
        | Some(stack) ->
            Failure((errorMsg,rng) :: stack)
        | None ->
            match typeCheck ctxt dict with
            | Success( Dictionary(domTy,codTy,_), dictR) ->
                let venv' = venv.Add(key, Capsule(domTy, CoeffectAny,noRange))
                let venv'' = venv'.Add(value, codTy)
                let venv''' = venv''.Add(acc, targetTy)
                match typeCheck { ctxt with venv = venv''' } body with
                | Success(bodyTy, bodyR) ->
                    match Ty.IsSubtype bodyTy targetTy with
                    | SubtypeResult.Success ->
                        Success(targetTy, contr (bodyR.Remove(key).Remove(value).Remove(acc)) dictR)
                    | SubtypeResult.Failure(stack) ->
                        Failure((errorMsg + ": body type " + bodyTy.ToString() + " is not a subtype of target type " + targetTy.ToString(),rng) :: List.map (fun k -> k,noRange) stack)
                | Failure(stack) ->
                    Failure(stack)
            | Success(wrongTy, _) ->
                Failure [errorMsg + ": type " + wrongTy.ToString() + " computed, but dictionary type expected",rng]
            | Failure(stack) ->
                Failure((errorMsg,rng) :: stack)
    | Cons(e1, e2, e3, rng) ->
        match typeCheck ctxt e3 with
        | Success( Dictionary(domTy,codTy,_), dictR ) ->
            match typeCheck ctxt e2 with
            | Success(valTy, valR) ->
                match Ty.IsSubtype valTy codTy with
                | SubtypeResult.Success ->
                    match typeCheck ctxt e1 with
                    | Success(keyTy, keyR) ->
                        match Ty.IsSubtype keyTy domTy with
                        | SubtypeResult.Success ->
                            let ty = Dictionary(domTy,codTy,noRange)
                            let R = contr (contr (comp CoeffectAny keyR) valR) dictR
                            Success(ty,R)
                        | SubtypeResult.Failure(stack) ->
                            let stack' = List.map (fun msg -> (msg,noRange)) stack
                            Failure((errorMsg + ": key type " + keyTy.ToString() + " is not a subtype of dictionary domain type " + domTy.ToString(), rng) :: stack')
                    | Failure(stack) ->
                        Failure((errorMsg,rng) :: stack)
                | SubtypeResult.Failure(stack) ->
                   Failure((errorMsg + ": value " + e2.ToString() + " is not a subtype of dictionary codomain " + codTy.ToString(), rng) :: List.map (fun k -> k,noRange) stack)
            | Failure(stack) ->
                Failure((errorMsg,rng) :: stack)
        | Success(wrongTy, _) ->
            Failure [errorMsg + ": dictionary type expected, but got " + wrongTy.ToString(),rng]
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Fst(ePair,rng) ->
        match typeCheck ctxt ePair with
        | Success(Prod(tyL,_,_), R) ->
            Success(tyL, R)
        | Success(wrongTy, _) ->
            Failure [errorMsg + ": expected product type, but got " + wrongTy.ToString(),rng]
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Snd(ePair,rng) ->
        match typeCheck ctxt ePair with
        | Success(Prod(_,tyR,_), R) ->
            Success(tyR, R)
        | Success(wrongTy, _) ->
            Failure [errorMsg + ": expected product type, but got " + wrongTy.ToString(),rng]
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Pair(eFst, eSnd, rng) ->
        match typeCheck ctxt eFst with
        | Success(fstTy, fstR) ->
            match typeCheck ctxt eSnd with
            | Success(sndTy, sndR) ->
                Success( Prod(fstTy, sndTy, noRange), contr fstR sndR )
            | Failure(stack) ->
                Failure((errorMsg,rng) :: stack)
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Case(eScrut, targetTy, lName, lElim, rName, rElim,rng) ->
        match typeCheck ctxt eScrut with
        | Success(Sum(lTy,rTy,_), R) ->
            let venvL = venv.Add(lName,lTy)
            let ctxtL = { ctxt with venv = venvL }
            match typeCheck ctxtL lElim with
            | Success(lElimTy, S) ->
                match Ty.IsSubtype lElimTy targetTy with
                | SubtypeResult.Success ->
                    let venvR = venv.Add(rName,rTy)
                    let ctxtR = { ctxt with venv = venvR }
                    match typeCheck ctxtR rElim with
                    | Success(rElimTy, T) ->
                        match Ty.IsSubtype rElimTy targetTy with
                        | SubtypeResult.Success ->
                            Success(targetTy, contr R (contr S T))
                        | SubtypeResult.Failure(stack) ->
                            Failure((errorMsg,rng) :: List.map (fun str -> (str,noRange)) stack)
                    | Failure(stack) ->
                        Failure( (errorMsg,rng) :: stack )
                | SubtypeResult.Failure(stack) ->
                    Failure((errorMsg,rng) :: List.map (fun str -> (str,noRange)) stack)
            | Failure(stack) ->
                Failure((errorMsg, rng) :: stack)
        | Success(scrTy,_) ->
            Failure [errorMsg + ": case scrutinee should have sum type, but instead found" + scrTy.ToString(), rng]
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Inl(lty, rty, expr, rng) ->
        match typeCheck ctxt expr with
        | Success(exprTy,R) ->
            match Ty.IsSubtype exprTy lty with
            | SubtypeResult.Success ->
                Success(Sum(lty,rty,noRange),R)        
            | SubtypeResult.Failure(stack) ->
                Failure((errorMsg,rng) :: List.map (fun str -> (str,noRange)) stack)
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Inr(lty, rty, expr, rng) ->
        match typeCheck ctxt expr with
        | Success(exprTy,R) ->
            match Ty.IsSubtype exprTy rty with
            | SubtypeResult.Success ->
                Success(Sum(lty,rty,noRange),R)        
            | SubtypeResult.Failure(stack) ->
                Failure((errorMsg,rng) :: List.map (fun str -> (str,noRange)) stack)
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Cap(q, e, rng) ->
        match typeCheck ctxt e with
        | Success(eTy, R) ->
            Success(Capsule(eTy,q,rng), comp q R)
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | Uncap(q, varId, capsule, body, rng) ->
        match typeCheck ctxt capsule with
        | Success(Capsule(contentsTy,s,_), R) when s = q ->
            let venv' = venv.Add(varId, contentsTy)
            match typeCheck { ctxt with venv = venv' } body with
            | Success(bodyTy, S) ->
                match S.TryFind(varId) with
                | Some(r) when Coeffect.LessThan r q -> 
                    Success(bodyTy, contr R (S.Remove(varId)))
                | Some(r) ->
                    Failure [(errorMsg + ": " + varId + " has coeffect " + r.ToString() + " but coeffect more restrictive 
                              than " + q.ToString() + " expected", rng)]
                | None ->
                    failwith "unreachable"
            | Failure(stack) ->
                Failure( (errorMsg,rng) :: stack )
        | Success(Capsule(contentsTy, s,_),R) ->
            Failure[errorMsg + ": expected a capsule " + q.ToString() + " expression in the binding position, but got an capsule " + s.ToString(), rng]
        | Success(bindTy,_) ->
            Failure [errorMsg + ": expected an expression of capsule type in the binding position, but got an expression of type " + bindTy.ToString(), rng]
        | Failure(stack) ->
            Failure( (errorMsg,rng) :: stack )
    | ISet(expr, rng) ->
        match typeCheck ctxt expr with
        | Success(contentsTy,R) ->
            match kCheckToset (ctxt.tenv) contentsTy with
            | None ->
                Success(IVar(contentsTy, noRange), comp CoeffectAny R)
            | Some(stack) ->
                Failure((errorMsg + ": computed type " + contentsTy.ToString() + " for " + expr.ToString(),rng) :: stack)
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | IGet(varId, ivar, body, rng) ->
        match typeCheck ctxt ivar with
        | Success(IVar(tyContents,_), R) ->
            let venv' = venv.Add(varId,tyContents)
            match typeCheck { ctxt with venv = venv' } body with
            | Success(tyBody,S) ->
                Success(Partial(tyBody,noRange), contr R S)
            | Failure(stack) ->
                Failure( (errorMsg, rng) :: stack )
        | Success(bindTy,_) ->
            Failure [errorMsg + ": " + expr.ToString() + " expected to have ivar type, but type " + bindTy.ToString() + " was computed.", rng]
        | Failure(stack) ->
            Failure( (errorMsg,rng) :: stack )
    | Let(varId, bindExpr, bodyExpr, rng) ->
        match typeCheck ctxt bindExpr with
        | Success(tyBind, R) ->
            let venv' = venv.Add(varId,tyBind)
            match typeCheck { ctxt with venv = venv' } bindExpr with
            | Success(tyBody, S) ->
                Success(tyBody, contr (comp S.[varId] R) (S.Remove(varId)))
            | Failure(stack) ->
                Failure((errorMsg,rng) :: stack)
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | MLet(varId, partialComputationExpr, bodyExpr, rng) ->
        match typeCheck ctxt partialComputationExpr with
        | Success(Partial(tyBind,_),R) ->
            let venv' = venv.Add(varId,tyBind)
            match typeCheck { ctxt with venv = venv' } bodyExpr with
            | Success(Partial(tyBody,_),S) ->
                Success(Partial(tyBody,noRange), contr (comp S.[varId] R) (S.Remove(varId)))
            | Success(tyBody,_) ->
                Failure [errorMsg + ": monadic let expected a partial computation in body position, but instead got " + tyBody.ToString(),rng]
            | Failure(stack) ->
                Failure((errorMsg,rng) :: stack)
        | Success(tyRes,_) ->
            Failure [errorMsg + ": monadic let expected a partial computation in binding position, but instead got " + tyRes.ToString(),rng]
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
    | MRet(expr,rng) ->
        match typeCheck ctxt expr with
        | Success(tyExpr,R) ->
            Success(Partial(tyExpr,noRange), R)
        | Failure(stack) ->
            Failure((errorMsg,rng) :: stack)
 
// type TypeEnvironment = { tyVarEnv : Map<string, Kind> ; tyBaseEnv : Map<string, Kind> }
// type ValueEnvironment = Map<string, Ty>
// type Context = { tenv : TypeEnvironment ; venv : ValueEnvironment }

let progCheck (ctxt : Context) (p : Prog) = 
    let foldAlias (acc : Check<TypeEnvironment>) (n : string) (ty : Ty) =
        match acc with
        | Error(stack) ->
            Error(stack)
        | Result(tenv) ->
            match kSynth tenv ty with
            | KindSynthResult.Success(k) ->
                Result { tenv with tyVarEnv = tenv.tyVarEnv.Add(n,k) }
            | KindSynthResult.Failure(stack) ->
                Error(stack)

    let tenvCheck = check { return ctxt.tenv }
    let tenvComp = Map.fold foldAlias tenvCheck p.typeAliases
    match tenvComp with
    | Error(stack) ->
        Error(stack)
    | Result(tenv) ->
        match typeCheck { ctxt with tenv = tenv } p.body with
        | Success(ty,R) ->
            Result(ty,R)
        | Failure(stack) ->
            Error(stack)
