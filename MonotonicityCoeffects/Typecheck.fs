module Typecheck

open Ast
open Kindcheck
open System

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
    | Abs(var, varTy, q, body, rng) ->
        let venv' = Map.add var varTy venv
        match typeCheck { ctxt with venv = venv' } body with
        | Success(tyBody, coeffect) ->
            match coeffect.TryFind var with
            | Some(q') when Coeffect.LessThan q q' ->
                Success(FunTy(varTy, q, tyBody, noRange), coeffect.Remove var)
            | Some(q') ->
                Failure [errorMsg + "required scalar " + q.ToString() + " not less than " + q'.ToString(), rng]
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
                        Success(targetTy, contr bodyR dictR)
                    | SubtypeResult.Failure(stack) ->
                        Failure((errorMsg + ": body type " + bodyTy.ToString() + " is not a subtype of target type " + targetTy.ToString(),rng) :: stack)
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
                   Failure((errorMsg + ": value " + e2.ToString() + " is not a subtype of dictionary codomain " + codTy.ToString(), rng) :: stack)
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
            match typeCheck ctxt

