module Typecheck

open Ast
open Kindcheck

type ValueEnvironment = Map<string, Ty>
type Context = { tenv : TypeEnvironment ; venv : ValueEnvironment }

type typeCheckResult =
    | Success of Ty
    | Failure of List<string*Range>

let rec typeCheck (ctxt : Context) (expr : Expr) =
    let tenv,venv = ctxt.tenv, ctxt.venv
    let errorMsg = "Expression " + expr.ToString() + " not well-typed"
    match expr with
    | Int(n, rng) ->
        if n >= 0 then
            Success (BaseTy("Nat", noRange))
        else
            Failure(["Negative integer constants not allowed", rng])
    | Forall(tyVarId, kind, body, rng) ->
        match typeCheck { ctxt with tenv = Map.add tyVarId kind tenv } expr with
        | _ ->
            ()