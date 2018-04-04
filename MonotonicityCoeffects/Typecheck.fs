module Typecheck
open Microsoft.FSharp.Text.Lexing
open Ast

/// (tyVarMap, baseTyMap)
/// tyVarMap maps each identifier to a kind it is bound to
/// baseTyMap maps each base type name (they are semilattices) to its delta type
type TypeEnvironment = Map<string, Kind> * Set<string> 

type Range = Position * Position

/// kCheckToset tenv ty = res
/// tenv - the type environment to check under
/// ty   - the type to check
/// res  - None if the type is a toset, 
///        (Some explanation), otherwise, where explanation is a stack of errors
let rec kCheckToset (tenv : TypeEnvironment) (ty : Ty) : Option<List<string * Range>> =
    let errorMsg = "Type " + ty.ToString() + " is not a toset"
    let tyVarEnv, tyBaseEnv = tenv
    match ty with
    | BaseTy(name,rng) ->
        match tyBaseEnv.Contains(name) with
        | true ->
            // all base types are tosets
            None
        | false ->
            
            Some([errorMsg + ": no base type " + name + "defined", rng])
    | FunTy(_,_,_,rng) ->
        Some([errorMsg + ": no function type is considered a toset", rng])
    | Dictionary(dom, cod, rng) ->
        Some([errorMsg + ": no dictionary type is considered a toset", rng])
    | Capsule(ty,q, rng) ->
        Some([errorMsg + ": no capsule type is considered a toset", rng])
    | Prod(tyL, tyR, rng) ->
        match kCheckToset tenv tyL with
        | Some(stack) ->
            Some((errorMsg + ": left component is not a toset type", rng) :: stack)
        | None ->
            match kCheckToset tenv tyR with
            | Some(stack) ->
                Some((errorMsg + ": right component is not a toset type", rng) :: stack)
            | None ->
                None
    | Sum(tyL, tyR, rng) ->
        match kCheckToset tenv tyL with
        | Some(stack) ->
            Some((errorMsg + ": left component is not a toset type", rng) :: stack)
        | None ->
            match kCheckToset tenv tyR with
            | Some(stack) ->
                Some((errorMsg + ": right component is not a toset type", rng) :: stack)
            | None ->
                None
    | IVar(_, rng) ->
        Some([(errorMsg + ": no ivar type is considered a toset", rng)])
    | TyAlias(name, rng) ->
        match tyVarEnv.TryFind name with
        | Some(Toset) ->
            None
        | Some(k) ->
            Some [name + " has kind " + k.ToString() + " rather than TOSET", rng]
        | None ->
            Some ["undeclared type " + name, rng]

/// kCheckSemilattice tenv ty = res 
/// tenv - the type environment to check under
/// ty - the type to check
/// ty0 - If ty is a semilattice type, None
///       Otherwise, Some explanation, where explanation is an error stack
let rec kCheckSemilattice (tenv : TypeEnvironment) (ty : Ty) : Option<List<string*Range>> =
    let tyVarEnv, tyBaseEnv = tenv
    let errorMsg = "Type " + ty.ToString() + " is not a semilattice"
    match ty with
    | BaseTy(name,rng) ->
        // all base types are semilattices
        None
    | FunTy(_,_,_,rng) ->
        Some [errorMsg + ": function types are not considered semilattice types", rng]
    | Dictionary(dom, cod, rng) ->
        match kCheckToset tenv dom with 
        | Some(stack) ->
            Some((errorMsg + ": the domain of a dictionary must be a toset", rng) :: stack)
        | None ->
            match kCheckSemilattice tenv cod with
            | Some(stack) ->
                Some((errorMsg + ": the codomain type of a dictionary must be a semilattice",rng) :: stack)
            | None ->
                None
    | Capsule(ty,q, rng) ->
        Some [errorMsg + ": capsule types are not considered semilattice types", rng]
    | Prod(tyL,tyR, rng) ->
        match kCheckSemilattice tenv tyL with
        | Some(stack) ->
            Some((errorMsg + ": left component is not a semilattice type", rng) :: stack)
        | None ->
            match kCheckSemilattice tenv tyR with
            | Some(stack) ->
                Some((errorMsg + ": right component is not a semilattice type",rng) :: stack)
            | None ->
                None
    | Sum(_,_,rng) ->
        Some [(errorMsg + ": sum types are not semilattice types",rng)]
    | IVar(tyContents, rng) ->
        match kCheckToset tenv tyContents with
        | Some(stack) ->
            Some((errorMsg + ": the content type of an ivar must be a toset type",rng) :: stack)
        | None ->
            None
    | TyAlias(name, rng)->
        match tyVarEnv.TryFind name with
        | None -> 
            Some(["Type variable " + name + " undeclared", rng])
        | Some(Semilattice) ->
            None
        | Some(k) ->
            let explanation = ": type variable " + name + " bound to " + k.ToString() + ", but semilattice expected" 
            Some([errorMsg + explanation, rng])    
    | ForallTy(_,_,_,rng) ->
        Some [errorMsg + ": forall types are not semilattice types", rng]
 