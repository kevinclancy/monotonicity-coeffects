module Kindcheck

open Microsoft.FSharp.Text.Lexing
open Ast

/// tyVarEnv maps each identifier to a kind it is bound to
/// tyBaseEnv maps each base type name (they are semilattices) to its kind
type TypeEnvironment = { tyVarEnv : Map<string, Kind> ; tyBaseEnv : Map<string, Kind> }

type Range = Position * Position

 type KindSynthResult =
    | Success of result : Kind
    | Failure of stack : List<string*Range>

/// kCheckToset tenv ty = res
/// tenv - the type environment to check under
/// ty   - the type to check
/// res  - None if the type is a toset, 
///        (Some explanation), otherwise, where explanation is a stack of errors
let rec kCheckToset (tenv : TypeEnvironment) (ty : Ty) : Option<List<string * Range>> =
    let errorMsg = "Type " + ty.ToString() + " is not a toset"
    let tyVarEnv, tyBaseEnv = tenv.tyVarEnv, tenv.tyBaseEnv
    match ty with
    | BaseTy(name,rng) ->
        match tyBaseEnv.TryFind(name) with
        | Some( KProper(kindRef,_) ) when kindRef.Contains( Toset ) ->
            // all base types are tosets
            None
        | Some ( KProper(_,_) ) ->
            Some [errorMsg, rng]
        | Some ( KOperator(_,_,rng) ) ->
            Some [errorMsg + ": has an operator kind, whereas tosets must have proper kind", rng]
        | None ->
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
        | Some(KProper(kindRefs,_)) when kindRefs.Contains(Toset) ->
            None
        | Some(k) ->
            Some [(name + " has kind " + k.ToString() + " rather than TOSET", rng)]
        | None ->
            Some [("undeclared type " + name, rng)]
    | ForallTy(varId, kind, body, rng) ->
        Some [(errorMsg + ": type abstractions do not denote totally ordered sets", rng)]

/// kCheckSemilattice tenv ty = res 
/// tenv - the type environment to check under
/// ty - the type to check
/// ty0 - If ty is a semilattice type, None
///       Otherwise, Some explanation, where explanation is an error stack
let rec kCheckSemilattice (tenv : TypeEnvironment) (ty : Ty) : Option<List<string*Range>> =
    let tyVarEnv, tyBaseEnv = tenv.tyVarEnv, tenv.tyBaseEnv
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
        | Some( KProper(properKindRef,_) ) when properKindRef.Contains(Semilattice) ->
            None
        | Some(k) ->
            let explanation = ": type variable " + name + " bound to " + k.ToString() + ", but semilattice expected" 
            Some([errorMsg + explanation, rng])    
    | ForallTy(_,_,_,rng) ->
        Some([(errorMsg + ": type abstractions do not denote semilattices", rng)])

let rec kCheckProset (tenv : TypeEnvironment) (ty : Ty) : Option<List<string*Range>> =
    let tyVarEnv, tyBaseEnv = tenv.tyVarEnv, tenv.tyBaseEnv
    let errorMsg = "Type " + ty.ToString() + " is not a proset"
    match ty with
    | BaseTy(name,rng) ->
        match tyBaseEnv.TryFind(name) with
        | Some( KProper(kProperRefs,_) ) when kProperRefs.Contains(Proset) ->
            None
        | Some( k ) ->
            Some [errorMsg + ": instead has kind " + k.ToString(), rng]
        | None ->
            Some [errorMsg + ": base type '" + name + "' unknown", rng]
    | FunTy(dom,q,cod,rng) ->
        match kCheckProset tenv dom with
        | Some(stack) ->
            Some((errorMsg + ": domain is not a proset", rng) :: stack)
        | None ->
            match kCheckProset tenv cod with
            | None ->
                None
            | Some(stack) ->
                Some((errorMsg + ": codomain is not a proset", rng) :: stack)
    | Dictionary(dom, cod, rng) ->
        match kCheckToset tenv dom with
        | Some(stack) ->
            Some((errorMsg + ": domain is not a toset", rng) :: stack)
        | None ->
            match kCheckSemilattice tenv cod with
            | None ->
                None
            | Some(stack) ->
                Some((errorMsg + ": codomain is not a semilattice", rng) :: stack)        
    | Capsule(tyContents, q, rng) ->
        //TODO: generate error if q has no left-adjoint
        match kCheckProset tenv tyContents with
        | Some(stack) ->
            Some((errorMsg, rng) :: stack)
        | None ->
            None
    | Prod(tyL, tyR, rng) ->
        match kCheckProset tenv tyL with
        | Some(stack) ->
            Some( (errorMsg + ": left component is not a proset", rng) :: stack )
        | None ->
            match kCheckProset tenv tyR with
            | Some(stack) ->
                Some( (errorMsg + ": right component is not a proset", rng) :: stack )
            | None ->
                None
    | Sum(tyL, tyR, rng) ->
        match kCheckProset tenv tyL with
        | Some(stack) ->
            Some( (errorMsg + ": left component is not a proset", rng) :: stack )
        | None ->
            match kCheckProset tenv tyR with
            | Some(stack) ->
                Some( (errorMsg + ": right component is not a proset", rng) :: stack )
            | None ->
                None
    | IVar(tyContents, rng) ->
        // really we'd like to have some notion of eqtypes for this
        // or, at least, a notion of certain types having *computable* information orderings
        match kCheckToset tenv tyContents with
        | Some(stack) ->
            Some((errorMsg,rng) :: stack)
        | None ->
            None
    | TyAlias(name, rng) ->
        match tyVarEnv.TryFind name with
        | Some(_) ->
            None
        | None ->
            Some [errorMsg + " type " + name + " not declared", rng]
    | ForallTy(varId, kind, body, rng) ->
        Some([(errorMsg + ": type abstractions do not denote prosets",rng)])

let rec kSynth (tenv : TypeEnvironment) (ty : Ty) : KindSynthResult =
    let tyVarEnv, tyBaseEnv = tenv.tyVarEnv, tenv.tyBaseEnv
    let errorMsg = "Type " + ty.ToString() + " is not well-formed"
    match ty with
    | BaseTy(name,rng) ->
        match tyBaseEnv.TryFind(name) with
        | Some(kind) ->
            Success kind
        | None ->
            Failure [errorMsg + ": base type '" + name + "' unknown", rng]
    | FunTy(dom,q,cod,rng) ->
        match kSynth tenv dom with
        | Failure(stack) ->
            Failure ((errorMsg + ": domain is not a well-kinded", rng) :: stack)
        | Success(kDom) ->
            match kSynth tenv cod with
            | Success(kCod) ->
                Success(KProper(Set [Proset], noRange))
            | Failure(stack) ->
                Failure((errorMsg + ": codomain is not well-kinded", rng) :: stack)
     | Dictionary(dom, cod, rng) ->
        match kCheckToset tenv dom with
        | Some(stack) ->
            Failure((errorMsg + ": domain is not a toset", rng) :: stack)
        | None ->
            match kCheckSemilattice tenv cod with
            | None ->
                Success(KProper(Set [Semilattice],noRange))
            | Some(stack) ->
                Failure((errorMsg + ": codomain is not a semilattice", rng) :: stack)        
    | Capsule(tyContents, q, rng) ->
        //TODO: generate error if q has no left-adjoint
        match kCheckProset tenv tyContents with
        | Some(stack) ->
            Failure((errorMsg + ": capsule content not a proset",rng) :: stack)
        | None ->
            //TODO: if tyContents is a toset, shouldn't that propagate? Maybe we should just use kSynth here
            Success(KProper(Set [Proset], noRange))
    | Prod(tyL, tyR, rng) ->
        match kSynth tenv tyL with
        | Failure(stack) ->
            Failure( (errorMsg + ": left component is not well-formed", rng) :: stack )
        | Success( KProper(kRefsL,_) ) ->
            match kSynth tenv tyR with
            | Failure(stack) ->
                Failure( (errorMsg + ": right component is not well-formed", rng) :: stack )
            | Success( KProper(kRefsR,_) ) ->
                Success( KProper(Set.intersect kRefsL kRefsR, noRange) )
            | Success( KOperator(_,_,_) as kop ) ->
                Failure( [(errorMsg + ": right component type has kind" + kop.ToString() + " but a proper type is expected", rng)] )
        | Success( KOperator(_,_,_) as kop ) ->
            Failure( [(errorMsg + ": left component type has kind" + kop.ToString() + " but a proper type is expected",rng)] )
    | Sum(tyL, tyR, rng) ->
        match kSynth tenv tyL with
        | Failure(stack) ->
            Failure( (errorMsg + ": left component is not well-formed", rng) :: stack )
        | Success( KOperator(_,_,_) as kop ) ->
            Failure( [(errorMsg + ": left component has kind " + kop.ToString() + " but a proper type is expected",rng)] )
        | Success( KProper(kRefsL,_) ) ->
            match kSynth tenv tyR with
            | Failure(stack) ->
                Failure( (errorMsg + ": right component is not a well-formed", rng) :: stack )
            | Success( KOperator(_,_,_) as kop ) ->
                Failure( [(errorMsg + ": right component has kind " + kop.ToString() + " but a proper type is expected",rng)] )
            | Success( KProper(kRefsR,_) ) ->
                Success(KProper(Set.difference (Set.intersect kRefsL kRefsR) (Set [Semilattice]), noRange)) 
    | IVar(tyContents, rng) ->
        // really we'd like to have some notion of eqtypes for this
        // or, at least, a notion of certain types having *computable* information orderings
        match kSynth tenv tyContents with
        | Failure(stack) ->
            Failure((errorMsg + ": content type is not well-formed",rng) :: stack)
        | Success( KOperator(_,_,_) as kop ) ->
            Failure( [errorMsg + ": contents type expected to be proper, but instead has kind " + kop.ToString(), rng] )
        | Success( KProper(krefs,_) ) ->
            match krefs.Contains(Toset) with
            | true ->
                Success( KProper(Set [Semilattice;Proset],noRange) )
            | false ->
                Failure( [errorMsg + ": contents type " + tyContents.ToString() + " not totally ordered", rng] )
    | TyAlias(name, rng) ->
        match tyVarEnv.TryFind name with
        | Some(k) ->
            Success(k)
        | None ->
            Failure [errorMsg + " type " + name + " not declared", rng]
    | ForallTy(varId, kind, body, rng) ->
        match kSynth { tenv with tyVarEnv = tyVarEnv.Add(varId, kind) } body with
        | Success(k) ->
            Success(k)
        | Failure(stack) ->
            Failure [errorMsg + ": body not well-formed", rng]
            
