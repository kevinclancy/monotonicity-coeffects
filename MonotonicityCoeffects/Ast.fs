module Ast

open Microsoft.FSharp.Text.Lexing
open System

type Range = Position * Position

type Coeffect =
  | CoeffectMonotone
  | CoeffectAntitone
  | CoeffectRobust
  | CoeffectAny

  static member Ign =
    CoeffectRobust

  static member Use =
    CoeffectMonotone

  //scalar composition
  static member (%%) (q,r) = 
    match r with
    | CoeffectRobust ->
        CoeffectRobust
    | CoeffectMonotone ->
        q
    | CoeffectAntitone ->
        match q with
        | CoeffectMonotone ->
            CoeffectAntitone
        | CoeffectAntitone ->
            CoeffectMonotone
        | CoeffectRobust ->
            CoeffectRobust
        | CoeffectAny ->
            CoeffectAny
    | CoeffectAny ->
        CoeffectAny
        
  // scalar contraction
  static member (++) (q,r) =
    match r with
    | CoeffectRobust ->
        q
    | CoeffectMonotone ->
        match q with
        | CoeffectMonotone
        | CoeffectRobust ->
            CoeffectMonotone
        | CoeffectAntitone
        | CoeffectAny ->
            CoeffectAny
    | CoeffectAntitone ->
        match q with
        | CoeffectAntitone
        | CoeffectRobust ->
            CoeffectAntitone
        | CoeffectMonotone
        | CoeffectAny ->
            CoeffectAny
    | CoeffectAny ->
        CoeffectAny
            
  static member LessThan (a : Coeffect) (b : Coeffect) =
    match (a,b) with
    | CoeffectRobust, _ -> true
    | CoeffectAntitone, CoeffectAntitone -> true
    | CoeffectAntitone, CoeffectAny -> true
    | CoeffectMonotone, CoeffectMonotone -> true
    | CoeffectMonotone, CoeffectAny -> true
    | CoeffectAny, CoeffectAny -> true
    | _, _ -> false

  override this.ToString() =
    match this with
    | CoeffectMonotone -> "+"
    | CoeffectAntitone -> "-"
    | CoeffectRobust -> "*"
    | CoeffectAny -> "?"

type ProperKind =
    | Toset 
    | Proset
    | Semilattice

    override this.ToString() =
        match this with
        | Toset -> "TOSET"
        | Proset -> "PROSET"
        | Semilattice -> "SEMILATTICE"                

type Kind =
  | KProper of Set<ProperKind> * Range
  | KOperator of dom : ProperKind * cod : Kind * Range

let noPos : Position = {
    pos_fname = ""
    pos_lnum = 0
    pos_bol = 0
    pos_cnum = 0
}

let noRange = (noPos, noPos)

type SubtypeResult =
    | Success
    | Failure of List<string>
    
type Ty =
  | BaseTy of name : string * pos : (Position * Position)
  /// A function type
  | FunTy of dom : Ty * q : Coeffect * cod : Ty * pos : (Position * Position)
  /// A finite semilattice dictionary
  | Dictionary of dom : Ty * cod : Ty * pos : (Position * Position)
  /// A scalar capsule
  | Capsule of ty : Ty * q : Coeffect * pos : (Position * Position)
  /// A componentwise ordered product
  | Prod of t1 : Ty * t2 : Ty  * pos : (Position * Position)
  /// A sum
  | Sum of t1 : Ty * t2 : Ty * pos : (Position * Position)
  /// An ivar
  | IVar of ty : Ty * pos : (Position * Position)
  /// A type from the type environmnet
  | TyAlias of name : string * pos : (Position * Position)
  /// Type abstraction
  | ForallTy of varId : string * kind : ProperKind * body : Ty * pos : (Position * Position)
  // Monotone partiality monad
  | Partial of ty : Ty * pos : Range

  static member IsEquiv (a : Ty) (b : Ty) : SubtypeResult =
    let errorMsg = "Type " + a.ToString() + " is not equivalent to " + b.ToString()
    match Ty.IsSubtype a b with
    | Success ->
        match Ty.IsSubtype b a with
        | Success ->
            Success
        | Failure(stack) ->
            Failure(errorMsg :: stack)
    | Failure(stack) ->
        Failure(errorMsg :: stack)

  static member IsSubtype (a : Ty) (b : Ty) : SubtypeResult =
    let errorMsg = a.ToString() + " is not a subtype of " + b.ToString()
    match (a,b) with
    | BaseTy(aName,_), BaseTy(bName,_) ->
        match aName = bName with
        | true -> 
            Success
        | false ->
            Failure ["Type " + aName + " is not a subtype of " + bName]
    | FunTy(aDom,aq,aCod,_), FunTy(bDom, bq, bCod, _) ->
        match Ty.IsSubtype bDom aDom with
        | Success ->
            match bq <= aq with
            | true ->
                match Ty.IsSubtype aCod bCod with
                | Success ->
                    Success
                | Failure(stack) ->
                    Failure(errorMsg + ": subtyping doesn't hold among domain types" :: stack)
            | false ->
                Failure(errorMsg + ": " + aq.ToString() + " is not a stronger capability than " + bq.ToString() :: stack)
        | Failure(stack) ->
            Failure(errorMsg + ": subtyping doesn't hold among codomain types" :: stack)
    | Dictionary(aDom,aCod,_), Dictionary(bDom,bCod,_) ->
        // should be able to relax this to contravariant domain, covariant codomain
        match Ty.IsEquiv aDom bDom with
        | Success ->
            match Ty.IsEquiv aCod bCod with
            | Success ->
                Success
            | Failure(stack) ->
                Failure(errorMsg :: stack)
        | Failure(stack) ->
            Failure(errorMsg :: stack)
    | Capsule(aContents,aq,_), Capsule(bContents,bq,_) ->
        match bq <= aq with
        | false ->
            Failure [errorMsg + ": " + aq.ToString() + " is not as strong as " + bq.ToString()]
        | true ->
            match Ty.IsSubtype aContents bContents with
            | Failure(stack) ->
                Failure(errorMsg + ": subtyping among content types does not hold" :: stack)
            | Success ->
                Success
    | Prod(aL,aR,_), Prod(bL,bR,_) ->
        match Ty.IsSubtype aL bL with
        | Success ->
            match Ty.IsSubtype aR bR with
            | Success ->
                Success
            | Failure(stack) ->
                Failure(errorMsg + ": left component" :: stack)
        | Failure(stack) ->
            Failure(errorMsg + ": right component" :: stack)
    | Sum(aL,aR,_), Sum(bL,bR,_) ->
        match Ty.IsSubtype aL bL with
        | Success ->
            match Ty.IsSubtype aR bR with
            | Success ->
                Success
            | Failure(stack) ->
                Failure(errorMsg + ": left component" :: stack)
        | Failure(stack) ->
            Failure(errorMsg + ": right component" :: stack)        
    | IVar(aContents, _), IVar(bContents, _) ->
        match Ty.IsSubtype aContents bContents with
        | Success ->
            Success
        | Failure(stack) ->
            Failure(errorMsg :: stack)
    /// A type from the type environmnet
    | TyAlias(aName,_), TyAlias(bName,_) ->
        match aName = bName with
        | true ->
            Success
        | false ->
            Failure [errorMsg + ": type alias " + aName + " is distinct from " + bName]
    /// Type abstraction
    | ForallTy(aId, aKind, aBody, _), ForallTy(bId, bKind, bBody, _) ->
        match aId = bId with
        | true ->
            match aKind = bKind with
            | true ->
                match Ty.IsSubtype aBody bBody with
                | Success ->
                    Success
                | Failure(stack) ->
                    Failure(errorMsg :: stack)
            | false ->
                Failure [errorMsg + ": kind " + aKind.ToString() + " distinct from " + bKind.ToString()]
        | false ->
            Failure [errorMsg + ": bound variable " + aId + " distinct from " + bId]
    | Partial(aTy,_), Partial(bTy,_) ->
        match Ty.IsSubtype aTy bTy with
        | Success ->
            Success
        | Failure(stack) ->
            Failure(errorMsg :: stack)

  override this.ToString() =
        match this with
        | BaseTy(name,_) ->
            "#" + name
        | FunTy(dom,q,cod,_) ->
            "(" + dom.ToString() + q.ToString() + cod.ToString() + ")"
        | Dictionary(dom,cod,_) ->
            "(" + dom.ToString() + " |> " + cod.ToString() + ")"
        | Capsule(ty,q,_) ->
            "(" + ty.ToString() + " " + q.ToString() + ")"
        | Prod(tyL, tyR, _) ->
            "(" + tyL.ToString() + " * " + tyR.ToString() + ")"
        | Sum(tyL, tyR, _) ->
            "(" + tyL.ToString() + " + " + tyR.ToString() + ")"
        | IVar(tyContents,_) ->
            "!" + tyContents.ToString() + "!"
        | TyAlias(name,_) ->
            name
        | ForallTy(varId, kind, body,_) ->
            "(Forall (" + varId + " : " + kind.ToString() + "). " + body.ToString() + ")"
        | Partial(ty,_) ->
            "[" + ty.ToString() + "]"

type Expr =
  | Int of int * Range
  | Float of float * Range
  | Forall of tyVar : string * kind : ProperKind * body : Expr * Range
  | ForallApp of forall : Expr * arg : Ty * Range
  | Abs of var : string * ty : Ty * scalar : Coeffect * body : Expr * Range
  | App of fn : Expr * arg : Expr * Range
  | Const of name : string * Range
  | Var of name : string * Range
  | Bot of ty : Ty * Range
  | Join of ty : Ty * e1 : Expr * e2 : Expr * Range
  /// The eliminator for semilattice dictionaries 
  | Extract of targetTy : Ty * key : string * value : string * acc : string * dict : Expr * body : Expr * Range
  /// The constructor for semilattice dictionaries
  | Cons of e1 : Expr * e2 : Expr * e3 :Expr * Range
  | Fst of pair : Expr * Range
  | Snd of pair : Expr * Range
  | Pair of fst : Expr * snd : Expr * Range
  | Case of scrut : Expr * target : Ty * lname : string * 
            lElim : Expr * rname : string * rElim : Expr * Range
  | Inl of lty : Ty * rTy : Ty * e : Expr * Range
  | Inr of lty : Ty * rTy : Ty * e : Expr * Range
  | Cap of q : Coeffect * e : Expr * Range
  | Uncap of q : Coeffect * varId : string * capsule : Expr * body : Expr * Range
  /// Constructor for ivars
  | ISet of e : Expr * Range
  /// Destructor for IVars
  | IGet of contentsBinder : string * ivar : Expr * elim : Expr * Range 
  | Let of var : string * bound : Expr * body : Expr * Range
  | MLet of var : string * bound : Expr * body : Expr * Range 
  | MRet of expr : Expr * Range

  type Prog = { typeAliases : Map<string, Ty> ; exprAliases : Map<string,Expr> ; body : Expr }