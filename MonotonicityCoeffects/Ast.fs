module Ast

open Microsoft.FSharp.Text.Lexing
open System

type Range = Position * Position

type Coeffect =
  | CoeffectMonotone
  | CoeffectAntitone
  | CoeffectRobust
  | CoeffectAny

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
  | ForallTy of varId : string * kind : Kind * body : Ty * pos : (Position * Position)

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

type Expr =
  | Int of int * Range
  | Float of float * Range
  | Forall of tyVar : string * kind : Kind * body : Expr * Range
  | Abs of var : string * ty : Ty * scalar : Coeffect * body : Expr * Range
  | App of fn : Expr * arg : Expr * Range
  | Const of name : string * Range
  | Var of name : string * Range
  | Bot of ty : Ty * Range
  | Join of ty : Ty * e1 : Expr * e2 : Expr * Range
  /// The eliminator for semilattice dictionaries 
  | Extract of key : string * value : string * acc : string * dict : Expr * body : Expr * Range
  /// The constructor for semilattice dictionaries
  | Cons of e1 : Expr * e2 : Expr * e3 :Expr * Range
  | Fst of pair : Expr * Range
  | Snd of pair : Expr * Range
  | Pair of fst : Expr * snd : Expr * Range
  | Case of scrutTyL : Ty * scrutTyR : Ty * scrut : Expr * lname : string * 
            lElim : Expr * rname : string * rElim : Expr * Range
  | Inl of lty : Ty * rTy : Ty * e : Expr * Range
  | Inr of lty : Ty * rTy : Ty * e : Expr * Range
  | Cap of q : Coeffect * e : Expr * Range
  | Uncap of e : Expr * Range
  /// Constructor for ivars
  | ISet of e : Expr * Range
  /// Destructor for IVars
  | IGet of contentsBinder : string * ivar : Expr * elim : Expr * Range 
  | Let of var : string * bound : Expr * body : Expr * Range

  type Prog = { typeAliases : Map<string, Ty> ; exprAliases : Map<string,Expr> ; body : Expr }