module Ast

open Microsoft.FSharp.Text.Lexing

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

type Kind =
  | Toset
  | Proset
  | Semilattice
  
  override this.ToString() =
    match this with
    | Toset -> "TOSET"
    | Proset -> "PROSET"
    | Semilattice -> "SEMILATTICE"

let noPos : Position = {
    pos_fname = ""
    pos_lnum = 0
    pos_bol = 0
    pos_cnum = 0
}

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
  | Int of int
  | Float of float
  | Forall of tyVar : string * kind : Kind * body : Expr
  | Abs of var : string * ty : Ty * scalar : Coeffect * body : Expr
  | App of fn : Expr * arg : Expr
  | Const of name : string
  | Var of name : string
  | Bot of ty : Ty
  | Join of ty : Ty * e1 : Expr * e2 : Expr
  /// The eliminator for semilattice dictionaries
  | Extract of key : string * value : string * acc : string * dict : Expr * body : Expr
  /// The constructor for semilattice dictionaries
  | Cons of e1 : Expr * e2 : Expr * e3 :Expr
  | Fst of pair : Expr
  | Snd of pair : Expr
  | Pair of fst : Expr * snd : Expr
  | Case of scrutTyL : Ty * scrutTyR : Ty * scrut : Expr * lname : string * 
            lElim : Expr * rname : string * rElim : Expr 
  | Inl of lty : Ty * rTy : Ty * e : Expr
  | Inr of lty : Ty * rTy : Ty * e : Expr 
  | Cap of q : Coeffect * e : Expr
  | Uncap of e : Expr
  /// Constructor for ivars
  | ISet of e : Expr
  /// Destructor for IVars
  | IGet of contentsBinder : string * ivar : Expr * elim : Expr 
  | Let of var : string * bound : Expr * body : Expr

  type Prog = { typeAliases : Map<string, Ty> ; exprAliases : Map<string,Expr> ; body : Expr }