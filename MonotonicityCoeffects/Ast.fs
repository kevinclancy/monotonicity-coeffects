module Ast

type Coeffect =
  | CoeffectMonotone
  | CoeffectAntitone
  | CoeffectRobust
  | CoeffectAny

type Ty =
  /// A primitive, built-in type
  | Base of name : string
  /// A function type
  | FunTy of dom : Ty * t : Coeffect * cod : Ty 
  /// A finite semilattice dictionary
  | Dictionary of dom : Ty * cod : Ty 
  /// A scalar capsule
  | Capsule of ty : Ty * t : Coeffect 
  /// A componentwise ordered product
  | Prod of t1 : Ty * t2 : Ty  
  /// A lexicographically ordered product
  | LexProd of t1 : Ty * t2 : Ty 
  /// A sum
  | Sum of t1 : Ty * t2 : Ty 
  /// An ivar
  | IVar of ty : Ty

type Expr =
  | Int of int
  | Float of float
  | Abs of var : string * ty : Ty * scalar : Coeffect
  | App of fn : Expr * arg : Expr
  | Const of name : string
  | Var of name : string
  | Bot of ty : Ty
  | Join of ty : Ty * e1 : Expr * e2 : Expr 
  | Extract of e1 : Expr * e2 : Expr * e3 : Expr
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
  | ISet of e : Expr
  | IGet of ivar : Expr * elim : Expr 
  | Let of var : string * bound : Expr * body : Expr

