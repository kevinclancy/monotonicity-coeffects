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
  // Type abstraction application
  | ForallTyApp of forall : Ty * arg : Ty * Range

  static member subst (a : Ty) (x : string) (s : Ty) : Ty =
    match a with
    | BaseTy(name,rng) ->
        BaseTy(name,rng)
    | FunTy(dom,q,cod,rng) ->
        FunTy(Ty.subst dom x s, q, Ty.subst cod x s, rng)
    | Dictionary(dom,cod,rng) ->
        Dictionary(Ty.subst dom x s, Ty.subst cod x s, rng)
    | Capsule(tyContents,q,rng) ->
        Capsule(Ty.subst tyContents x s, q, rng)
    | Prod(tyL,tyR,rng) ->
        Prod(Ty.subst tyL x s, Ty.subst tyR x s, rng)
    | Sum(tyL, tyR, rng) ->
        Sum(Ty.subst tyL x s, Ty.subst tyR x s, rng)
    | IVar(tyContents, rng) ->
        IVar(Ty.subst tyContents x s, rng)
    | TyAlias(name,rng) ->
        if name = x then
            s
        else
            TyAlias(name,rng)
    | ForallTy(varId,kind,body,rng) ->
        if varId = x then
            ForallTy(varId, kind, body, rng)
        else
            ForallTy(varId,kind,Ty.subst body x s, rng)
    | Partial(tyContents, rng) ->
        Partial(Ty.subst tyContents x s, rng)
    | ForallTyApp(forallTy, argTy, rng) ->
        ForallTyApp(Ty.subst forallTy x s, Ty.subst argTy x s, rng)

  static member normalize (a : Ty) : Ty =
    match a with
    | ForallTyApp(ForallTy(varId,kind,body,_), argTy, _) ->
        Ty.normalize (Ty.subst body varId argTy)
    | _ ->
        a

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
                Failure [errorMsg + ": " + aq.ToString() + " is not a stronger capability than " + bq.ToString()]
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
    | _ ->
        Failure [errorMsg]

  override this.ToString() =
        match this with
        | BaseTy(name,_) ->
            "#" + name
        | FunTy(dom,q,cod,_) ->
            "(" + dom.ToString() + " " + q.ToString() + "-> " + cod.ToString() + ")"
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
        | ForallTyApp(forallTy, argTy, rng) ->
            "(" + forallTy.ToString() + " " + argTy.ToString() + ")" 

type Expr =
  | Int of int * Range
  | Float of float * Range
  | Forall of tyVar : string * kind : ProperKind * body : Expr * Range
  | ForallApp of forall : Expr * arg : Ty * Range
  | Abs of var : string * ty : Ty * body : Expr * Range
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

  override this.ToString() =
    match this with
    | Int(i,_) ->
        i.ToString()
    | Float(f,_) ->
        f.ToString()
    | Forall(tyVar,kind,body,_) ->
        "(" + "forall " + tyVar.ToString() + " : " + kind.ToString() + " . " + body.ToString() + ")" 
    | ForallApp(forall,arg,rng) ->
        "(" + forall.ToString() + " " + arg.ToString() + ")"
    | Abs(var,ty,body,_) ->
        "(fun " + var + " : " + ty.ToString() + " . " + body.ToString() + ")"
    | App(fn,arg,_) ->
        "( " + fn.ToString() + " " + arg.ToString() + ")"
    | Const(nm,_) ->
        nm
    | Var(nm,_) ->
        nm
    | Bot(ty,_) ->
        "(bot " + ty.ToString() + ")"
    | Join(ty,e1,e2,_) ->
        "(join " + ty.ToString() + " " + e1.ToString() + " " + e2.ToString() + ")"
    | Extract(targetTy,k,v,acc,dict,body,_) ->
        "let cons " + targetTy.ToString() + " " + k + " " + v + " " + acc + " = " + dict.ToString() + " in\n"
          + body.ToString() + "end"
    | Cons(k,v,dict,_) ->
        "(cons " + k.ToString() + " " + v.ToString() + " " + dict.ToString() + ")" 
    | Fst(pair,_) ->
        "(fst " + pair.ToString() + ")"
    | Snd(pair,_) ->
        "(snd " + pair.ToString() + ")"
    | Pair(fst,snd,_) ->
        "(" + fst.ToString() + " , " + snd.ToString() + " )"
    | Case(scrut, target, lname, lElim, rname, rElim, _) ->
        "(case " + scrut.ToString() + " " + target.ToString() + " " + lname 
         + " -> " + lElim.ToString() + " " + rname + " -> " + rElim.ToString() + ")"
    | Inl(_,_,e,_) ->
        "(inl " + e.ToString() + ")"
    | Inr(_,_,e,_) ->
        "(inr " + e.ToString() + ")"
    | Cap(q,e,_) ->
        "(cap " + q.ToString() + " " + e.ToString() + ")"
    | Uncap(q,varId,capsule,body,_) ->
        "let cap " + q.ToString() + " " + varId + " = " + capsule.ToString() + " in \n" + body.ToString() + "\nend"
    | ISet(e,_) ->
        "(iset " + e.ToString() + ")"
    | IGet(id,ivar,elim,_) ->
        "let | " + id + " | = " + ivar.ToString() + " in \n" + elim.ToString() + "\nend"
    | Let(var,bound,body,_) ->
        "let " + var + " = " + bound.ToString() + " in \n" + body.ToString() + "\nend"
    | MLet(var,bound,body,_) ->
        "let [" + var + "] = " + bound.ToString() + " in \n" + body.ToString() + "\nend"
    | MRet(e,_) ->
        "[" + e.ToString() + "]"

  type Prog = { typeAliases : Map<string, Ty> ; exprAliases : Map<string,Expr> ; body : Expr }