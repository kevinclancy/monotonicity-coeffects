module Ast

open Microsoft.FSharp.Text.Lexing
open System
open CheckComputation

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
    | Poset
    | Semilattice

    override this.ToString() =
        match this with
        | Toset -> "TOSET"
        | Poset -> "POSET"
        | Semilattice -> "SEMILATTICE"                

/// Semantic interpretation of toset as a PCF comparison operator
type SemToset = PCF.Term
/// Posets semantically interpreted as PCF type paired with predicate (the latter irrelevant for our purposes)
type SemPoset = PCF.Ty
/// Semilattices semantically interpreted as tuple of PCF terms (bottom element , join operator)
type SemSemilat = { bot : PCF.Term ; join : PCF.Term }

type Kind =
  /// poset - underlying PCF proper type (i.e. the set underlying the poset -- the order is an RHOL predicate beyond the 
  ///         scope of this prototype)
  /// toset - Some(semToset) if classified type provides a toset interpretation, None otherwise
  /// semilat - Some(semSemilat) if classified type provides a semilattice interpretation, None otherwise
  | KProper of poset : SemPoset * toset : Option<SemToset> * semilat : Option<SemSemilat> * Range
  | KOperator of dom : ProperKind * cod : Kind * Range

/// If k is KProper, return true iff it holds a component representing the proper kind p
let hasKind (k : Kind) (p : ProperKind) =
    match k with
    | KProper(_,toset,semilat,_) ->
        match p with
        | Poset ->
            true
        | Toset ->
            toset.IsSome
        | Semilattice ->
            semilat.IsSome
    | KOperator(_,_,_) ->
        false

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
  // In order of precedence,
  // could be a type variable, a type identifier, or a base type
  | TyId of name : string * pos : (Position * Position)
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
  /// Type operator
  | TyOp of varId : string * kind : ProperKind * body : Ty * pos : (Position * Position)
  /// Universally quantified type
  | ForallTy of varId : string * kind : ProperKind * body : Ty * pos : Range
  // Monotone partiality monad
  | Partial of ty : Ty * pos : Range
  // Type abstraction application
  | TyApp of op : Ty * arg : Ty * Range

  static member subst (a : Ty) (x : string) (b : Ty) : Ty =
    match b with
    | TyId(id,rng) ->
        if id = x then
            a
        else 
            TyId(id,rng)
    | FunTy(dom,q,cod,rng) -> 
        FunTy(Ty.subst a x dom, q, Ty.subst a x cod, rng) 
    | Dictionary(dom,cod,rng) ->
        Dictionary(Ty.subst a x dom, Ty.subst a x cod, rng)
    /// A scalar capsule
    | Capsule(ty,q,rng) ->
        Capsule(Ty.subst a x ty, q, rng)
    /// A componentwise ordered product
    | Prod(tyL, tyR, rng) ->
        Prod(Ty.subst a x tyL, Ty.subst a x tyR, rng)
    | Sum(tyL, tyR, rng) ->
        Sum(Ty.subst a x tyL, Ty.subst a x tyR, rng)
    /// An ivar
    | IVar(ty, rng) ->
        IVar(Ty.subst a x ty, rng)
    | TyOp(id, pk, body, rng) ->
        if x = id then
            TyOp(id,pk,body,rng)
        else
            TyOp(id,pk,Ty.subst a x body, rng)
    | Partial(ty, rng) ->
        Partial(Ty.subst a x ty, rng)
    | TyApp(op, arg, rng) ->
        TyApp(Ty.subst a x op, Ty.subst a x arg, rng)

  static member IsEquiv (a : Ty) (b : Ty) : Check<Unit> =
    let errorMsg = "Type " + a.ToString() + " is not equivalent to " + b.ToString()
    check {
        do! withError errorMsg noRange (Ty.IsSubtype a b)
        do! withError errorMsg noRange (Ty.IsSubtype b a)
        return ()
    }

  static member IsSubtype (a : Ty) (b : Ty) : Check<Unit> =
    let errorMsg = a.ToString() + " is not a subtype of " + b.ToString()
    match (a,b) with
    | TyId(aName,_), TyId(bName,_) ->
        match aName = bName with
        | true -> 
            Result ()
        | false ->
            Error ["Type " + aName + " is not a subtype of " + bName, noRange]
    | FunTy(aDom,aq,aCod,_), FunTy(bDom, bq, bCod, _) ->
        check {
            let! _ = withError ("subtyping doesn't hold among domain types") noRange (Ty.IsSubtype bDom aDom)
            let! _ = withError ("subtyping doesn't hold among codomain types") noRange (Ty.IsSubtype aCod bCod)
            let! _ =
                match bq <= aq with
                | true ->
                    Result ()
                | false ->
                    Error [errorMsg + ": " + aq.ToString() + " is not a stronger capability than " + bq.ToString(), noRange]
            return ()
        }
    | Dictionary(aDom,aCod,_), Dictionary(bDom,bCod,_) ->
        // should be able to relax this to contravariant domain, covariant codomain
        check {
            let! _ = withError ("domain types not equal") noRange (Ty.IsEquiv aDom bDom)
            let! _ = withError ("codomain types not equal") noRange (Ty.IsEquiv aCod bCod)
            return ()
        }
    | Capsule(aContents,aq,_), Capsule(bContents,bq,_) ->
        match bq <= aq with
        | false ->
            Error [errorMsg + ": " + aq.ToString() + " is not as strong as " + bq.ToString(), noRange]
        | true ->
            check {
                let! _ = withError (errorMsg + ": subtyping among content types does not hold") noRange (Ty.IsSubtype aContents bContents)
                return ()
            }
    | Prod(aL,aR,_), Prod(bL,bR,_) ->
        check {
            let! _ = withError (errorMsg + ": left component") noRange (Ty.IsSubtype aL bL)
            let! _ = withError (errorMsg + ": right component") noRange (Ty.IsSubtype aR bR)
            return ()
        }
    | Sum(aL,aR,_), Sum(bL,bR,_) ->
        check {
            let! _ = withError (errorMsg + ": left component") noRange (Ty.IsSubtype aL bL)
            let! _ = withError (errorMsg + ": right component") noRange (Ty.IsSubtype aR bR)
            return ()
        }    
    | IVar(aContents, _), IVar(bContents, _) ->
        check {
            let! _ = withError errorMsg noRange (Ty.IsSubtype aContents bContents)
            return ()
        }
    /// Type abstraction
    | TyOp(aId, aKind, aBody, _), TyOp(bId, bKind, bBody, _) ->
        match aId = bId with
        | true ->
            match aKind = bKind with
            | true ->
                check {
                    let! _ = withError errorMsg noRange (Ty.IsSubtype aBody bBody)
                    return ()
                }
            | false ->
                Error [errorMsg + ": kind " + aKind.ToString() + " distinct from " + bKind.ToString(), noRange]
        | false ->
            Error [errorMsg + ": bound variable " + aId + " distinct from " + bId, noRange]
    | Partial(aTy,_), Partial(bTy,_) ->
        check {
            let! _ = withError errorMsg noRange (Ty.IsSubtype aTy bTy)
            return ()
        }
    | _ ->
        Error [errorMsg, noRange]

  override this.ToString() =
        match this with
        | TyId(name,_) ->
            name
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
        | TyOp(varId, kind, body,_) ->
            "(TypeFun (" + varId + " : " + kind.ToString() + "). " + body.ToString() + ")"
        | ForallTy(varId, kind, body,_) ->
            "(Forall (" + varId + " : " + kind.ToString() + "). " + body.ToString() + ")"
        | Partial(ty,_) ->
            "[" + ty.ToString() + "]"
        | TyApp(forallTy, argTy, rng) ->
            "(" + forallTy.ToString() + " " + argTy.ToString() + ")" 

type Expr =
  | Int of int * Range
  | Bool of bool * Range
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
    | Bool(b,_) ->
        b.ToString().ToLower()
    | Forall(tyVar,kind,body,_) ->
        "(" + "forall " + tyVar.ToString() + " : " + kind.ToString() + " . " + body.ToString() + ")" 
    | ForallApp(forall,arg,rng) ->
        "(" + forall.ToString() + " " + arg.ToString() + ")"
    | Abs(var,ty,body,_) ->
        "(fun " + var + " : " + ty.ToString() + " . " + body.ToString() + ")"
    | App(fn,arg,_) ->
        "(" + fn.ToString() + " " + arg.ToString() + ")"
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
          + body.ToString() + "\nend"
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