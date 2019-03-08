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
    | Chain

    override this.ToString() =
        match this with
        | Toset -> "TOSET"
        | Poset -> "POSET"
        | Semilattice -> "SEMILATTICE"    
        | Chain -> "CHAIN"

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
  /// A lexicographical product
  | LexProd of t1 : Ty * t2 : Ty * pos : (Position * Position)
  /// A sum
  | Sum of t1 : Ty * t2 : Ty * pos : (Position * Position)
  /// An ivar
  | IVar of ty : Ty * pos : (Position * Position)
  /// Type operator
  | TyOp of varId : string * kind : ProperKind * body : Ty * pos : (Position * Position)
  /// Universally quantified type
  | ForallTy of varId : string * kind : ProperKind * body : Ty * pos : Range
  // Monotone exception monad
  | Exception of ty : Ty * pos : Range
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
    | LexProd(tyL, tyR, rng) ->
        LexProd(Ty.subst a x tyL, Ty.subst a x tyR, rng)
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
    | ForallTy(id, pk, body, rng) ->
        if x = id then
            ForallTy(id,pk,body,rng)
        else
            ForallTy(id,pk,Ty.subst a x body, rng)        
    | Exception(ty, rng) ->
        Exception(Ty.subst a x ty, rng)
    | TyApp(op, arg, rng) ->
        TyApp(Ty.subst a x op, Ty.subst a x arg, rng)

  static member IsEquiv (aliasEnv : Map<string, Ty>) (a : Ty) (b : Ty) : Check<Unit> =
    let errorMsg = "Type " + a.ToString() + " is not equivalent to " + b.ToString()
    check {
        do! withError errorMsg noRange (Ty.IsSubtype aliasEnv a b)
        do! withError errorMsg noRange (Ty.IsSubtype aliasEnv b a)
        return ()
    }

  static member normalize (aliasEnv : Map<string, Ty>, a : Ty) =
    match Ty.reduce aliasEnv a with
    | Some(a') ->
        Ty.normalize(aliasEnv, a')
    | None ->
        a

  static member reduce (aliasEnv : Map<string, Ty>) (a : Ty) : Option<Ty> =
    match a with
    | TyId(name,rng) ->
        match aliasEnv.TryFind(name) with
        | Some(ty) ->
            Some(ty)
        | None ->
            None
    | FunTy(dom,q,cod,rng) ->
        match Ty.reduce aliasEnv dom with
        | Some(dom') ->
            Some(FunTy(dom',q,cod,rng))
        | None ->
            match Ty.reduce aliasEnv cod with
            | Some(cod') ->
                Some(FunTy(dom,q,cod',rng))
            | None ->
                None
    | Dictionary(dom,cod,rng) ->
        match Ty.reduce aliasEnv dom with
        | Some(dom') ->
            Some(Dictionary(dom',cod,rng))
        | None ->
            match Ty.reduce aliasEnv cod with
            | Some(cod') ->
                Some(Dictionary(dom,cod',rng))
            | None ->
                None
    | Capsule(tyContents,q,rng) ->
        match Ty.reduce aliasEnv tyContents with
        | Some(tyContents') ->
            Some(Capsule(tyContents',q,rng))
        | None ->
            None
    | Prod(tyL,tyR,rng) ->
        match Ty.reduce aliasEnv tyL with
        | Some(tyL') ->
            Some(Prod(tyL',tyR,rng))
        | None ->
            match Ty.reduce aliasEnv tyR with
            | Some(tyR') ->
                Some(Prod(tyL,tyR',rng))
            | None ->
                None
    | LexProd(tyL,tyR,rng) ->
        match Ty.reduce aliasEnv tyL with
        | Some(tyL') ->
            Some(LexProd(tyL',tyR,rng))
        | None ->
            match Ty.reduce aliasEnv tyR with
            | Some(tyR') ->
                Some(LexProd(tyL,tyR',rng))
            | None ->
                None
    | Sum(tyL, tyR, rng) ->
        match Ty.reduce aliasEnv tyL with
        | Some(tyL') ->
            Some(Sum(tyL',tyR,rng))
        | None ->
            match Ty.reduce aliasEnv tyR with
            | Some(tyR') ->
                Some(Sum(tyL,tyR',rng))
            | None ->
                None
    | IVar(tyContents, rng) ->
        match Ty.reduce aliasEnv tyContents with
        | Some(tyContents') ->
            Some(IVar(tyContents', rng))
        | None ->
            None
    | TyOp(varId,kind,body,rng) ->
        None
    | ForallTy(varId, kind, body, rng) ->
        None
    | Exception(tyContents, rng) ->
        None
    | TyApp(tyOp, argTy, rng) ->
        match Ty.reduce aliasEnv tyOp with
        | Some(forallTy') ->
            Some(TyApp(forallTy', argTy, rng))
        | None ->
            match Ty.reduce aliasEnv argTy with
            | Some(argTy') ->
                Some(TyApp(tyOp,argTy',rng))
            | None ->
                match tyOp with
                | TyOp(id,_,body,_) ->
                    Some(Ty.subst argTy id body)
                | _ ->
                    failwith "this type 'went wrong'. oops." 

  static member IsSubtype (aliasEnv : Map<string,Ty>) (a : Ty) (b : Ty) : Check<Unit> =
    let errorMsg = a.ToString() + " is not a subtype of " + b.ToString()
    match (Ty.normalize(aliasEnv, a),Ty.normalize(aliasEnv, b)) with
    | TyId(aName,_), TyId(bName,_) ->
        match aName = bName with
        | true -> 
            Result ()
        | false ->
            Error ["Type " + aName + " is not a subtype of " + bName, noRange]
    | FunTy(aDom,aq,aCod,_), FunTy(bDom, bq, bCod, _) ->
        check {
            let! _ = withError ("subtyping doesn't hold among domain types") noRange (Ty.IsSubtype aliasEnv bDom aDom)
            let! _ = withError ("subtyping doesn't hold among codomain types") noRange (Ty.IsSubtype aliasEnv aCod bCod)
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
            let! _ = withError ("domain types not equal") noRange (Ty.IsEquiv aliasEnv aDom bDom)
            let! _ = withError ("codomain types not equal") noRange (Ty.IsEquiv aliasEnv aCod bCod)
            return ()
        }
    | Capsule(aContents,aq,_), Capsule(bContents,bq,_) ->
        match bq <= aq with
        | false ->
            Error [errorMsg + ": " + aq.ToString() + " is not as strong as " + bq.ToString(), noRange]
        | true ->
            check {
                let! _ = withError (errorMsg + ": subtyping among content types does not hold") noRange (Ty.IsSubtype aliasEnv aContents bContents)
                return ()
            }
    | Prod(aL,aR,_), Prod(bL,bR,_) ->
        check {
            let! _ = withError (errorMsg + ": left component") noRange (Ty.IsSubtype aliasEnv aL bL)
            let! _ = withError (errorMsg + ": right component") noRange (Ty.IsSubtype aliasEnv aR bR)
            return ()
        }
    | (LexProd(aL, aR, _), LexProd(bL, bR, _)) ->
        check {
            let! _ = withError (errorMsg + ": left component") noRange (Ty.IsSubtype aliasEnv aL bL)
            let! _ = withError (errorMsg + ": right component") noRange (Ty.IsSubtype aliasEnv aR bR)
            return ()            
        }
    | Sum(aL,aR,_), Sum(bL,bR,_) ->
        check {
            let! _ = withError (errorMsg + ": left component") noRange (Ty.IsSubtype aliasEnv aL bL)
            let! _ = withError (errorMsg + ": right component") noRange (Ty.IsSubtype aliasEnv aR bR)
            return ()
        }    
    | IVar(aContents, _), IVar(bContents, _) ->
        check {
            let! _ = withError errorMsg noRange (Ty.IsSubtype aliasEnv aContents bContents)
            return ()
        }
    /// Type abstraction
    | TyOp(aId, aKind, aBody, _), TyOp(bId, bKind, bBody, _) ->
        match aId = bId with
        | true ->
            match aKind = bKind with
            | true ->
                check {
                    let! _ = withError errorMsg noRange (Ty.IsSubtype aliasEnv aBody bBody)
                    return ()
                }
            | false ->
                Error [errorMsg + ": kind " + aKind.ToString() + " distinct from " + bKind.ToString(), noRange]
        | false ->
            Error [errorMsg + ": bound variable " + aId + " distinct from " + bId, noRange]
    | Exception(aTy,_), Exception(bTy,_) ->
        check {
            let! _ = withError errorMsg noRange (Ty.IsSubtype aliasEnv aTy bTy)
            return ()
        }
    | _ ->
        Error [errorMsg, noRange]

  override this.ToString() =
        match this with
        | TyId(name,_) ->
            name
        | FunTy(dom,q,cod,_) ->
            "(" + dom.ToString() + " ->" + q.ToString() + " " + cod.ToString() + ")"
        | Dictionary(dom,cod,_) ->
            "(" + dom.ToString() + " |> " + cod.ToString() + ")"
        | Capsule(ty,q,_) ->
            "(" + q.ToString() + " " + ty.ToString() + ")"
        | Prod(tyL, tyR, _) ->
            "(" + tyL.ToString() + " * " + tyR.ToString() + ")"
        | LexProd(tyL, tyR, _) ->
            "(" + tyL.ToString() + " ^ " + tyR.ToString() + ")"
        | Sum(tyL, tyR, _) ->
            "(" + tyL.ToString() + " + " + tyR.ToString() + ")"
        | IVar(tyContents,_) ->
            "!" + tyContents.ToString() + "!"
        | TyOp(varId, kind, body,_) ->
            "(TypeFun (" + varId + " : " + kind.ToString() + "). " + body.ToString() + ")"
        | ForallTy(varId, kind, body,_) ->
            "(Forall (" + varId + " : " + kind.ToString() + "). " + body.ToString() + ")"
        | Exception(ty,_) ->
            "[" + ty.ToString() + "]"
        | TyApp(forallTy, argTy, rng) ->
            "(" + forallTy.ToString() + " " + argTy.ToString() + ")" 

/// Interpretation of toset type as a PCF comparison operator
type SemToset = PCF.Term
/// Posets semantically interpreted as PCF type paired with predicate (the latter irrelevant for our purposes)
type SemPoset = PCF.Ty
/// Semilattices semantically interpreted as tuple of PCF terms (bottom element , join operator)
type SemSemilat = { bot : PCF.Term ; join : PCF.Term ; tyDelta : Ty ; iso : PCF.Term }
/// Interpretation of chain type as comparison operator
type SemChain = PCF.Term

type Kind =
  /// poset - underlying PCF proper type (i.e. the set underlying the poset -- the order is an RHOL predicate beyond the 
  ///         scope of this prototype)
  /// toset - Some(semToset) if classified type provides a toset interpretation, None otherwise
  /// semilat - Some(semSemilat) if classified type provides a semilattice interpretation, None otherwise
  /// chain - a semilattice which is also a toset where the total order coincides with the semilattice order
  | KProper of poset : SemPoset * toset : Option<SemToset> * semilat : Option<SemSemilat> * chain : bool * Range
  | KOperator of dom : ProperKind * cod : Kind * Range

/// If k is KProper, return true iff it holds a component representing the proper kind p
let hasKind (k : Kind) (p : ProperKind) =
    match k with
    | KProper(_,toset,semilat,chain,_) ->
        match p with
        | Poset ->
            true
        | Toset ->
            toset.IsSome
        | Semilattice ->
            semilat.IsSome
        | Chain ->
            chain
    | KOperator(_,_,_) ->
        false

type Expr =
  | Int of int * Range
  // "upper bound" int
  | UInt of int * Range
  | Prop of PCF.Prop * Range
  | Forall of tyVar : string * kind : ProperKind * body : Expr * Range
  | ForallApp of forall : Expr * arg : Ty * Range
  | Hom of var : string * semilatTy : Ty * deltaTy : Ty * body : Expr * Range
  | Abs of var : string * ty : Ty * body : Expr * Range
  | App of fn : Expr * arg : Expr * Range
  | Const of name : string * Range
  | Var of name : string * Range
  | Bot of ty : Ty * Range
  | Join of ty : Ty * e1 : Expr * e2 : Expr * Range
  | LessThan of e1 : Expr * e2 : Expr * Range
  /// The eliminator for semilattice dictionaries 
  | Extract of targetTy : Ty * key : string * value : string * acc : string * dict : Expr * body : Expr * Range
  /// The constructor for semilattice dictionaries
  | Cons of e1 : Expr * e2 : Expr * e3 :Expr * Range
  | Fst of pair : Expr * Range
  | Snd of pair : Expr * Range
  | LFst of pair : Expr * Range
  | LSnd of pair : Expr * Range
  | Pair of fst : Expr * snd : Expr * Range
  | LexPair of fst : Expr * snd : Expr * Range
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
  | CoeffectAscription of assertions : List<Coeffect * string> * body : Expr * Range
  | TypeAscription of ty : Ty * body : Expr * Range
  | Hole of Range

  member this.GetRange() : Range =
    match this with
    | Int(_,rng)
    | UInt(_,rng)
    | Prop(_,rng)
    | Forall(_,_,_,rng)
    | ForallApp(_,_,rng)
    | Hom(_,_,_,_,rng)
    | Abs(_,_,_,rng)
    | App(_,_,rng)
    | Const(_, rng)
    | Var(_,rng)
    | Bot(_,rng)
    | Join(_,_,_,rng)
    | LessThan(_,_,rng)
    | Extract(_,_,_,_,_,_,rng)
    | Cons(_,_,_,rng)
    | Fst(_,rng)
    | Snd(_,rng)
    | LFst(_,rng)
    | LSnd(_,rng)
    | LexPair(_,_,rng)
    | Pair(_,_,rng)
    | Case(_,_,_,_,_,_,rng)
    | Inl(_,_,_,rng)
    | Inr(_,_,_,rng)
    | Cap(_,_,rng)
    | Uncap(_,_,_,_,rng)
    | ISet(_,rng)
    | IGet(_,_,_,rng)
    | Let(_,_,_,rng)
    | MLet(_,_,_,rng)
    | MRet(_,rng)
    | CoeffectAscription(_,_,rng)
    | TypeAscription(_,_,rng)
    | Hole(rng) ->
        rng

  override this.ToString() =
    match this with
    | Int(i,_) ->
        i.ToString()
    | UInt(i,_) ->
        "u" + i.ToString()
    | Prop(b,_) ->
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
    | LessThan(e1, e2, _) ->
        "(" + e1.ToString() + " < " + e2.ToString() + ")"
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
    | CoeffectAscription(assertions, expr, _) ->
        let contents = List.map (fun (q,x) -> q.ToString() + " " + x) assertions
        let contents' = String.concat ", " contents
        "@(" + contents' + ")"
    | TypeAscription(ty, expr, _) ->
        "::" + ty.ToString() + " " + expr.ToString()
    | Hom(varId, tySemilat, tyDelta, body, rng) ->
        "(hom (" + varId + " : " + tySemilat.ToString() + " . " + tyDelta.ToString() + ") " + body.ToString() + ")"
    | Hole(rng) ->
        "##"
  
  type Prog = { typeAliases : List<string * Ty> ; exprAliases : Map<string,Expr> ; body : Expr }

// converts a PCF value into a LambdaMC value
let rec toMC (tyAliases : Map<string, Ty>) (t : PCF.Term) (ty : Ty) (tyName : Option<string>) : string =
    match ty, t with
    | TyId(name,_), PCF.PrimUnitVal when name = "Unit" ->
        "()"
    | TyId(name,_), _ when name = "Prop" ->
        match t with
        | PCF.PCFProp(PCF.Known) ->
            "known"
        | PCF.PCFProp(PCF.Unknown) ->
            "unknown"
    | TyId(name,_), PCF.PrimNatVal(n) when name = "Nat" ->
        n.ToString()
    | TyId(name,_), PCF.In1(PCF.Prim("Nat"), PCF.Unit, PCF.PrimNatVal(n)) when name = "NatU" ->
        "u" + n.ToString()
    | TyId(name,_), PCF.In2(_, _, _) when name = "NatU" ->
        "inf"
    | TyId(name,_), _ ->
        match tyAliases.TryFind(name) with
        | Some(ty') ->
            toMC tyAliases t ty' (Some name)
        | None ->
            failwith "unknown type"
    | FunTy(_,_,_,_), _ ->
        "function"
    | Dictionary(dom,cod,_), PCF.Cons(hd, rest) ->
        "{" + toMCDictionary tyAliases t dom cod + " : " + Option.defaultValue (ty.ToString()) tyName + "}" 
    | Capsule(ty',_,_), _ ->
        toMC tyAliases t ty' None
    | Prod(tyL, tyR, _), PCF.Pair(t1, t2) ->
        "(" + (toMC tyAliases t1 tyL None) + ", " + (toMC tyAliases t2 tyR None) + ")"
    | LexProd(tyL, tyR, _), PCF.Pair(t1,t2) ->
        "<<" + (toMC tyAliases t1 tyL None) + ", " + (toMC tyAliases t2 tyR None) + ">>"
    | Sum(tyL, _, _), PCF.In1(_,_,t') ->
        "inl " + (toMC tyAliases t' tyL None)
    | Sum(_, tyR, _), PCF.In2(_,_,t') ->
        "inr " + toMC tyAliases t' tyR None
    | IVar(ty',_), t ->
        "|" + toMCIVar tyAliases t ty' + "|"
    | ForallTy(_,_,_,_), _ ->
        "forall"
    | Exception(ty',_), PCF.In1(_,_,t') ->
        "[" + toMC tyAliases t' ty' None + "]"
    | Exception(ty',_), PCF.In2(_,_,_) ->
        "error"
    | TyApp(forallTy, argTy, rng), t ->
        (toMC tyAliases t (Ty.reduce tyAliases ty).Value (Some(Option.defaultValue (ty.ToString()) tyName)))

and toMCIVar (tyAliases : Map<string, Ty>) (t : PCF.Term) (tyContents : Ty) : string =
    match t with
    | PCF.Cons(e, PCF.EmptyList(_)) ->
      (toMC tyAliases e tyContents None)
    | PCF.Cons(e, rest) ->
      (toMC tyAliases e tyContents None) + ", " + (toMCIVar tyAliases rest tyContents)

and toMCDictionary (tyAliases : Map<string, Ty>) (t : PCF.Term) (dom : Ty) (cod : Ty) : string  =    
    match t with
    | PCF.Cons(PCF.Pair(k,v), PCF.EmptyList(_)) ->
      toMC tyAliases k dom None + " -> " + toMC tyAliases v cod None
    | PCF.Cons(PCF.Pair(k,v), rest) ->
      toMC tyAliases k dom None + " -> " + toMC tyAliases v cod None + ", " + toMCDictionary tyAliases rest dom cod
      
