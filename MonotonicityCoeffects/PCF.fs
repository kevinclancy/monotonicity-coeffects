module PCF

open CheckComputation
open System.Reflection.Metadata.Ecma335
open System.Runtime.Serialization

type Ty =
    | Unit
    | List of elemTy : Ty 
    | Prod of lTy : Ty * rTy : Ty
    | Sum of lTy : Ty * rTy : Ty
    | Fun of dom : Ty * cod : Ty
    | Prim of name : string // semilattice primitives: unit, bool, nat
    | TyVar of name : string
    | ForallTy of id : string * body : Ty

    override this.ToString() =
        match this with
        | Unit ->
            "Unit"
        | List(elemTy) ->
            "List[" + elemTy.ToString() + "]"
        | Prod(lTy, rTy) ->
            "(" + lTy.ToString() + "*" + rTy.ToString() + ")"
        | Sum(lTy, rTy) ->
            "(" + lTy.ToString() + "+" + rTy.ToString() + ")"
        | Fun(dom,cod) ->
            "(" + dom.ToString() + " -> " + cod.ToString() + ")"
        | Prim(name) ->
            name
        | TyVar(name) ->
            name
        | ForallTy(id, body) ->
            "(Forall " + id + "." + body.ToString() + ")"

type Term =
    | Var of name : string
    | Pair of l : Term * r : Term
    | Proj1 of Term
    | Proj2 of Term
    | In1 of Ty * Ty * Term
    | In2 of Ty * Ty * Term
    | App of fn : Term * arg : Term
    | Abs of id : string * dom : Ty * body : Term
    | TyApp of forall : Term * arg : Ty
    | Forall of id : string * body : Term
    | PrimFun of name : string * domTy : Ty * codTy : Ty * impl : (Term -> Term)
    | PrimNatVal of int
    | PrimUnitVal
    | EmptyList of elemTy : Ty
    | Cons of head : Term * rest : Term
    | ListCase of scrutinee : Term * nilCase : Term * consCase : Term
    | SumCase of scrutinee : Term * leftCase : Term * rightCase : Term
    | LetRec of funName : string * parName : string * domTy : Ty  * codTy : Ty * body : Term

    override this.ToString() =
        match this with
        | Var(n) ->
            n
        | Pair(l,r) ->
            "(" + l.ToString() + ", " + r.ToString() + ")"
        | Proj1(p) ->
            "(π1 " + p.ToString() + ")"
        | Proj2(p) ->
            "(π2 " + p.ToString() + ")"
        | In1(_,_,t) ->
            "(i1 " + t.ToString() + ")"
        | In2(_,_,t) ->
            "(i2 " + t.ToString() + ")"
        | App(fn, arg) ->
            "(" + fn.ToString() + " " + arg.ToString() + ")"
        | Abs(id,dom,body) ->
            "(fn " + id + ":" + dom.ToString() + "." + body.ToString() + ")"
        | TyApp(forall,arg) ->
            "(" + forall.ToString() + " !" + arg.ToString() + ")"
        | Forall(id,body) ->
            "(tf " + id + "." + body.ToString() + ")"
        | PrimFun(name, domTy, codTy, impl) ->
            name
        | PrimNatVal(n) ->
            n.ToString()
        | PrimUnitVal ->
            "()"
        | EmptyList(_) ->
            "[]"
        | Cons(hd, rest) ->
            hd.ToString() + " :: " + rest.ToString() 
        | ListCase(scrut, nilCase, conCase) ->
            "(case " + scrut.ToString() + " with | nil -> " + nilCase.ToString() + " | _ :: _ -> " + conCase.ToString() + ")"
        | SumCase(scrut, leftCase, rightCase) ->
            "(case " + scrut.ToString() + " with | κ1 -> " + leftCase.ToString() + " | κ2 -> " + rightCase.ToString() + ")"
        | LetRec(funName, parName, domTy, codTy, body) ->
            "(letrec " + funName + " " + parName + " = " + body.ToString() + ")"

type Prop =
   | Unknown 
   | Known

let pcfTrue = In1(Unit,Unit,PrimUnitVal)
let pcfFalse = In2(Unit,Unit,PrimUnitVal)
let makePcfBool b = if b then In1(Unit,Unit,PrimUnitVal) else In2(Unit,Unit,PrimUnitVal)
let makePcfProp p = match p with Known -> In1(Unit, Unit, PrimUnitVal) | Unknown -> In2(Unit,Unit,PrimUnitVal)
let pPropTy = Sum(Unit,Unit)
let pBoolTy = Sum(Unit,Unit)
let pUnitTy = Unit

let (|PCFBool|) (t : Term) =
    match t with
    | In1(Unit,Unit,PrimUnitVal) ->
        true
    | In2(Unit,Unit,PrimUnitVal) ->
        false
    | _ ->
        failwith "This program has 'gone wrong'. Oops."

let (|PCFProp|) (t : Term) = 
    match t with
    | In1(Unit, Unit, PrimUnitVal) ->
        Known
    | In2(Unit, Unit, PrimUnitVal) ->
        Unknown
    | _ ->
        failwith "This program has 'gone wrong'. Oops."

/// subs - list of variable identifier/term pairs to substitute into t
/// t - the term to substitute subs into
let rec subst (subs : List<string * Term>) (t : Term) =
    match t with
    | Var(id) ->
        match List.tryFind (fun (x,s) -> x = id) subs with
        | Some(_,s) ->
            s
        | None ->
            Var(id)
    | Pair(e1, e2) ->
        Pair(subst subs e1, subst subs e2)
    | Proj1(e) ->
        Proj1(subst subs e)
    | Proj2(e) ->
        Proj2(subst subs e)
    | In1(ty1, ty2, e) ->
        In1(ty1, ty2, subst subs e)
    | In2(ty1, ty2, e) ->
        In2(ty1, ty2, subst subs e)
    | App(fn, arg) ->
        App(subst subs fn, subst subs arg)
    | Abs(id, dom, body) ->
        let subs' = List.filter (fun (x,s) -> not (x = id)) subs
        Abs(id, dom, subst subs' body)
    | TyApp(forall, arg) ->
        TyApp(subst subs forall, arg)
    | Forall(id, body) ->
        Forall(id, subst subs body)
    | PrimFun(name, domTy, codTy, impl) ->
        PrimFun(name, domTy, codTy, impl)
    | PrimNatVal(n) ->
        PrimNatVal(n)
    | PrimUnitVal ->
        PrimUnitVal
    | EmptyList(elemTy) ->
        EmptyList(elemTy)
    | Cons(t1, t2) ->
        Cons(subst subs t1, subst subs t2)
    | ListCase(scrut, nil, cons) ->
        ListCase(subst subs scrut, subst subs nil, subst subs cons)
    | SumCase(scrut, lCase, rCase) ->
        SumCase(subst subs scrut, subst subs lCase, subst subs rCase)
    | LetRec(funName, parName, domTy, codTy, body) ->
        let subs' = List.filter (fun (x,s) -> not (x = funName || x = parName)) subs
        LetRec(funName, parName, domTy, codTy, subst subs' body)

let rec tySubstTy (a : Ty) (x : string) (b : Ty) =
    match b with
    | Unit ->
        Unit
    | List(elemTy) ->
        List(tySubstTy a x elemTy)
    | Prod(lTy, rTy) ->
        Prod(tySubstTy a x lTy, tySubstTy a x rTy)
    | Sum(lTy, rTy) ->
        Sum(tySubstTy a x lTy, tySubstTy a x rTy)
    | Fun(dom, cod) ->
        Fun(tySubstTy a x dom, tySubstTy a x cod)
    | Prim(name) ->
        Prim(name)
    | TyVar(name) ->
        if name = x then
            a
        else
            TyVar(name)
    | ForallTy(id, body) ->
        if x = id then
            ForallTy(id, body)
        else
            ForallTy(id, tySubstTy a x body)

let rec tySubstTerm (ty : Ty) (x : string) (t : Term) =
    match t with
    | Var(id) ->
        Var(id)
    | Pair(e1, e2) ->
        Pair(tySubstTerm ty x e1, tySubstTerm ty x e2)
    | Proj1(e) ->
        Proj1(tySubstTerm ty x e)
    | Proj2(e) ->
        Proj2(tySubstTerm ty x e)
    | In1(ty1, ty2, e) ->
        In1(tySubstTy ty x ty1, tySubstTy ty x ty2, tySubstTerm ty x e)
    | In2(ty1, ty2, e) ->
        In2(tySubstTy ty x ty1, tySubstTy ty x ty2, tySubstTerm ty x e)
    | App(fn, arg) ->
        App(tySubstTerm ty x fn, tySubstTerm ty x arg)
    | Abs(id, dom, body) ->
        Abs(id, dom, tySubstTerm ty x body)
    | TyApp(forall, arg) ->
        TyApp(tySubstTerm ty x forall, arg)
    | Forall(id, body) ->
        Forall(id, tySubstTerm ty x body)
    | PrimFun(name, domTy, codTy, impl) ->
        PrimFun(name, domTy, codTy, impl)
    | PrimNatVal(n) ->
        PrimNatVal(n)
    | PrimUnitVal ->
        PrimUnitVal
    | EmptyList(elemTy) ->
        EmptyList(tySubstTy ty x elemTy)
    | Cons(t1, t2) ->
        Cons(tySubstTerm ty x t1, tySubstTerm ty x t2)
    | ListCase(scrut, nil, cons) ->
        ListCase(tySubstTerm ty x scrut, tySubstTerm ty x nil, tySubstTerm ty x cons)
    | SumCase(scrut, lCase, rCase) ->
        SumCase(tySubstTerm ty x scrut, tySubstTerm ty x lCase, tySubstTerm ty x rCase)
    | LetRec(funName, parName, domTy, codTy, body) ->
        LetRec(funName, parName, domTy, codTy, tySubstTerm ty x body)

let rec step (t : Term) : Option<Term> =
    match t with
    | Var(_) ->
        None
    | Pair(l,r) ->
        match step l with
        | Some(l') ->
            Some(Pair(l', r))
        | None ->
            match step r with
            | Some(r') ->
                Some(Pair(l, r'))
            | None ->
                None
    | Proj1(e) ->
        match step e with
        | Some(e') ->
            Some(Proj1(e'))
        | None ->
            match e with
            | Pair(e1, _) ->
                Some(e1)
            | _ ->
                None
    | Proj2(e) ->
        match step e with
        | Some(e') ->
            Some(Proj2(e'))
        | None ->
            match e with
            | Pair(_, e2) ->
                Some(e2)
            | _ ->
                None
    | In1(ty1, ty2, e) ->
        match step e with
        | Some(e') ->
            Some(In1(ty1, ty2, e'))
        | None ->
            None
    | In2(ty1, ty2, e) ->
        match step e with
        | Some(e') ->
            Some(In1(ty1, ty2, e'))
        | None ->
            None
    | App(fn, arg) ->
        match step fn with
        | Some(fn') ->
            Some(App(fn', arg))
        | None ->
            match step arg with
            | Some(arg') ->
                Some(App(fn,arg'))
            | None ->
                match fn with
                | PrimFun(name, domTy, codTy, impl) ->
                    Some(impl arg)
                | Abs(id,dom,body) ->
                    Some(subst [(id, arg)] body)
                | LetRec(funName, parName, domTy, codTy, body) ->
                    match arg with
                    | Cons(_,_)
                    | EmptyList(_) ->
                        let f = LetRec(funName,parName,domTy,codTy,body)
                        Some(subst [(funName,f);(parName,arg)] body)
                    | _ ->
                        None
                | _ ->
                    None
    | TyApp(forall, arg) ->
        match step forall with
        | Some(forall') ->
            Some(TyApp(forall', arg))
        | None ->
            match forall with
            | Forall(id, body) ->
                Some(tySubstTerm arg id body)
            | _ ->
                failwith "This program 'went wrong'. Oops."
    | PrimFun(_,_,_,_)
    | PrimNatVal(_)
    | PrimUnitVal
    | EmptyList(_) 
    | Forall(_,_)
    | Abs(_,_,_)
    | LetRec(_,_,_,_,_) ->
        None        
    | Cons(e1,e2) ->
        match step e1 with
        | Some(e1') ->
            Some(Cons(e1',e2))
        | None ->
            match step e2 with
            | Some(e2') ->
                Some(Cons(e1,e2'))
            | None ->
                None
    | ListCase(scrut, nilCase, consCase) ->
        match step scrut with
        | Some(scrut') ->
            Some(ListCase(scrut', nilCase, consCase))
        | None ->
            match scrut with
            | EmptyList(_) ->
                Some(nilCase)
            | Cons(head, tail) ->
                Some(App(App(consCase, head), tail)) 
            | _ ->
                failwith "this program 'went wrong'. oops."
    | SumCase(scrut, lCase, rCase) ->
        match step scrut with
        | Some(scrut') ->
            Some(SumCase(scrut', lCase, rCase))
        | None ->
            match scrut with
            | In1(_, _, e) ->
                Some(App(lCase,e))
            | In2(_, _, e) ->
                Some(App(rCase,e)) 
            | _ ->
                failwith "this program 'went wrong'. oops."

let rec normalize (t : Term) =
    match step t with
    | Some(t') ->
        normalize t'
    | None ->
        t

//let isBot ((t : Term) (ty : Ty) =
//    match (t, Ty) with
    
type Context = { venv : Map<string,Ty> ; tenv : Set<string> }

let rec typeCheck (ctxt : Context) (t : Term) : Check<Ty> =
    let errorMsg = "type error in term " + t.ToString() + ": "
    let w (msg : string) = withError msg noRange
    let err (msg : string) = Error [errorMsg + msg,noRange]
    match t with
    | Var(name) ->
        match ctxt.venv.TryFind(name) with
        | Some(ty) ->
            Result ty
        | None ->
            Error [("variable " + name + " not found", noRange)]
    | Pair(l, r) ->
        check {
            let! tyL = w errorMsg (typeCheck ctxt l)
            let! tyR = w errorMsg (typeCheck ctxt r)
            return Prod(tyL, tyR)
        }
    | Proj1(t) ->
        check {
            let! ty = w errorMsg (typeCheck ctxt t)
            let! tyL = 
                match ty with
                | Prod(tyL, _) ->
                    Result tyL
                | _ ->
                    err (": expected pair type, but computed " + ty.ToString())
            return tyL
        }
    | Proj2(t) ->
        check {
            let! ty = w errorMsg (typeCheck ctxt t)
            let! tyR = 
                match ty with
                | Prod(_, tyR) ->
                    Result tyR
                | _ ->
                    err (": expected pair type, but computed " + ty.ToString())
            return tyR
        }
    | In1(ty1,ty2,s) ->
        check {
            let! ty = w errorMsg (typeCheck ctxt s)
            do!
                match ty = ty1 with
                | true -> 
                    Result ()
                | false ->
                    err (": ascripted type " + ty1.ToString() + " does not match computed type " + ty.ToString())
            return Sum(ty1,ty2)
        }
    | In2(ty1, ty2, s) ->
        check {
            let! ty = w errorMsg (typeCheck ctxt s)
            do!
                match ty = ty2 with
                | true -> 
                    Result ()
                | false ->
                    err ("ascripted type " + ty2.ToString() + " does not match computed type " + ty.ToString())
            return Sum(ty1,ty2)
        }     
    | App(fn, arg) ->
        check {
            let! tyFn = w errorMsg (typeCheck ctxt fn)
            let! tyDom, tyCod =
                match tyFn with
                | Fun(dom, cod) ->
                    Result (dom, cod)
                | _ ->
                    err "expected function type in function position"
            let! tyArg = w errorMsg (typeCheck ctxt arg)
            do! 
                match tyDom = tyArg with
                | true ->
                    Result ()
                | false ->
                    err ("domain type " + tyDom.ToString() + " does not match argument type " + tyArg.ToString())
            return tyCod
        }
    | Abs(id,domTy,body) ->
        check {
            let ctxt' = { ctxt with venv = ctxt.venv.Add(id,domTy) }
            let! codTy = w errorMsg (typeCheck ctxt' body)
            return Fun(domTy, codTy)
        }
    | TyApp(forall, argTy) ->
        check {
            let! forallTy = w errorMsg (typeCheck ctxt forall)
            let! tyId,tyBody = 
                match forallTy with
                | ForallTy(id, body) ->
                    Result (id,body)
                | _ ->
                    err ("forall type expected in function position of type application, but computed " + forallTy.ToString())
            return (tySubstTy argTy tyId tyBody)
        }
    | Forall(id, body) ->
        check {
            let ctxt' = { ctxt with tenv = ctxt.tenv.Add(id) }
            let! tyBody = w errorMsg (typeCheck ctxt' body)
            return ForallTy(id, tyBody)
        }
    | PrimFun(name, domTy, codTy, impl) ->
        Result (Fun(domTy, codTy))
    | PrimNatVal(n) ->
        Result (Prim("Nat"))
    | PrimUnitVal ->
        Result (pUnitTy)
    | EmptyList(elemTy) ->
        Result (List(elemTy))
    | Cons(head, rest) ->
        check {
            let! restTy = w errorMsg (typeCheck ctxt rest)
            let! headTy = w errorMsg (typeCheck ctxt head)
            let! elemTy =
                match restTy with
                | List(elemTy) ->
                    Result(elemTy)
                | _ ->
                    err ("expected cons tail " + rest.ToString() + " to have a list type, but " + restTy.ToString() + " computed")
            do! 
                match elemTy = headTy with
                | true ->
                    Result ()
                | false ->
                    err ("List element type " + elemTy.ToString() + " does not match cons head type " + headTy.ToString())
            return restTy
        }
    | ListCase(scrut, nilCase, consCase) ->
        check {
            let! scrutTy = w errorMsg (typeCheck ctxt scrut)
            let! elemTy =
                match scrutTy with
                | List(elemTy) ->
                    Result elemTy
                | _ ->
                    err ("scrutinee expected to have list type but instead has type " + scrutTy.ToString())
            let! nilCaseTy = w errorMsg (typeCheck ctxt nilCase)
            let! consCaseTy = w errorMsg (typeCheck ctxt consCase)
            let! resTy =
                match consCaseTy with
                | Fun(headTy,Fun(tailTy,resTy)) when headTy = elemTy && tailTy = scrutTy ->
                    Result resTy
                | _ ->
                    err ("tail case expected to have type " + elemTy.ToString() + " -> " + scrutTy.ToString() + " -> " + nilCaseTy.ToString() + " but instead computed " + consCaseTy.ToString())
            return resTy
        }
    | SumCase(scrut, lCase, rCase) ->
        check {
            let! scrutTy = w errorMsg (typeCheck ctxt scrut)
            let! tyL, tyR =
                match scrutTy with
                | Sum(tyL, tyR) ->
                    Result (tyL, tyR)
                | _ ->
                    err ("scrutinee expected to have sum type but instead has type " + scrutTy.ToString())
            let! lCaseTy = w errorMsg (typeCheck ctxt lCase)
            let! rCaseTy = w errorMsg (typeCheck ctxt rCase)
            let! resTyL =
                match lCaseTy with
                | Fun(domL,resTy) when domL = tyL ->
                    Result resTy
                | _ ->
                    err ("left case expected to have type of the form " + tyL.ToString() + " -> ?, but instead computed " + lCaseTy.ToString())
            let! resTyR =
                match rCaseTy with
                | Fun(domR,resTy) when domR = tyR ->
                    Result resTy
                | _ ->
                    err ("right case expected to have type of the form " + tyR.ToString() + " -> ?, but instead computed " + rCaseTy.ToString())
            do!
                match resTyR = resTyL with
                | true ->
                    Result ()
                | false ->
                    err ("left case body type " + resTyL.ToString() + " does not match right case body type " + resTyR.ToString())
            return resTyL
        }
    | LetRec(funName, parName, domTy, codTy, body) ->
        check {
            let funTy = Fun(domTy,codTy)
            let ctxt' = { ctxt with venv = ctxt.venv.Add(funName,funTy).Add(parName,domTy) }
            let! tyBody = w errorMsg (typeCheck ctxt' body)
            do! 
                match tyBody = codTy with
                | true ->
                    Result ()
                | false ->
                    err ("Computed letrec body type " + tyBody.ToString() + " does not matched ascribed type " + codTy.ToString())
            return Fun(domTy, tyBody)
        }

let forEach (pSrcTy : Ty) (pDestTy : Ty) (pFun : Term) (pList : Term) : Term =
    let forEachFun = 
        LetRec("!f", "!l", List(pSrcTy), List(pDestTy), 
            ListCase(Var("!l"), EmptyList(pDestTy), Abs("!h", pSrcTy, Abs("!t", List(pSrcTy), 
                Cons(App(pFun, Var("!h")), App(Var("!f"), Var("!t")))))))
    App(forEachFun, pList)

let append (pElemTy : Ty) (pList1 : Term) (pList2 : Term) =
    let appendFun = Abs("!l1", List(pElemTy), LetRec("!f", "!l2", List(pElemTy), List(pElemTy),
        ListCase(Var("!l1"),
            Var("!l2"),
            Abs("!h", pElemTy, Abs("!t", List(pElemTy), Cons(Var("!h"), App(Var("!f"), Var("!t"))))))))
    App(App(appendFun, pList1), pList2)

let fold (srcTy : Ty) (destTy : Ty) (g : Term) (l : Term) (init : Term) =
    let fn =
        LetRec("!f", "!l", List(srcTy), destTy,
            ListCase(Var("!l"),
                init,
                Abs("!h", srcTy, Abs("!t", List(srcTy), 
                    App(App(g, Var("!h")), App(Var("!f"), Var("!t")))))))
    App(fn, l)
