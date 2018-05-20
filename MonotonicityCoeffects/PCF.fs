module PCF

open System.Threading.Tasks.Dataflow
open System.Runtime.InteropServices.ComTypes
open System.Reflection.Metadata
open System

type Ty =
    | Unit
    | BB // discrete boolean
    | List of elemTy : Ty 
    | Prod of lTy : Ty * rTy : Ty
    | Sum of lTy : Ty * rTy : Ty
    | Fun of dom : Ty * cod : Ty
    | Prim of name : string // semilattice primitives: unit, bool, nat
    | TyVar of name : string
    | ForallTy of id : string * body : Ty

type Term =
    | Var of name : string
    | Pair of l : Term * r : Term
    | Proj1 of Term
    | Proj2 of Term
    | In1 of Term
    | In2 of Term
    | App of fn : Term * arg : Term
    | Abs of id : string * dom : Ty * body : Term
    | TyApp of forall : Term * arg : Ty
    | Forall of id : string * body : Term
    | PrimFun of name : string * impl : (Term -> Term)
    | PrimNatVal of int
    | PrimBoolVal of bool 
    | PrimUnitVal
    | EmptyList
    | Cons of head : Term * rest : Term
    | BBTrue
    | BBFalse
    | BoolCase of scrutinee : Term * trueCase : Term * falseCase : Term
    | ListCase of scrutinee : Term * nilCase : Term * consCase : Term
    | SumCase of scrutinee : Term * leftCase : Term * rightCase : Term
    | LetRec of funName : string * parName : string * domTy : Ty  * codTy : Ty * body : Term

/// s - the term to substitute
/// x - the variable to substitute with s
/// t - the term to substitute s into
let rec subst (s : Term) (x : string) (t : Term) =
    match t with
    | Var(id) ->
        if id = x then
            s
        else
            Var(id)
    | Pair(e1, e2) ->
        Pair(subst s x e1, subst s x e2)
    | Proj1(e) ->
        Proj1(subst s x e)
    | Proj2(e) ->
        Proj2(subst s x e)
    | In1(e) ->
        In1(subst s x e)
    | In2(e) ->
        In2(subst s x e)
    | App(fn, arg) ->
        App(subst s x fn, subst s x arg)
    | Abs(id, dom, body) ->
        if x = id then
            Abs(id, dom, body)
        else
            Abs(id, dom, subst s x body)
    | TyApp(forall, arg) ->
        TyApp(subst s x forall, arg)
    | Forall(id, body) ->
        Forall(id, subst s x body)
    | PrimFun(name, impl) ->
        PrimFun(name, impl)
    | PrimNatVal(n) ->
        PrimNatVal(n)
    | PrimBoolVal(b) ->
        PrimBoolVal(b)
    | PrimUnitVal ->
        PrimUnitVal
    | EmptyList ->
        EmptyList
    | Cons(t1, t2) ->
        Cons(subst s x t1, subst s x t2)
    | BBTrue ->
        BBTrue
    | BBFalse ->
        BBFalse
    | BoolCase(scrut, t, f) ->
        BoolCase(subst s x scrut, subst s x t, subst s x f)
    | ListCase(scrut, nil, cons) ->
        ListCase(subst s x scrut, subst s x nil, subst s x cons)
    | SumCase(scrut, lCase, rCase) ->
        SumCase(subst s x scrut, subst s x lCase, subst s x rCase)
    | LetRec(funName, parName, domTy, codTy, body) ->
        if parName = x then
            LetRec(funName, parName, domTy, codTy, body)
        else
            LetRec(funName, parName, domTy, codTy, subst s x body)

let rec tySubstTy (a : Ty) (x : string) (b : Ty) =
    match b with
    | Unit ->
        Unit
    | BB -> 
        BB
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
    | In1(e) ->
        In1(tySubstTerm ty x e)
    | In2(e) ->
        In2(tySubstTerm ty x e)
    | App(fn, arg) ->
        App(tySubstTerm ty x fn, tySubstTerm ty x arg)
    | Abs(id, dom, body) ->
        Abs(id, dom, tySubstTerm ty x body)
    | TyApp(forall, arg) ->
        TyApp(tySubstTerm ty x forall, arg)
    | Forall(id, body) ->
        Forall(id, tySubstTerm ty x body)
    | PrimFun(name, impl) ->
        PrimFun(name, impl)
    | PrimNatVal(n) ->
        PrimNatVal(n)
    | PrimBoolVal(b) ->
        PrimBoolVal(b)
    | PrimUnitVal ->
        PrimUnitVal
    | EmptyList ->
        EmptyList
    | Cons(t1, t2) ->
        Cons(tySubstTerm ty x t1, tySubstTerm ty x t2)
    | BBTrue ->
        BBTrue
    | BBFalse ->
        BBFalse
    | BoolCase(scrut, t, f) ->
        BoolCase(tySubstTerm ty x scrut, tySubstTerm ty x t, tySubstTerm ty x f)
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
    | In1(e) ->
        match step e with
        | Some(e') ->
            Some(In1(e'))
        | None ->
            None
    | In2(e) ->
        match step e with
        | Some(e') ->
            Some(In1(e'))
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
                | PrimFun(name, impl) ->
                    Some(impl arg)
                | Abs(id,dom,body) ->
                    Some(subst arg id body)
                | LetRec(funName, parName, domTy, codTy, body) ->
                    match arg with
                    | Cons(_,_)
                    | EmptyList ->
                        let f = LetRec(funName,parName,domTy,codTy,body)
                        Some(subst f funName (subst arg parName body))
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
    | PrimFun(_, _)
    | PrimNatVal(_)
    | PrimBoolVal(_)
    | PrimUnitVal
    | EmptyList 
    | Forall(_,_)
    | Abs(_,_,_)
    | LetRec(_,_,_,_,_) 
    | BBTrue 
    | BBFalse ->
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
    | BoolCase(scrut, tcase, fcase) ->
        match step scrut with
        | Some(scrut') ->
            Some(BoolCase(scrut', tcase, fcase))
        | None ->
            match scrut with
            | BBTrue ->
                Some(tcase)
            | BBFalse ->
                Some(fcase)
            | _ ->
                failwith "this program 'went wrong'. oops."
    | ListCase(scrut, nilCase, consCase) ->
        match step scrut with
        | Some(scrut') ->
            Some(ListCase(scrut', nilCase, consCase))
        | None ->
            match scrut with
            | EmptyList ->
                Some(nilCase)
            | Cons(head, tail) ->
                Some(App(App(consCase, head), tail)) 
            | _ ->
                failwith "this program 'went wrong'. oops."
    | SumCase(scrut, lCase, rCase) ->
        match step scrut with
        | Some(scrut') ->
            Some(ListCase(scrut', lCase, rCase))
        | None ->
            match scrut with
            | In1(e) ->
                Some(App(lCase,e))
            | In2(e) ->
                Some(App(rCase,e)) 
            | _ ->
                failwith "this program 'went wrong'. oops."
