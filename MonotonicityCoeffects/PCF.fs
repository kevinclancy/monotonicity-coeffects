module PCF

open System.Threading.Tasks.Dataflow
open System.Runtime.InteropServices.ComTypes
open System.Reflection.Metadata
open System

type Ty = 
    | BB // discrete boolean
    | List of elemTy : Ty 
    | Pair of lTy : Ty * rTy : Ty
    | Fun of dom : Ty * cod : Ty
    | Prim of name : string // semilattice primitives: unit, bool, nat

type Term =
    | Var of name : string
    | Pair of l : Term * r : Term
    | Proj1 of Term
    | Proj2 of Term
    | App of fn : Term * arg : Term
    | Abs of id : string * dom : Ty * body : Term
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

let lessThan (t : Term)  =
    match t with
    | PrimNatVal(m) ->
        let lessThan' (s : Term) =
            match s with
            | PrimNatVal(n) ->
                if m < n then
                    PrimBoolVal(true)
                else    
                    PrimBoolVal(false)
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        Abs("n", Prim("Nat"), App(PrimFun("<'", lessThan'), Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

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
    | App(fn, arg) ->
        App(subst s x fn, subst s x arg)
    | Abs(id, dom, body) ->
        if x = id then
            Abs(id, dom, body)
        else
            Abs(id, dom, subst s x body)
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

let rec step (t : Term) : Option<Term> =
    match t with
    | Var("x") ->
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
                | Abs(id,dom,body) ->
                    Some(subst arg id body)
                | _ ->
                    None
    | PrimFun(_, _)
    | PrimNatVal(_)
    | PrimBoolVal(_)
    | PrimUnitVal
    | EmptyList 
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