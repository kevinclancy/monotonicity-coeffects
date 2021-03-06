﻿open System
open Microsoft.FSharp.Text.Lexing
open System.IO
open Typecheck
open Ast
open Kindcheck
open CheckComputation
open PCF

module P = PCF

let goneWrong = "This program has 'gone wrong'. Oops."

// natural numbers for upper bound (right injection is infinity, i.e. no upper bound)
let pNatUpperTy = P.Sum(P.Prim("Nat"), P.Unit)

let joinNatUpper (t : P.Term) =
    match t with
    | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(m)) ->
        let joinNatUpper' (s : P.Term) =
            match s with
            | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n)) ->
                P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(Math.Min(m,n)))
            | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
                P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(m))
            | _ ->
                failwith goneWrong
        P.Abs("n", pNatUpperTy, P.App(PrimFun("joinNatUpper'", pNatUpperTy, pNatUpperTy, joinNatUpper'), P.Var("n")))
    | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
        let joinNatUpper' (s : P.Term) =
            match s with
            | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n)) ->
                P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n))
            | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
                P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal)
            | _ ->
                failwith goneWrong
        P.Abs("n", pNatUpperTy, P.App(PrimFun("joinNatUpper'", pNatUpperTy, pNatUpperTy, joinNatUpper'), P.Var("n")))
    | _ ->
        failwith goneWrong

let primJoinNatUpper = P.PrimFun("joinNat", pNatUpperTy, P.Fun(pNatUpperTy, pNatUpperTy), joinNatUpper)

let lessNatUpper (t : P.Term) =
    match t with
    | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(m)) ->
        let lessNatUpper' (s : P.Term) =
            match s with
            | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n)) ->
                if m < n then
                    pcfTrue
                else
                    pcfFalse
            | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
                pcfTrue
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("n", pNatUpperTy, P.App(PrimFun("lessNatUpper'", pNatUpperTy, pBoolTy, lessNatUpper'), P.Var("n")))
    | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
        let lessNatUpper' (s : P.Term) =
            match s with
            | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(_))
            | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
                pcfFalse
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("n", pNatUpperTy, P.App(PrimFun("lessNatUpper'", pNatUpperTy, pBoolTy, lessNatUpper'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let primLessNatUpper = P.PrimFun("lessNatUpper", pNatUpperTy, P.Fun(pNatUpperTy, P.pBoolTy), lessNatUpper)

let isoNatUpper (t : P.Term) : P.Term =
    match t with
    | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(m)) ->
        P.Cons(P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(m)), P.EmptyList(P.Prim("NatU")))
    | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
        P.EmptyList(P.TyVar("Nat"))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let primIsoNatUpper = P.PrimFun("isoNatUpper", pNatUpperTy, P.List(pNatUpperTy), isoNatUpper)

let joinNat (t : P.Term) =
    match t with
    | P.PrimNatVal(m) ->
        let joinNat' (s : P.Term) =
            match s with
            | P.PrimNatVal(n) ->
                P.PrimNatVal(Math.Max(m,n))
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("joinNat'", P.Prim("Nat"), P.Prim("Nat"), joinNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let primJoinNat = P.PrimFun("joinNat", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), joinNat)

let lessNat (t : P.Term) =
    match t with
    | P.PrimNatVal(m) ->
        let lessNat' (s : P.Term) =
            match s with
            | P.PrimNatVal(n) ->
                if m < n then
                    pcfTrue
                else
                    pcfFalse
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("lessNat'", P.Prim("Nat"), P.Prim("Bool"), lessNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let primLessNat = P.PrimFun("lessNat", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.pBoolTy), lessNat)

let isoNat (t : P.Term) : P.Term =
    match t with
    | P.PrimNatVal(m) when m = 0 ->
        P.EmptyList(P.TyVar("Nat"))
    | P.PrimNatVal(m) ->
        P.Cons(P.PrimNatVal(m), P.EmptyList(P.Prim("Nat")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let primIsoNat = P.PrimFun("isoNat", P.Prim("Nat"), P.List(P.Prim("Nat")), isoNat)

let promNat (t : P.Term) : P.Term =
    t

let primPromNat = P.PrimFun("promNat", P.Prim("Nat"), P.Prim("Nat"), promNat)

let joinProp (t : P.Term)  =
    match t with
    | PCFBool(a) ->
        let joinBool' (s : P.Term) =
            match s with
            | PCFBool(b) ->
                makePcfBool (a || b)
        P.Abs("b", P.pPropTy, P.App(P.PrimFun("joinProp'", P.pPropTy, P.pPropTy, joinBool'), P.Var("b")))

let primJoinProp = P.PrimFun("joinProp", P.pPropTy, P.Fun(P.pPropTy, P.pPropTy), joinProp)

let lessProp (t : P.Term)  =
    match t with
    | PCFProp(a) -> //unknown
        let lessBool' (s : P.Term) : P.Term =
            match s with
            | PCFProp(b) ->
                makePcfBool (a = Unknown && b = Known)
        P.Abs("b", P.pPropTy, P.App(P.PrimFun("lessProp'", P.pPropTy, P.pPropTy, lessBool'), P.Var("b")))

let lessBool (t : P.Term)  =
    match t with
    | PCFBool(a) -> //false
        let lessBool' (s : P.Term) : P.Term =
            match s with
            | PCFBool(b) ->
                makePcfBool (a = false && b = true)
        P.Abs("b", P.pBoolTy, P.App(P.PrimFun("lessBool'", P.pBoolTy, P.pBoolTy, lessBool'), P.Var("b")))


let primLessProp = P.PrimFun("lessProp", P.pPropTy, P.Fun(P.pPropTy, P.pPropTy), lessProp)

let isoProp (t : P.Term) : P.Term =
    match t with
    | PCFBool(a) when a = true ->
        P.Cons(P.PrimUnitVal, P.EmptyList(P.Unit))
    | PCFBool(a) ->
        P.EmptyList(P.Unit)
    | _ ->
        failwith goneWrong

let primIsoProp = P.PrimFun("isoProp", pPropTy, P.List(P.Unit), isoProp)

let primLessBool = P.PrimFun("lessBool", P.pBoolTy, P.Fun(P.pBoolTy, P.pBoolTy), lessProp)


let joinUnit (t : P.Term)  =
    match t with
    | P.PrimUnitVal ->
        let joinUnit' (s : P.Term) =
            match s with
            | P.PrimUnitVal ->
                P.PrimUnitVal
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("b", P.pUnitTy, P.App(P.PrimFun("jUnit'", P.pUnitTy, P.pUnitTy, joinUnit'), P.Var("b")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let primJoinUnit = P.PrimFun("joinUnit", P.pUnitTy, P.Fun(P.pUnitTy, P.pUnitTy), joinUnit)

let lessUnit (t : P.Term)  =
    match t with
    | P.PrimUnitVal ->
        let lessUnit' (s : P.Term) =
            match s with
            | P.PrimUnitVal ->
                pcfFalse
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("b", P.pUnitTy, P.App(P.PrimFun("<'", P.pUnitTy, P.pBoolTy, lessUnit'), P.Var("b")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let primLessUnit = P.PrimFun("lessUnit", P.pUnitTy, P.Fun(P.pUnitTy, P.pBoolTy), lessUnit)

let baseTyMap =
    Map<string, Kind>(
        [("Nat", KProper(
                    P.Prim("Nat"), 
                    Some(primLessNat), 
                    Some { bot = PrimNatVal(0) ; join = primJoinNat ; tyDelta = TyId("Nat",noRange) ; iso = primIsoNat ; prom = primPromNat }, 
                    true,
                    noRange));

         ("NatU", KProper(
                    pNatUpperTy,
                    Some(primLessNatUpper),
                    Some { bot = P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ; join = primJoinNatUpper ; tyDelta = TyId("NatU", noRange) ; iso = primIsoNatUpper ; prom = P.Abs("!x", pNatUpperTy, V("!x")) },
                    true,
                    noRange));

         ("Unit", KProper(
                    P.Unit,
                    Some(primLessUnit),
                    None,
                    false,
                    noRange));

         ("Prop", KProper(
                    P.Sum(P.Unit, P.Unit),
                    Some(primLessProp),
                    Some{bot = In2(P.Unit, P.Unit, P.PrimUnitVal); join = primJoinProp ; tyDelta = TyId("Unit", noRange) ; iso = primIsoProp ; prom = P.Abs("!x", P.Sum(P.Unit, P.Unit), V("!x")) },
                    true,
                    noRange)) ;

        ("Bool", KProper(
                    P.Sum(P.Unit, P.Unit),
                    Some(primLessBool),
                    None,
                    true,
                    noRange))])


let plus (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let plus' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimNatVal(n + m)
            | _ ->
                failwith goneWrong
        P.PrimFun("plus'", P.Prim("Nat"), P.Prim("Nat"), plus')
    | _ ->
        failwith goneWrong

let primPlus = P.PrimFun("plus", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), plus)

let plusU (t1 : P.Term) : P.Term =
    match t1 with
    | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n)) ->
        let plusU' (t2 : P.Term) =
            match t2 with
            | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(m)) ->
                P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n + m))
            | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
                P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal)
            | _ ->
                failwith goneWrong
        P.PrimFun("plusU'", pNatUpperTy, pNatUpperTy, plusU')
    | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
        let plusU' (t2 : P.Term) =
            match t2 with
            | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(_)) 
            | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
                P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal)
            | _ ->
                failwith goneWrong
        P.PrimFun("plusU'", pNatUpperTy, pNatUpperTy, plusU')
    | _ ->
        failwith goneWrong

let primPlusU = P.PrimFun("plusU", pNatUpperTy, P.Fun(pNatUpperTy, pNatUpperTy), plusU)

let flip (t : P.Term) : P.Term =
    match t with
    | P.PrimNatVal(n) ->
        P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n))
    | _ ->
        failwith goneWrong

let primFlip = P.PrimFun("flip", P.Prim("Nat"), pNatUpperTy, flip)

let mult (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let mult' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimNatVal(n * m)
            | _ ->
                failwith goneWrong
        P.PrimFun("mult'", P.Prim("Nat"), P.Prim("Nat"), mult')
    | _ ->
        failwith goneWrong

let primMult = P.PrimFun("mult", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), mult)

let minus (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let minus' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimNatVal(n - m)
            | _ ->
                failwith goneWrong
        P.PrimFun("minus'", P.Prim("Nat"), P.Prim("Nat"), minus')
    | _ ->
        failwith goneWrong

let primMinus = P.PrimFun("minus", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), minus)

let bAnd (t1 : P.Term) : P.Term =
    match t1 with
    | PCFBool(a) ->
        let and' (t2 : P.Term) =
            match t2 with
            | PCFBool(b) ->
                makePcfBool (a && b)
        P.PrimFun("and'", P.pBoolTy, P.pBoolTy, and')

let primAnd = P.PrimFun("bAnd", P.pBoolTy, P.Fun(P.pBoolTy, P.pBoolTy), bAnd)

let bOr (t1 : P.Term) : P.Term =
    match t1 with
    | PCFBool(a) ->
        let or' (t2 : P.Term) =
            match t2 with
            | PCFBool(b) ->
                makePcfBool (a || b)
        P.PrimFun("or'", P.pBoolTy, P.pBoolTy, or')

let primOr = P.PrimFun("bOr", P.pBoolTy, P.Fun(P.pBoolTy, P.pBoolTy), bOr)

let bNot (t1 : P.Term) : P.Term =
    match t1 with
    | PCFBool(a) ->
        makePcfBool (not a)

let primNot = P.PrimFun("bNot", P.pBoolTy, P.pBoolTy, bNot)

let leq (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let leq' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                makePcfBool (n <= m)
            | _ ->
                failwith goneWrong
        P.PrimFun("leq'", P.Prim("Nat"), P.pBoolTy, leq')
    | _ ->
        failwith goneWrong

let primLeq = P.PrimFun("leq", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.pBoolTy), leq)


let leqU (t1 : P.Term) : P.Term =
    match t1 with
    | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n)) ->
        let leq' (t2 : P.Term) =
            match t2 with
            | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(m)) ->
                makePcfBool (n <= m)
            | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
                pcfTrue
            | _ ->
                failwith goneWrong
        P.PrimFun("leqU", P.Sum(P.Prim("Nat"), P.Unit), P.pBoolTy, leq')
    | P.In1(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
        pcfFalse 
    | _ ->
        failwith goneWrong

let primLeqU = P.PrimFun("leqU", P.Sum(P.Prim("Nat"),P.Unit), P.Fun(P.Sum(P.Prim("Nat"),P.Unit), P.pBoolTy), leqU)

let ltU (t1 : P.Term) : P.Term =
    match t1 with
    | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(n)) ->
        let leq' (t2 : P.Term) =
            match t2 with
            | P.In1(P.Prim("Nat"), P.Unit, P.PrimNatVal(m)) ->
                makePcfBool (n < m)
            | P.In2(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
                pcfTrue
            | _ ->
                failwith goneWrong
        P.PrimFun("ltU'", P.Sum(P.Prim("Nat"), P.Unit), P.pBoolTy, leq')
    | P.In1(P.Prim("Nat"), P.Unit, P.PrimUnitVal) ->
        pcfFalse 
    | _ ->
        failwith goneWrong

let primLtU = P.PrimFun("lt", P.Sum(P.Prim("Nat"),P.Unit), P.Fun(P.Sum(P.Prim("Nat"),P.Unit), P.pBoolTy), ltU)

let geq (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let geq' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                makePcfBool (n >= m)
            | _ ->
                failwith goneWrong
        P.PrimFun("geq'", P.Prim("Nat"), P.pBoolTy, geq')
    | _ ->
        failwith goneWrong

let primGeq = P.PrimFun("geq", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.pBoolTy), geq)
let primGeqU = P.PrimFun("geqU", P.Prim("NatU"), P.Fun(P.Prim("NatU"), P.pBoolTy), geq)

let gt (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let gt' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                makePcfBool (n > m)
            | _ ->
                failwith goneWrong
        P.PrimFun("gt'", P.Prim("Nat"), P.pBoolTy, gt')
    | _ ->
        failwith goneWrong

let primGt = P.PrimFun("gt", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.pBoolTy), gt)


let maxNat (t : P.Term) =
    match t with
    | P.PrimNatVal(m) ->
        let maxNat' (s : P.Term) =
            match s with
            | P.PrimNatVal(n) ->
                P.PrimNatVal(Math.Max(m,n))
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("maxNat'", P.Prim("Nat"), P.Prim("Nat"), maxNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let primMaxNat = P.PrimFun("maxNat", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), maxNat)

let minNat (t : P.Term) =
    match t with
    | P.PrimNatVal(m) ->
        let minNat' (s : P.Term) =
            match s with
            | P.PrimNatVal(n) ->
                P.PrimNatVal(Math.Min(m,n))
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("minNat'", P.Prim("Nat"), P.Prim("Nat"), minNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let primMinNat = P.PrimFun("minNat", P.Prim("Nat"), P.Fun(P.Prim("Nat"), P.Prim("Nat")), minNat)

let BoolTy = Ast.Sum(Ast.TyId("Unit",noRange), Ast.TyId("Unit", noRange), noRange)

let baseVEnv =
    Map<string, Ast.Ty * P.Term>(
        [("plus", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Nat", noRange), noRange), noRange), 
                   primPlus))
         ("mult", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Nat", noRange), noRange), noRange), 
                   primMult))
         ("minus",(FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectAntitone, TyId("Nat", noRange), noRange), noRange),
                   primMinus))
         ("bAnd", (FunTy(BoolTy, CoeffectRobust, FunTy(BoolTy, CoeffectRobust, BoolTy, noRange), noRange),
                   primAnd))
         ("bOr", (FunTy(BoolTy, CoeffectRobust, FunTy(BoolTy, CoeffectRobust, BoolTy, noRange), noRange),
                  primOr))
         ("bNot", (FunTy(BoolTy, CoeffectRobust, BoolTy, noRange),
                   primNot))
         ("pAnd", (FunTy(TyId("Prop",noRange), CoeffectMonotone, FunTy(TyId("Prop",noRange), CoeffectMonotone, TyId("Prop", noRange), noRange), noRange),
                   primAnd))
         ("pOr", (FunTy(TyId("Prop",noRange), CoeffectMonotone, FunTy(TyId("Prop",noRange), CoeffectMonotone, TyId("Prop", noRange), noRange), noRange),
                  primOr))
         ("pNot", (FunTy(TyId("Prop",noRange), CoeffectAntitone, TyId("Prop",noRange), noRange),
                   primNot))
         ("leq", (FunTy(TyId("Nat",noRange), CoeffectAntitone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Prop", noRange), noRange), noRange),
                  primLeq))
         ("geq", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectAntitone, TyId("Prop", noRange), noRange), noRange),
                  primGeq))
         ("gt", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectAntitone, TyId("Prop", noRange), noRange), noRange),
                  primGt))
         ("max", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Nat", noRange), noRange), noRange), 
                   primMaxNat))
         ("min", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Nat", noRange), noRange), noRange), 
                   primMinNat))
         ("flip", (FunTy(TyId("Nat",noRange), CoeffectAntitone, TyId("NatU", noRange), noRange), primFlip))
         ("plusU", (FunTy(TyId("NatU",noRange), CoeffectMonotone, FunTy(TyId("NatU",noRange), CoeffectMonotone, TyId("NatU", noRange), noRange), noRange), 
                   primPlusU))
         ("ltU", (FunTy(TyId("NatU",noRange), CoeffectMonotone, FunTy(TyId("NatU",noRange), CoeffectAntitone, TyId("Prop", noRange), noRange), noRange),
                  primLtU))
         ("leqU", (FunTy(TyId("NatU",noRange), CoeffectMonotone, FunTy(TyId("NatU",noRange), CoeffectAntitone, TyId("Prop", noRange), noRange), noRange),
                  primLeqU))
         //("eq", (FunTy(TyId("Nat",noRange), CoeffectAny, FunTy(TyId("Nat",noRange), CoeffectAny, TyId("Bool", noRange), noRange), noRange))
        // TODO: we need primitive unit values in syntax
         ("unit", (TyId("Unit", noRange),
                  P.PrimUnitVal))] 
    )

let tenv = { tyVarEnv = Map.empty ; tyBaseEnv = baseTyMap; tyAliasEnv = Map.empty }
let ctxt = { tenv = tenv ; venv = Map.empty ; bvenv = baseVEnv ; src = ""}

let help = """
The McLambda repl provides the following commands:
help                      --  Display this text
showContext               --  Show typing context
checkSemilat *type*       --  Checks that the provided type is a semilattice type and prints its delta type
checkToset *type*         --  Checks that the provided type is a toset type
checkPoset *type*         --  Checks that the provided type is a poset type
typeCheck *expr           --  Typechecks the provided expression, printing its type and coeffect
exit                      --  Shuts down the repl"""

let rec printStack (stack : List<string*Range>) =
    match stack with
    | (error, rng) :: rest when rng = noRange ->
        printfn "%s" error
        printStack rest
    | (error,(startPos,_)) ::  rest ->
        let location = "line: " + (startPos.Line + 1).ToString() + " column: " + startPos.Column.ToString()
        printfn ("%s\n  %s\n") location error
        printStack rest
    | [] ->
        ()

let printVenv (ctxt : Typecheck.Context) : Unit =
    let printVenvEntry (k : string, v : Ast.Ty) : string =
        k + " : " + v.ToString() 
    printfn "%s\n" (String.concat "\n" (List.map printVenvEntry (Map.toList ctxt.venv)))    

let rec repl (ctxt : Typecheck.Context) =
    printf "> "
    let commandStr = Console.In.ReadLine()
    match commandStr with
    | "exit" ->
        ()
    | "help" ->
        printfn "%s" help
        repl ctxt
    | "showContext" ->
        printVenv ctxt
        repl ctxt
    | _ ->
        let firstSpace = commandStr.IndexOf(' ')
        match firstSpace with
        | -1 ->
            printfn "%s is not a valid command. Type 'help' for a list of valid commands." commandStr
        | n ->
            let commandName = commandStr.Substring(0, firstSpace)
            let param = commandStr.Substring(firstSpace)
            match commandName with
            | "checkSemilat" ->
                let reader = new StringReader(param)
                let lexbuffer : LexBuffer<char> = LexBuffer.FromString(reader.ReadToEnd()) 
                try 
                    let ty = Parser.Ty(Lexer.token) lexbuffer
                    match kCheckSemilattice ctxt.tenv ty with
                    | Result(_,_,_,ty0,_,_) ->
                        printfn "Semilattice formation check succeeded:\n%s is a semilattice type with delta type %s"
                                param
                                (ty0.ToString())
                    | Error(stack) ->
                        printStack stack
                with
                | e ->
                    let message = e.Message
                    printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) (lexbuffer.StartPos.Column)
            | "checkPoset" ->
                let reader = new StringReader(param)
                let lexbuffer : LexBuffer<char> = LexBuffer.FromString(reader.ReadToEnd()) 
                try 
                    let ty = Parser.Ty(Lexer.token) lexbuffer
                    match kCheckProset ctxt.tenv ty with
                    | Result(_) ->
                        printfn "Poset formation check succeeded:\n%s is a poset type"
                                param
                    | Error(stack) ->
                        printStack stack
                with
                | e ->
                    let message = e.Message
                    printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) (lexbuffer.StartPos.Column)
            | "checkToset" ->
                let reader = new StringReader(param)
                let lexbuffer : LexBuffer<char> = LexBuffer.FromString(reader.ReadToEnd()) 
                try 
                    let ty = Parser.Ty(Lexer.token) lexbuffer
                    match kCheckToset ctxt.tenv ty with
                    | Result(_,_) ->
                        printfn "Toset formation check succeeded:\n%s is a toset type"
                                param
                    | Error(stack) ->
                        printStack stack
                with
                | e ->
                    let message = e.Message
                    printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) (lexbuffer.StartPos.Column)
            | "typeCheck" ->
                let reader = new StringReader(param)
                let lexbuffer : LexBuffer<char> = LexBuffer.FromString(reader.ReadToEnd())
                try
                    let expr = Parser.ExprList (Lexer.token) lexbuffer
                    match Typecheck.typeCheck ctxt expr with
                    | Result(ty,coeffect,_) ->
                        let coeffectEntryStr (k : string, v : Coeffect) =
                            k + " ==> " + v.ToString() 
                        printfn "Computed type: %s\n%s"
                                (ty.ToString())
                                (String.concat "\n" (List.map coeffectEntryStr (Map.toList coeffect)))
                    | Error(stack) ->
                        printStack stack
                with
                | e ->
                    let message = e.Message
                    printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) (lexbuffer.StartPos.Column)
            | unknownCommandName ->
               printfn "Command name '%s' unknown" unknownCommandName
        repl ctxt
[<EntryPoint>]
let main argv =
    try 
        let reader = new StreamReader(argv.[0])
        let lexbuffer : LexBuffer<char> = LexBuffer.FromString(reader.ReadToEnd())
        let src = (new StreamReader(argv.[0])).ReadToEnd()
        let prog = 
          try 
            Parser.start(Lexer.token) lexbuffer
          with
          | e ->
            let message = e.Message
            printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) (lexbuffer.StartPos.Column * 2)
            exit 1
        
        match progCheck {ctxt with src = src} prog with
        | CheckResult(Error(stack)) ->
            printStack stack
        | CheckResult(Result(ty,R,pTerm,tenv)) ->
            let result = normalize pTerm
            let resultStr = toMC tenv.tyAliasEnv result ty (Some(ty.ToString()))
            printf "Successfully checked program.\nType: %s\nValue: %s\n" (ty.ToString()) resultStr
        | FoundHole(ctxt, (startPos, _)) ->
            printfn "found hole at Line: %d, Column: %d ...\n" (startPos.Line + 1) (startPos.Column * 2)
            printVenv ctxt
            printfn "Type 'help' to show recognized commands\n"
            repl ctxt
        0 // return an integer exit code
    with 
    | :? IndexOutOfRangeException ->
        printfn "provide the name of a text file as the command line argument"
        1
    | :? FileNotFoundException ->
        printfn "file not found"
        1