// Learn more about F# at http://fsharp.org

open System
open Lexer
open Microsoft.FSharp.Text.Lexing
open Microsoft.FSharp.Text.Parsing
open Microsoft.FSharp.Text.Parsing.ParseHelpers
open System.IO
open Parser
open Typecheck
open Ast
open System
open Kindcheck
open CheckComputation
open PCF

module P = PCF

let goneWrong = "This program has 'gone wrong'. Oops."

let joinNat (t : P.Term) =
    match t with
    | P.PrimNatVal(m) ->
        let joinNat' (s : P.Term) =
            match s with
            | P.PrimNatVal(n) ->
                P.PrimNatVal(Math.Max(m,n))
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("joinNat'", joinNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let lessNat (t : P.Term) =
    match t with
    | P.PrimNatVal(m) ->
        let joinNat' (s : P.Term) =
            match s with
            | P.PrimNatVal(n) ->
                if m < n then
                    pcfTrue
                else
                    pcfFalse
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("lessNat'", joinNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let joinBool (t : P.Term)  =
    match t with
    | PCFBool(a) ->
        let lessNat' (s : P.Term) =
            match s with
            | PCFBool(b) ->
                makePcfBool (a || b)
        P.Abs("b", P.Prim("Bool"), P.App(P.PrimFun("joinBool'", lessNat'), P.Var("b")))

let lessBool (t : P.Term)  =
    match t with
    | PCFBool(a) -> //false
        let lessBool' (s : P.Term) : P.Term =
            match s with
            | PCFBool(b) ->
                makePcfBool (a = false && b = true)
        P.Abs("b", P.Prim("Bool"), P.App(P.PrimFun("lessBool'", lessBool'), P.Var("b")))

let joinUnit (t : P.Term)  =
    match t with
    | P.PrimUnitVal ->
        let joinUnit' (s : P.Term) =
            match s with
            | P.PrimUnitVal ->
                P.PrimUnitVal
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("b", P.Prim("Unit"), P.App(P.PrimFun("jUnit'", joinUnit'), P.Var("b")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let lessUnit (t : P.Term)  =
    match t with
    | P.PrimUnitVal ->
        let lessUnit' (s : P.Term) =
            match s with
            | P.PrimUnitVal ->
                pcfFalse
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("b", P.Prim("Unit"), P.App(P.PrimFun("<'", lessUnit'), P.Var("b")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let baseTyMap =
    Map<string, Kind>(
        [("Nat", KProper(
                    P.Prim("Nat"), 
                    Some(PrimFun("lessNat", lessNat)), 
                    Some { bot = PrimNatVal(0) ; join = PrimFun("joinNat", joinNat) }, 
                    noRange));

         ("Unit", KProper(
                    P.Unit,
                    Some(PrimFun("lessUnit", lessUnit)),
                    Some{bot = PrimUnitVal ; join = PrimFun("joinUnit", joinUnit)},
                    noRange));

         ("Bool", KProper(
                    P.Sum(P.Unit, P.Unit),
                    Some(PrimFun("lessBool", lessBool)),
                    Some{bot = P.In1(P.PrimUnitVal) ; join = PrimFun("joinBool", joinBool)},
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
        P.PrimFun("plus'", plus')
    | _ ->
        failwith goneWrong

let mult (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let mult' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimNatVal(n * m)
            | _ ->
                failwith goneWrong
        P.PrimFun("mult'", mult')
    | _ ->
        failwith goneWrong

let minus (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let minus' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimNatVal(n - m)
            | _ ->
                failwith goneWrong
        P.PrimFun("minus'", minus')
    | _ ->
        failwith goneWrong

let bAnd (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimBoolVal(a) ->
        let and' (t2 : P.Term) =
            match t2 with
            | P.PrimBoolVal(b) ->
                P.PrimBoolVal(a && b)
            | _ ->
                failwith goneWrong
        P.PrimFun("and'", and')
    | _ ->
        failwith goneWrong
  
let bOr (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimBoolVal(a) ->
        let or' (t2 : P.Term) =
            match t2 with
            | P.PrimBoolVal(b) ->
                P.PrimBoolVal(a || b)
            | _ ->
                failwith goneWrong
        P.PrimFun("or'", or')
    | _ ->
        failwith goneWrong

let bNot (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimBoolVal(a) ->
        P.PrimBoolVal(not a)
    | _ ->
        failwith goneWrong

let leq (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let leq' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimBoolVal(n <= m)
            | _ ->
                failwith goneWrong
        P.PrimFun("leq'", leq')
    | _ ->
        failwith goneWrong

let geq (t1 : P.Term) : P.Term =
    match t1 with
    | P.PrimNatVal(n) ->
        let geq' (t2 : P.Term) =
            match t2 with
            | P.PrimNatVal(m) ->
                P.PrimBoolVal(n >= m)
            | _ ->
                failwith goneWrong
        P.PrimFun("geq'", geq')
    | _ ->
        failwith goneWrong

let baseVEnv =
    Map<string, Ast.Ty * P.Term>(
        [("plus", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Nat", noRange), noRange), noRange), 
                   P.PrimFun("plus", plus)))
         ("mult", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Nat", noRange), noRange), noRange), 
                   P.PrimFun("mult", mult)))
         ("minus",(FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectAntitone, TyId("Nat", noRange), noRange), noRange),
                   P.PrimFun("minus",minus)))
         ("bAnd", (FunTy(TyId("Bool",noRange), CoeffectMonotone, FunTy(TyId("Bool",noRange), CoeffectMonotone, TyId("Bool", noRange), noRange), noRange),
                   P.PrimFun("bAnd",bAnd)))
         ("bOr", (FunTy(TyId("Bool",noRange), CoeffectMonotone, FunTy(TyId("Bool",noRange), CoeffectMonotone, TyId("Bool", noRange), noRange), noRange),
                  P.PrimFun("bOr",bOr)))
         ("bNot", (FunTy(TyId("Bool",noRange), CoeffectAntitone, TyId("Bool",noRange), noRange),
                   P.PrimFun("bNot", bNot)))
         ("leq", (FunTy(TyId("Nat",noRange), CoeffectAntitone, FunTy(TyId("Nat",noRange), CoeffectMonotone, TyId("Bool", noRange), noRange), noRange),
                  P.PrimFun("leq", leq)))
         ("geq", (FunTy(TyId("Nat",noRange), CoeffectMonotone, FunTy(TyId("Nat",noRange), CoeffectAntitone, TyId("Bool", noRange), noRange), noRange),
                  P.PrimFun("geq", geq)))
         //("eq", (FunTy(TyId("Nat",noRange), CoeffectAny, FunTy(TyId("Nat",noRange), CoeffectAny, TyId("Bool", noRange), noRange), noRange))
        // TODO: we need primitive unit values in syntax
         ("unit", (TyId("Unit", noRange),
                  P.PrimUnitVal))] 
        
    )

let tenv = { tyVarEnv = Map.empty ; tyBaseEnv = baseTyMap; tyAliasEnv = Map.empty }
let ctxt = { tenv = tenv ; venv = Map.empty ; bvenv = baseVEnv}

let rec printStack (stack : List<string*Range>) =
    match stack with
    | (error,(startPos,_)) ::  rest ->
        let location = "line: " + startPos.Line.ToString() + " column: " + startPos.Column.ToString() 
        printfn ("%s\n  %s\n") location error
        printStack rest
    | [] ->
        ()

[<EntryPoint>]
let main argv =
    try 
        let reader = new StreamReader(argv.[0])
        let lexbuffer : LexBuffer<char> = LexBuffer.FromString(reader.ReadToEnd())
        let ty = 
          try 
            Parser.start(Lexer.token) lexbuffer
          with
          | e ->
            let message = e.Message
            printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) lexbuffer.StartPos.Column
            exit 1
        
        match progCheck ctxt ty with
        | Error(stack) ->
            printStack stack
        | Result(ty,R,pTerm) ->
            let mapCoeffectEntry (id : string) (q: Coeffect) =
                q.ToString() + " " + id
            let stringEntriesR = (Map.toList (Map.map mapCoeffectEntry R))
            let stringR = String.concat ", " (List.map (fun (_,v) -> v) stringEntriesR)
            let result = normalize pTerm
            printf "Successfully checked program.\nType: %s\nCoeffect: %s" (ty.ToString()) stringR
        0 // return an integer exit code
    with 
    | :? IndexOutOfRangeException ->
        printfn "provide the name of a text file as the command line argument"
        1
    | :? FileNotFoundException ->
        printfn "file not found"
        1