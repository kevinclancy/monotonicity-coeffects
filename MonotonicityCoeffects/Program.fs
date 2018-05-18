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
                P.PrimNatVal(Math.Max(m,n))
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("n", P.Prim("Nat"), P.App(PrimFun("lessNat'", joinNat'), P.Var("n")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."    

let joinBool (t : P.Term)  =
    match t with
    | P.PrimBoolVal(a) ->
        let lessNat' (s : P.Term) =
            match s with
            | P.PrimBoolVal(b) ->
                P.PrimBoolVal(a || b)
            | _ ->
                failwith "This program has 'gone wrong'. Oops."

        P.Abs("b", P.Prim("Bool"), P.App(P.PrimFun("joinBool'", lessNat'), P.Var("b")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

let lessBool (t : P.Term)  =
    match t with
    | P.PrimBoolVal(a) ->
        let lessBool' (s : P.Term) =
            match s with
            | P.PrimBoolVal(b) ->
                P.PrimBoolVal(a = false && b = true)
            | _ ->
                failwith "This program has 'gone wrong'. Oops."
        P.Abs("b", P.Prim("Bool"), P.App(P.PrimFun("lessBool'", lessBool'), P.Var("b")))
    | _ ->
        failwith "this program has 'gone wrong'. oops."

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
                P.PrimBoolVal(false)
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
                    P.Prim("Unit"),
                    Some(PrimFun("lessUnit", lessUnit)),
                    Some{bot = PrimUnitVal ; join = PrimFun("joinUnit", joinUnit)},
                    noRange));

         ("Bool", KProper(
                    P.Prim("Bool"),
                    Some(PrimFun("lessBool", lessBool)),
                    Some{bot = PrimUnitVal ; join = PrimFun("joinBool", joinBool)},
                    noRange))])

let baseVEnv =
    Map<string, Ast.Ty>(
        [("unit", TyId("Unit", noRange))]
    )

let tenv = { tyVarEnv = Map.empty ; tyBaseEnv = baseTyMap; tyAliasEnv = Map.empty }
let ctxt = { tenv = tenv ; venv = baseVEnv}

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
            printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) lexbuffer.StartPos.Column
            exit 1
        
        match progCheck ctxt ty with
        | Error(stack) ->
            printStack stack
        | Result(ty,R) ->
            printf "Successfully type-and-coeffect-checked program as: %s\n%s\n" (ty.ToString()) (R.ToString())
        0 // return an integer exit code
    with 
    | :? IndexOutOfRangeException ->
        printfn "provide the name of a text file as the command line argument"
        1
    | :? FileNotFoundException ->
        printfn "file not found"
        1