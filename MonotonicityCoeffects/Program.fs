﻿// Learn more about F# at http://fsharp.org

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

let baseTyMap = 
    Map<string, Kind>(
        [("Nat", KProper(Set [Semilattice; Toset; Proset], noRange)); 
         ("MinNat", KProper(Set [Semilattice; Toset; Proset], noRange)); 
         ("Unit", KProper(Set [Semilattice; Toset; Proset], noRange));
         ("Bool", KProper(Set [Semilattice; Toset; Proset], noRange))])

let tyVarEnv = Map.empty
let tenv = { tyVarEnv = tyVarEnv ; tyBaseEnv = baseTyMap }

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
            Parser.Ty(Lexer.token) lexbuffer
          with
          | e ->
            printfn "Parse error. Line: %d, Column: %d" (lexbuffer.StartPos.Line + 1) lexbuffer.StartPos.Column
            exit 1

        match Kindcheck.kCheckSemilattice tenv ty with
        | Some(stack) ->
            printStack stack
        | None ->
            printf "success!"

        printfn "Hello World from F#!"
        0 // return an integer exit code
    with 
    | :? IndexOutOfRangeException ->
        printfn "provide the name of a text file as the command line argument"
        1
    | :? FileNotFoundException ->
        printfn "file not found"
        1