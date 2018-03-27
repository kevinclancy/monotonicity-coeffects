// Learn more about F# at http://fsharp.org

open System
open Lexer
open Microsoft.FSharp.Text.Lexing
open Tokens


[<EntryPoint>]
let main argv =
    let prog = "while begin x ( y )"
    let buf = LexBuffer<_>.FromChars(prog.ToCharArray()) 
    
    printfn "Hello World from F#!"
    0 // return an integer exit code
