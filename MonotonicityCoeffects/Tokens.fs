module Tokens

open System.Linq
open System

type Token = 
    | TRUE
    | FALSE
    | FUN
    | COLON
    | EQUAL
    | BOT
    | JOIN
    | EXTRACT
    | CONS
    | IGET
    | ISET
    | FST
    | SND
    | OF
    | CASE
    | COMMA
    | INL
    | INR
    | TO
    | CAP
    | UNCAP
    | AT
    | PLUS
    | MINUS
    | QUESTION
    | ASTERISK
    | DOT
    | LPAREN
    | RPAREN
    | IN
    | LET
    | END
    | ID of string
    | CONST of string
    | INT of int
    | FLOAT of float
    | EOF
