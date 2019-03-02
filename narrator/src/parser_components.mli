open MParser

type 'a stateless_p = ('a, unit) parser

val ignore_space : 'a stateless_p -> 'a stateless_p

val ident_p : string stateless_p
