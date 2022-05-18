(*    
    Copyright (C) 2022 Raven Beutner

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.
*)

module LTL 

open System
open System.IO
open FParsec

open Util

/// Type of an LTL formula with atoms of type 'T
type LTL<'T when 'T: comparison> = 
    | Atom of 'T
    | True
    | False 
    | And of LTL<'T> * LTL<'T>
    | Or of LTL<'T> * LTL<'T>
    | Implies of LTL<'T> * LTL<'T>
    | Equiv of LTL<'T> * LTL<'T>
    | Xor of LTL<'T> * LTL<'T>
    | Not of LTL<'T>
    | X of LTL<'T>
    | F of LTL<'T>
    | G of LTL<'T>
    | U of LTL<'T> * LTL<'T>
    | W of LTL<'T> * LTL<'T>
    | M of LTL<'T> * LTL<'T>
    | R of LTL<'T> * LTL<'T>

   /// Print this LTl formula as a string as supported by spot
    member this.Print (varNames : 'T -> String) =
        match this with
            | Atom x -> "\"" + varNames x + "\""
            | True -> "1"
            | False -> "0"
            | And(e1, e2) -> "(" + e1.Print varNames + " & " + e2.Print varNames + ")"
            | Or(e1, e2) -> "(" + e1.Print varNames + " | " + e2.Print varNames + ")"
            | Implies(e1, e2) -> "(" + e1.Print varNames + " -> " + e2.Print varNames + ")"
            | Equiv(e1, e2) -> "(" + e1.Print varNames + " <-> " + e2.Print varNames + ")"
            | Xor(e1, e2) -> "(" + e1.Print varNames + " xor " + e2.Print varNames + ")"
            | Not e -> "(! " + e.Print varNames + ")"
            | X e -> "(X " + e.Print varNames + ")"
            | F e -> "(F " + e.Print varNames + ")"
            | G e -> "(G " + e.Print varNames + ")"
            | U(e1, e2) -> "(" + e1.Print varNames + " U " + e2.Print varNames + ")"
            | W(e1, e2) -> "(" + e1.Print varNames + " W " + e2.Print varNames + ")"
            | M(e1, e2) -> "(" + e1.Print varNames + " M " + e2.Print varNames + ")"
            | R(e1, e2) -> "(" + e1.Print varNames + " R " + e2.Print varNames + ")"

    /// Map a function over this formula
    member this.Map (f : 'T -> 'U) = 
        match this with 
            | Atom x -> Atom (f x)
            | True -> True 
            | False -> False 
            | And(e1, e2) -> And(e1.Map f, e2.Map f)
            | Implies(e1, e2) -> Implies(e1.Map f, e2.Map f)
            | Equiv(e1, e2) -> Equiv(e1.Map f, e2.Map f)
            | Xor(e1, e2) -> Xor(e1.Map f, e2.Map f)
            | Or(e1, e2) -> Or(e1.Map f, e2.Map f)
            | U(e1, e2) -> U(e1.Map f, e2.Map f)
            | W(e1, e2) -> W(e1.Map f, e2.Map f)
            | M(e1, e2) -> M(e1.Map f, e2.Map f)
            | R(e1, e2) -> R(e1.Map f, e2.Map f)
            | F e -> F(e.Map f)
            | G e -> G(e.Map f)
            | X e -> X(e.Map f)
            | Not e -> Not(e.Map f)

    /// Compute all atoms in this formula
    member this.AllAtoms = 
        match this with 
            | Atom x -> Set.singleton x
            | True | False -> Set.empty 
            | And(e1, e2) | Implies(e1, e2) | Equiv(e1, e2) | Xor(e1, e2) | Or(e1, e2) | U(e1, e2) | W(e1, e2) | M(e1, e2) | R(e1, e2) -> Set.union e1.AllAtoms e2.AllAtoms
            | F e | G e | X e | Not e -> e.AllAtoms

/// A simple HyperLTL formula consits of the LTL matrix and the qunetifier prefix
type HyperLTL<'T when 'T: comparison> = 
    {
        QuantifierPrefix : list<TraceQuantifierType>
        LTLMatrix : LTL<'T * int>
    }

// A Block HyperLTL formula is a more succinct representation that groups together multiple consecutive quantifiers of the same type.
// We assume that it always starts with a universal quantifier and the list gives the number of trace quantifier in each block of identical quantifier type
type BlockHyperLTL<'T when 'T: comparison> = 
    {
        QuantifierPrefix : list<int>
        LTLMatrix : LTL<'T * int>
    } 

/// Given the quantifier prefix of a "normal" HyperLTL formula, extract the prefix in the more succinct block format
let extractBlocks (qf : list<TraceQuantifierType>) = 

    let rec helper t count q = 
        match q with 
            | [] -> [count]
            | x::xs -> 
                if x = t then 
                    helper t (count + 1) xs
                else 
                    count::helper x 1 xs

    helper qf.[0] 0 qf


module Parser =
    let private ltlParser (atomParser : Parser<'T, unit>) = 
        let ltlParser, ltlParserRef = createParserForwardedToRef()

        let trueParser = 
            stringReturn "1" True

        let falseParser = 
            stringReturn "0" False 

        let variableParser = 
            atomParser
            |>> Atom

        let parParser = 
            skipChar '(' >>. spaces >>. ltlParser .>> spaces .>> skipChar ')'

        let andParser = 
            skipString "(and" >>. spaces >>. 
                many1 (ltlParser .>> spaces)
            .>> spaces .>> skipChar ')'
            |>> fun x -> 
                List.reduce (fun x y -> And(x, y)) x

        let basicParser = 
            spaces >>. choice [ 
                trueParser
                falseParser
                variableParser
                andParser
                parParser
            ] .>> spaces

        let oppLtl = new OperatorPrecedenceParser<LTL<'T>, unit, unit>()

        let addInfixOperator string precedence associativity f =
            oppLtl.AddOperator(
                InfixOperator(string, spaces, precedence, associativity, f)
            )

        let addPrefixOperator string precedence associativity f =
            oppLtl.AddOperator(
                PrefixOperator(string, spaces, precedence, associativity, f)
            )

        let additionPrecedence = 10

        do
            oppLtl.TermParser <- basicParser

            addInfixOperator "&" additionPrecedence Associativity.Left (fun x y -> And(x, y))
            addInfixOperator "|" additionPrecedence Associativity.Left (fun x y -> Or(x, y))
            addInfixOperator "->" additionPrecedence Associativity.Left (fun x y -> Implies(x, y))
            addInfixOperator "<->" additionPrecedence Associativity.None (fun x y -> Equiv(x, y))
            addInfixOperator "xor" additionPrecedence Associativity.None (fun x y -> Xor(x, y))
            addInfixOperator "U" additionPrecedence Associativity.Left (fun x y -> U(x, y))
            addInfixOperator "W" additionPrecedence Associativity.Left (fun x y -> W(x, y))
            addInfixOperator "M" additionPrecedence Associativity.Left (fun x y -> M(x, y))
            addInfixOperator "R" additionPrecedence Associativity.Left (fun x y -> R(x, y))

            addPrefixOperator "F" 20 true (fun x -> F x)
            addPrefixOperator "G" 20 false (fun x -> G x)
            addPrefixOperator "X" 20 true (fun x -> X x)
            addPrefixOperator "!" 20 true (fun x -> Not x)

        
        do 
            ltlParserRef := oppLtl.ExpressionParser

        ltlParser

    let private prefixParser = 
        let eParser = stringReturn "exists" EXISTS
        let uParser = stringReturn "forall" FORALL
        
        spaces >>.
        many1 ((eParser <|> uParser) .>> spaces)


    let private hyperltlParser (atomParser : Parser<'T * int, unit>) = 
        pipe2 
            prefixParser
            (ltlParser atomParser)
            (fun x y -> {HyperLTL.QuantifierPrefix = x; LTLMatrix = y})


    let parseLTL (atomParser : Parser<'T, unit>) s =    
        let full = ltlParser atomParser .>> spaces .>> eof
        let res = run full s
        match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> failwith err

    let parseHyperltl (atomParser : Parser<'T * int, unit>) s =    
        let full = hyperltlParser atomParser .>> spaces .>> eof
        let res = run full s
        match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> failwith err


module Random = 

    /// Given a seed, size bounds, a list of aps and a number of samples, call spots randltl to genarte random LTL formulas
    let private invokeRandLtl (seed : int) (sizel : int, sizeu : int)  (aps : list<string>) (numberOfSamples : int) = 
    
        let args = "--seed=" + string(seed) + " --tree-size=" + string(sizel) + ".." + string(sizeu) + " --ltl-priorities \"xor=0,M=0\"" + " -p -n" + string(numberOfSamples) + (List.fold (fun s x -> s + " " + x) "" aps)
        let res = 
            Util.systemCall (Util.spotPath + "randltl") args Option.None
            |> ReturnOption.get
        
        let lines = 
            res.Split('\n')
            |> Array.toList
            |> List.filter (fun x -> x <> "")

        let asLtL = 
            lines 
            |> List.map (fun x -> Parser.parseLTL Util.relVarParser x)

        asLtL

    /// Generates random HyperLTL formulas with a given quantifier prefix
    let getRandomHyperLTL (prefix : list<TraceQuantifierType>) (sizel, sizeu) (aps : list<String>) numberOfSamples = 
        let indexed_aps = 
            List.allPairs aps [0..prefix.Length-1]
            |> List.map (fun (x, i) -> x + "_" + string(i))
            
        let seed = Util.rnd.Next() 

        let ltlFormulas = invokeRandLtl seed (sizel, sizeu) indexed_aps numberOfSamples

        let hyperltlFormulas = 
            ltlFormulas
            |> List.map (fun x -> {HyperLTL.QuantifierPrefix = prefix; LTLMatrix = x})

        hyperltlFormulas

    /// Generates random HyperLTL formulas with a given quantifier prefix but calls spot once for each sample. Multiple formulas can thus be identical
    let getRandomHyperLTLOneByOne (prefix : list<TraceQuantifierType>) (sizel, sizeu) (aps : list<String>) numberOfSamples = 
        let indexed_aps = 
            List.allPairs aps [0..prefix.Length-1]
            |> List.map (fun (x, i) -> x + "_" + string(i))

        let ltlFormulas = 
            List.init numberOfSamples 
                (fun _ -> 
                    let seed = Util.rnd.Next() 
                    let formulas = invokeRandLtl seed (sizel, sizeu) indexed_aps 10

                    let indexToPick =  
                        Util.rnd.Next(10)
                    formulas.[indexToPick]
                )

        let hyperltlFormulas = 
            ltlFormulas
            |> List.map (fun x -> {HyperLTL.QuantifierPrefix = prefix; LTLMatrix = x})

        hyperltlFormulas

