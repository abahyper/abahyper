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

module HoaParser

open System 
open FParsec

open BuchiAutomaton
open ParityAutomaton

type AcceptanceConditionAtom = Fin | Inf

/// A boolean acceptance formula as used by the HOA format 
type AcceptanceCondition = 
    | AccAtom of AcceptanceConditionAtom * bool * int
    | AccTrue 
    | AccFalse 
    | AccAnd of AcceptanceCondition * AcceptanceCondition
    | AccOr of AcceptanceCondition * AcceptanceCondition

/// A type representing the header of the HOA format
type AutomatonHeader = 
    {
        HoaVersion : option<string>
        States : option<int>
        Start : list<int>
        APs : option<list<String>>
        Properties : list<String> 
        Tool : option<list<String>>
        Name : option<String>
        Acceptance : option<int * AcceptanceCondition>
        AcceptanceName : option<list<String>>
    }

/// A type representing the body of the HOA format
type AutomatonBody = 
    {
        StateMap : Map<int, Set<int> * list<BooleanCombination<int> * int>>
    }

type HoaAutomaton = 
    {
        Header : AutomatonHeader;
        Body : AutomatonBody
    }

/// This module contains several conversion methods that extract from a (general) Hoa automaton, more specific automata
module Converter =
    
    /// Convert a HOA automaton (that is assumed to be a NBA) to a NBA
    let convertToNba (hoaAut : HoaAutomaton) = 
        let header = hoaAut.Header
        let body = hoaAut.Body

        let step = 
            body.StateMap
            |> Map.map (fun _ x -> snd x)

        // The accepting states are all those where the unqieue accepting set is non-empty
        let accepting = 
            body.StateMap
            |> Map.map (fun _ x -> fst x)
            |> Map.toSeq
            |> Seq.filter (fun (x, y) -> y.Count <> 0)
            |> Seq.map fst
            |> set 
            
        let nba =
            {
                NBA.States = set [0..header.States.Value - 1];
                InitialStates = header.Start |> set;
                APs = header.APs.Value
                Step = step
                AcceptingStates = accepting
            }
        nba

    /// Convert a HOA automaton (that is assumed to be a DPA) to a DPA
    let convertToDpa (hoaAut : HoaAutomaton) = 
        let header = hoaAut.Header
        let body = hoaAut.Body

        let step = 
            body.StateMap
            |> Map.map (fun _ x -> snd x)

        let colour = 
            body.StateMap
            |> Map.map (fun _ x -> fst x)
            // As we deal with a parity automaton, we can assume that *all* nodes are coloured by spot
            |> Map.map (fun _ x -> x |> seq |> Seq.last)

        assert(colour.Count = header.States.Value)
        assert(step.Count = header.States.Value)


        let dpa =
            {
                DPA.States = set [0..header.States.Value - 1];
                DPA.InitialState = header.Start.[0];
                DPA.APs = header.APs.Value
                DPA.Colour = colour
                DPA.Step = step
            }
        dpa

/// A module that allows to parse a HOA automaton
module Parser =
    
    // Whitespaces without newline
    let private ws = manyChars (satisfy (fun x -> x = ' ' || x = '\t')) |>> ignore
    
    let private headerParser =
        let headerLineParser (header : AutomatonHeader) = 

            let hoaParser = 
                skipString "HOA:" >>. ws >>. many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n'))
                |>> (fun x -> {header with HoaVersion = Some x})

            let nameParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "name:" >>. ws >>. escapedStringParser
                |>> fun x -> {header with Name = Some x}

            let toolParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "tool:" >>. ws >>. many1 (escapedStringParser .>> ws)
                |>> fun x -> {header with Tool = Some x}


            let apParser  = 
                let escapedStringParser = 
                    skipChar '\"' >>. many1Chars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'

                skipString "AP:" >>. ws >>.
                    pipe2 
                        pint32 
                        (ws >>. many (escapedStringParser .>> ws))
                        (fun x y -> {header with APs = Some y})

            let statesParser  = 
                skipString "States:" >>. ws >>. pint32
                |>> fun x -> {header with States = Some x}

            let startParser = 
                skipString "Start:" >>. ws >>. pint32
                |>> fun x -> {header with Start = x::header.Start}


            let propertiesParser = 
                skipString "properties:" >>. ws >>. many1 (many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n')) .>> ws)
                |>> fun x -> {header with Properties = x @ header.Properties}
                

            let accNameParser = 
                skipString "acc-name:" >>. ws >>. many1 (many1Chars (satisfy (fun x -> x <> ' ' && x <> '\n')) .>> ws)
                |>> fun x -> {header with AcceptanceName = Some x}


            let accParser = 
                let accParser, accParserRef = createParserForwardedToRef()

                let literalParser = 
                    (skipChar '!' >>. ws >>. pint32 |>> (fun x -> false, x))
                    <|>
                    (pint32 |>> (fun x -> true, x))

                let infParser = 
                    skipString "Inf" >>. ws .>> skipChar '(' >>. ws >>. literalParser .>> ws .>> pchar ')'
                    |>> fun (b, x) -> AccAtom (Inf, b, x)

                let finParser = 
                    skipString "Fin" >>. ws .>> skipChar '(' >>. ws >>. literalParser .>> ws .>> pchar ')'
                    |>> fun (b, x) -> AccAtom (Fin, true, x)

                let parParser = 
                    skipChar '(' >>. accParser .>> ws .>> skipChar ')'

                let falseParser = 
                    charReturn 'f' AccFalse

                let trueParser = 
                    charReturn 't' AccTrue
                
                let opp = new OperatorPrecedenceParser<AcceptanceCondition, unit, unit>()
                
                let addInfixOperator string precedence associativity f =
                    opp.AddOperator(
                        InfixOperator(string, ws, precedence, associativity, f)
                    )
                
                let orPrecedence = 10
                let andPrecedence = 20

                addInfixOperator "&" andPrecedence Associativity.Left (fun e1 e2 -> AccAnd(e1, e2))
                addInfixOperator "|" orPrecedence Associativity.Left (fun e1 e2 -> AccOr(e1, e2))

                let innerParser = 
                    spaces >>. choice [
                        falseParser
                        trueParser
                        infParser
                        finParser
                        parParser
                    ] .>> spaces

                opp.TermParser <- innerParser
                
                do accParserRef := opp.ExpressionParser

                skipString "Acceptance:" >>. spaces >>. pint32 .>>. accParser
                |>> fun (x, y) -> {header with Acceptance = Some (x, y)}

            choice [
                hoaParser
                nameParser
                toolParser
                apParser
                statesParser
                startParser
                propertiesParser
                accNameParser
                accParser
            ] .>> spaces

        let initHeader = 
            {
                HoaVersion = None
                States = None
                Start = []
                APs = None
                Properties  = []
                Tool  = None
                Name = None
                Acceptance  = None
                AcceptanceName = None
            }
        
        let rec headerParserRec (header: AutomatonHeader) =
            (attempt (headerLineParser header) >>= headerParserRec)
            <|>% header
        
        headerParserRec initHeader
        
    let private bodyParser =
        let booleanCombinationParser = 
            let bcParser, bcParserRef  = createParserForwardedToRef()

            let atomParser = 
                pint32 |>> (fun x -> BooleanCombination.Atom x)

            let trueParser = 
                stringReturn "t" BooleanCombination.True

            let falseParser = 
                stringReturn "f" BooleanCombination.False

            let parParser = 
                skipChar '(' >>. bcParser .>> spaces .>> skipChar ')'

            let oppBooleanCombination =
                new OperatorPrecedenceParser<BooleanCombination<int>, unit, unit>()

            // a helper function for adding infix operators to opp
            let addInfixOperator string precedence associativity f =
                oppBooleanCombination.AddOperator(
                    InfixOperator(string, spaces, precedence, associativity, f)
                )

            let addPrefixOperator string precedence associativity f =
                oppBooleanCombination.AddOperator(
                    PrefixOperator(string, spaces, precedence, associativity, f)
                )

            let orPrecedence = 10
            let andPrecedence = 20
            let negPrecedence = 30

            addInfixOperator "&" andPrecedence Associativity.Left (fun e1 e2 -> BooleanCombination.And(e1, e2))
            addInfixOperator "|" orPrecedence Associativity.Left (fun e1 e2 -> BooleanCombination.Or(e1, e2))

            addPrefixOperator "!" negPrecedence true (fun x -> BooleanCombination.Neg x)

            let basicParser = 
                spaces >>. choice [ 
                    parParser
                    atomParser
                    trueParser
                    falseParser
                    //oppBooleanCombination.ExpressionParser
                ] .>> spaces

            oppBooleanCombination.TermParser <- basicParser

            do bcParserRef := oppBooleanCombination.ExpressionParser
            
            bcParser
        
        let edgeParser = 
            pipe2 
                (pchar '[' >>. spaces >>. booleanCombinationParser .>> spaces .>> pchar ']')
                (spaces >>. pint32)
                (fun g t -> (g, t))

        let stateHeadParser = 
            pstring "State:" >>.
                pipe2 
                    (spaces >>. pint32 .>> spaces)
                    (
                        (between (skipChar '{' .>> spaces) (skipChar '}') (many (pint32 .>> spaces)) |>> fun x -> set x)
                        <|>
                        (preturn Set.empty)
                    )
                    (fun a b -> (a, b))

        let stateParser = 
            pipe2 
                (stateHeadParser .>> spaces)
                (many (edgeParser .>> spaces))
                (fun (id, c) y -> id, c, y)

        spaces >>. many (stateParser .>> spaces)
        |>> fun x -> 
            x 
            |> List.map (fun (x, y, z) -> (x, (y, z)))
            |> Map.ofList
            |> fun x -> {AutomatonBody.StateMap = x}

    let private hoaParser =
        pipe3 
            headerParser
            (spaces .>> skipString "--BODY--" .>> spaces)
            (bodyParser .>> spaces .>> skipString "--END--" .>> spaces .>> eof)
            (fun x _ y -> {HoaAutomaton.Header = x; Body = y})

    let parseHoaAutomaton (s: string) =
        let res = run hoaParser s
        match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> failwith err

