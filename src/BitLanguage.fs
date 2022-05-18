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


module BitLanguage 

open System
open System.Collections.Generic

open TransitionSystem

type Var = String 

type Value = list<bool>

type VarAssignment = Map<Var, Value>


/// The program expressions supported in the boolean PL
type ProgramExpression = 
    | True 
    | False
    | Variable of Var
    | And of ProgramExpression * ProgramExpression
    | Or of ProgramExpression * ProgramExpression
    | Not of ProgramExpression 
    | Proj of ProgramExpression * int 
    | Concat of ProgramExpression * ProgramExpression
    | Dup of ProgramExpression * int 

    /// Given an assignment to the variables, evaluate the expression
    member this.Eval (A : VarAssignment) : Value = 
        match this with 
            | True -> [true]
            | False -> [false]
            | Variable x -> A.[x]
            | And(e1, e2) -> 
                List.zip (e1.Eval A) (e2.Eval A)
                |> List.map (fun (x, y) -> x && y)
            | Or(e1, e2) ->
                List.zip (e1.Eval A) (e2.Eval A)
                |> List.map (fun (x, y) -> x || y)
            | Not e -> 
                e.Eval A |> List.map not
            | Proj(e, n) -> [(e.Eval A).[n]]
            | Concat(e1, e2) -> List.append (e1.Eval A) (e2.Eval A)
            | Dup(e, n) -> 
                let t = e.Eval A
                
                List.init n (fun _ -> t)
                |> List.concat 


/// The program statements in the boolean PL
type ProgramStatement = 
    | Terminated
    | Skip
    | Assignment of Var * ProgramExpression 
    | If of ProgramExpression * ProgramStatement * ProgramStatement
    | Nondet of ProgramStatement * ProgramStatement
    | Read of  Var 
    | Seq of list<ProgramStatement>
    | While of ProgramExpression * ProgramStatement

    /// Given a variable assignment compute one step of the current statement
    /// This returns a sequence of next statements and assignments
    member this.OneStep(A : VarAssignment) = 
        match this with 
            | Terminated -> Seq.singleton (this, A)
            | Skip -> Seq.singleton (Terminated, A)
            | Assignment(v, e) ->
                let newVal = e.Eval A
                let newAssignment = Map.add v newVal A
                Seq.singleton (Terminated, newAssignment)
            | If(e, s1, s2) -> 
                let res = e.Eval A
                if res.[0] then 
                    Seq.singleton (s1, A)
                else
                    Seq.singleton (s2, A)
            | Nondet(s1, s2) ->
                seq {(s1, A); (s2, A)}
            | Read v -> 
                let width = A.[v].Length
                seq {for b in Util.computeBooleanPowerSet width do (Terminated,  Map.add v b A)}
            | Seq slist -> 
                match slist with 
                    | [] -> Seq.singleton (Terminated, A)
                    | [x] -> x.OneStep A
                    | x::xs -> 
                        x.OneStep A
                        |> Seq.map (fun (s, A') -> 
                            match s with 
                                | Terminated -> (Seq xs, A')
                                | t -> (Seq(t::xs), A')
                            )
            | While(e, s) -> 
                let res = e.Eval A 
                if res.[0] then 
                    Seq.singleton (Seq[s; While(e, s)], A)
                else
                    Seq.singleton (Terminated, A)
                    
/// A program has a name, a bitwidth for each variables and a root statement
type Program = 
        {
            Name : String
            DomainMap : Map<Var, int>
            Statement : ProgramStatement
        }

module Compilation = 
    
    type ProgramState = ProgramStatement * VarAssignment

    /// Given a program and a list of propositions that are relevant, compile the program to a TS
    let compileProgramToTS (P : Program) (relevantAps : list<Var * int>) = 

        let initialState : ProgramState = (P.Statement, Map.map (fun k x -> List.init x (fun _ -> false)) P.DomainMap)

        let mutable currentId = 0

        let initialStates = new HashSet<_>()
        initialStates.Add currentId |> ignore

        // Map state ids to program states
        let idDict = new Dictionary<_,_>()

        idDict.Add(initialState, currentId)
        currentId <- currentId + 1

        let queue = new Queue<_>()
        queue.Enqueue initialState

        let stepMap = new Dictionary<_,_>()

        while queue.Count <> 0 do 
            let s, A = queue.Dequeue() 

            let id = idDict.[s, A]

            // Compute the successor states of the program state by taking one step with the current assignment
            let sucs = new HashSet<_>()
            for c in s.OneStep A  do 
                if idDict.ContainsKey c then 
                    sucs.Add(idDict.[c]) |> ignore
                else 
                    idDict.Add(c, currentId)
                    queue.Enqueue c  
                    sucs.Add(currentId) |> ignore

                    currentId <- currentId + 1

            // To get the AP evaluation, we check the variable content of each variable in the APs
            let aps =   
                relevantAps 
                |> List.map (fun (v, i) -> 
                    A.[v].[i]
                    )
            
            stepMap.Add(id, (sucs, aps))

        
        let res = 
            {
                InitialStates = initialStates;
                APs = relevantAps;
                Step = stepMap;
            }

        res

module Parser =

    open System 
    open FParsec

    let private ws = spaces

    let private varParser = 
        many1Chars letter 

    let private expParser, private expParserRef = createParserForwardedToRef()

    let private trueParser = 
        stringReturn "t" True

    let private falseParser = 
        stringReturn "f" False 

    let private variableParser = 
        attempt
            (
                varParser 
                >>= (fun x -> if x <> "t" && x <> "f" then Variable x |> preturn else fail "")
            )
    
    let private andParser = 
        pstring "(&" >>. spaces >>.
            pipe2 
                expParser
                expParser
                (fun x y -> And(x, y))
        .>> spaces .>> pstring ")"

    let private orParser = 
        pstring "(|" >>. spaces >>.
            pipe2 
                expParser
                expParser
                (fun x y -> Or(x, y))
        .>> spaces .>> pstring ")"

    let private concatParser = 
        pstring "(@" >>. spaces >>.
            pipe2 
                expParser
                expParser
                (fun x y -> Concat(x, y))
        .>> spaces .>> pstring ")"

    let private notParser = 
        pstring "(!" >>. expParser .>> spaces .>> pstring ")"
        |>> Not

    let private parParser = 
        pstring "(" >>. expParser .>> pstring ")"

    let private projParser = 
        pstring "(#" >>.
            pipe2 
                expParser 
                (spaces >>. pint32)
                (fun x y -> Proj(x, y))
        .>> spaces .>> pstring ")" 

    let private dupParser = 
        pstring "(x" >>.
            pipe2 
                expParser 
                (spaces >>. pint32)
                (fun x y -> Dup(x, y))
        .>> spaces .>> pstring ")" 

    do expParserRef := 
        spaces >>. choice [
                andParser
                orParser
                concatParser
                projParser
                dupParser
                notParser
                parParser
                variableParser
                trueParser
                falseParser
        ] .>> spaces

    let private statementParser, private statementParserRef = createParserForwardedToRef() 

    let private assignmentParser = 
        pipe3 
            varParser
            (spaces .>> pstring ":=" .>> spaces)
            expParser
            (fun x _ y -> Assignment(x, y))

    let private ifParser = 
        pstring "IF" >>. spaces >>. pstring "(" >>.
            pipe3 
                (expParser .>> spaces .>> pstring ")" .>> spaces .>> pstring "THEN" .>> spaces .>> pstring "{")
                (statementParser .>> spaces .>> pstring "}" .>> spaces .>> pstring "ELSE" .>> spaces .>> pstring "{")
                (statementParser .>> spaces .>> pstring "}")
                (fun x y z -> If(x, y, z))
    
    let private ndetParser = 
        pstring "NONDET" >>. spaces >>. pstring "THEN" >>. spaces >>. pstring "{" >>.
            pipe2
                (statementParser .>> spaces .>> pstring "}" .>> spaces .>> pstring "ELSE" .>> spaces .>> pstring "{")
                (statementParser .>> spaces .>> pstring "}")
                (fun x y -> Nondet(x, y))


    let private inParser = 
        pstring "READ" >>. spaces >>. pstring "(" >>. varParser .>> spaces .>> pstring ")"
        |>> Read
    
    let private skipParser = 
        stringReturn "SKIP" Skip

    let private whileParser = 
        pstring "WHILE" >>. spaces >>. pstring "(" >>.
            pipe2
                (expParser .>> spaces .>> pstring ")" .>> spaces .>> pstring "{")
                (statementParser .>> spaces .>> pstring "}")
                (fun x y -> While(x, y))

    let private seqParser = 
        between (pchar '[') (pchar ']') (sepBy (statementParser .>> spaces) (pchar ';'))
        |>> Seq


    do statementParserRef := 
        spaces >>. choice [
                ifParser
                ndetParser
                inParser
                skipParser
                whileParser
                seqParser
                assignmentParser
        ] .>> spaces

    let private parseHeader = 
        spaces >>. pstring "dom:" >>. spaces >>. pchar '[' >>. spaces >>.
        sepBy (between (pchar '(') (pchar ')')  (varParser .>>. (spaces >>. pint32) .>> spaces)) (pchar ',' .>> spaces)
        .>> spaces .>> pchar ']'
        |>> Map.ofList

    let private programParser = 
        pipe2
            parseHeader
            (spaces >>. statementParser)
            (fun x y -> {Program.DomainMap = x; Name = ""; Statement = y})

    let parseProgram (s : String) = 
        let full =
            programParser .>> spaces .>> eof

        let res = run full s

        match res with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> failwith err