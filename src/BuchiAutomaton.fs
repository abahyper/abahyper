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

module BuchiAutomaton

open System 
open System.IO
open System.Collections.Generic

type private ThreeValues = TOP | BOT | DASH


/// A boolean expressions over atoms of type 'T
type BooleanCombination<'T when 'T: comparison> = 
    | Atom of 'T 
    | True 
    | False
    | Neg of BooleanCombination<'T>
    | And of BooleanCombination<'T> * BooleanCombination<'T>
    | Or of BooleanCombination<'T> * BooleanCombination<'T>

    member this.AsString() = 
        match this with 
            | Atom x -> string x
            | True -> "t" 
            | False -> "f" 
            | Neg c -> "(!" + c.AsString() + ")"
            | And(c1, c2) -> "(" + c1.AsString() + "&" + c2.AsString() + ")"
            | Or(c1, c2) -> "(" + c1.AsString() + "|" + c2.AsString() + ")"

    /// Given an assignment to the atoms, evaluate this expression
    member this.Eval (A : 'T -> bool) = 
        match this with 
            | Atom x -> A x
            | True -> true 
            | False -> false 
            | Neg c -> not (c.Eval A)
            | And(c1, c2) -> (c1.Eval A) && (c2.Eval A)
            | Or(c1, c2) -> (c1.Eval A) || (c2.Eval A)

    /// Given an assignment to the atoms (provided as a map), evaluate this expression
    member this.EvalMap (A : Map<'T, bool>) = 
        match this with 
            | Atom x -> A.[x]
            | True -> true 
            | False -> false 
            | Neg c -> not (c.EvalMap A)
            | And(c1, c2) -> (c1.EvalMap A) && (c2.EvalMap A)
            | Or(c1, c2) -> (c1.EvalMap A) || (c2.EvalMap A)
    
    /// Map the atoms in this formula
    member this.Map (f : 'T -> 'U) = 
        match this with 
            | Atom x -> Atom (f x)
            | True -> True 
            | False -> False 
            | Neg c -> Neg (c.Map f)
            | And(c1, c2) -> And(c1.Map f, c2.Map f)
            | Or(c1, c2) -> Or(c1.Map f, c2.Map f)

    member this.MapWithMap (f : Map<'T,'U>) = 
        this.Map (fun x -> f.[x])

    /// Compute all atoms used in this formula
    member this.Atoms = 
        match this with 
            | Atom x -> Set.singleton x 
            | True | False -> Set.empty
            | Neg e -> e.Atoms
            | And(e1, e2) | Or (e1, e2) -> Set.union e1.Atoms e2.Atoms

    /// Fix the boolean value of some of the atoms in this formula
    member this.FixValues (m : Map<'T, bool>) = 
        match this with 
            | Atom x -> if m.ContainsKey x then (if m.[x] then True else False) else Atom x
            | True -> True 
            | False -> False 
            | Neg c -> Neg (c.FixValues m)
            | And(c1, c2) -> And(c1.FixValues m, c2.FixValues m)
            | Or(c1, c2) -> Or(c1.FixValues m, c2.FixValues m)

    /// Check if this boolean formula is SAT
    member this.IsSat() =  
        let atoms = 
            this.Atoms
            |> Set.toList
            
        // We simply try all possible assignments
        // This is very inefficient, but works on the small formulas we consider
        Util.computeBooleanPowerSet (List.length atoms)
        |> Seq.exists (fun x -> 
            let A = 
                List.zip atoms x 
                |> Map.ofList
            this.EvalMap A)

   /// Given a set of formulas construct an AND
    static member constructAnd (l) = 
        match l with 
            | [] -> True 
            | [x] -> x 
            | xs -> List.reduce (fun x y -> And(x, y)) xs

    // Given a set of formulas construct a OR
    static member constructOr (l) = 
        match l with 
            | [] -> False 
            | [x] -> x 
            | xs -> List.reduce (fun x y -> Or(x, y)) xs


// #######################################################################################

/// A NBA consists of a set of states, a set of initial states, the list of APs, a set of accepting states and
/// a step function that maps states to a list of transitions (pairs of guard formula and successor state)
type NBA<'T, 'L when 'T: comparison> = 
    {
        States : Set<'T>
        InitialStates : Set<'T>
        APs: list<'L>
        Step: Map<'T, list<BooleanCombination<int> * 'T>>
        AcceptingStates : Set<'T>
    }

    /// Convert the states to the fixed type INT
    member this.ConvertStatesToInt() = 
        let idDict = new Dictionary<_,_>()
        let mutable currentId = 0
        for s in this.States do 
            idDict.Add(s, currentId)
            currentId <- currentId + 1

        {
            States = this.States |> Set.map (fun x -> idDict.[x]);
            InitialStates = this.InitialStates |> Set.map (fun x -> idDict.[x]);
            APs = this.APs;
            Step = this.Step |> Map.toSeq |> Seq.map (fun (k, v) -> idDict.[k], v |> List.map (fun (g, s) -> g, idDict.[s])) |> Map.ofSeq
            AcceptingStates = 
                this.AcceptingStates
                |> Set.map (fun x -> idDict.[x])
        }
    
    /// Map a function on the APs
    member this.ReplaceAPs (f : 'L -> 'U) = 
        {
            States = this.States;
            InitialStates = this.InitialStates
            APs = this.APs |> List.map f
            Step = this.Step
            AcceptingStates = this.AcceptingStates
        }

    /// Write this automaton in the Hoa (HANOI) format 
    member this.WriteHoaFormat (s : StringWriter) = 
        let idDict = new Dictionary<_,_>()
        let mutable currentId = 0
        for s in this.States do 
            idDict.Add(s, currentId)
            currentId <- currentId + 1
        
        s.WriteLine("HOA: v1")

        s.WriteLine ("States: " + string(idDict.Count))
        
        // Write all initial states
        for n in this.InitialStates do 
            s.WriteLine ("Start: " + string(idDict.[n]))

        s.WriteLine ("AP: " + string(this.APs.Length) + " " + List.fold (fun s x -> s + " \"" + string(x) + "\"") "" this.APs)

        s.WriteLine ("acc-name: Buchi")

        s.WriteLine ("Acceptance: 1 Inf(0)")
        
        s.WriteLine "--BODY--"
        
        // We put each state of the automaton in the body
        for n in this.States do 
            let accString = if this.AcceptingStates.Contains n then " {0}" else ""
            s.WriteLine("State: " + string(idDict.[n]) + " " + accString)

            for (g, n') in this.Step.[n] do 
                s.WriteLine("[" + g.AsString() + "] " + string(idDict.[n']))

        s.WriteLine "--END--"


/// A NBA that has an explict alphabet, i.e., each transition is not guarded by a formula over AP but by a single letter from the Alphabet
/// An explicit NBA has a unqiue initial state (as required by the BA format)
type ExplicitNBA<'T, 'L when 'T: comparison> = 
    {
        States : Set<'T>
        InitialState : 'T
        Alphabet: list<'L>
        Step: Map<'T, list<int * 'T>>
        AcceptingStates : Set<'T>
    }

    /// Writes this automaton in the BA format
    /// Assumes a function that converts letters of the alphabet to a string
    member this.WriteBaFormat (alphMapper : 'L -> String) (s : StringWriter) = 
        let idDict = new Dictionary<_,_>()
        let mutable currentId = 0
        for s in this.States do 
            idDict.Add(s, "["+ string(currentId) + "]")
            currentId <- currentId + 1
        
        s.WriteLine (idDict.[this.InitialState])

        // Each transition of each state is written in a separate line
        for n in this.States do 
            for (l, n') in this.Step.[n] do 
                s.WriteLine (alphMapper (this.Alphabet.[l]) + "," + idDict.[n] + "->" + idDict.[n'])

        for n in this.AcceptingStates do 
            s.WriteLine (idDict.[n])


type AutState<'T> =
    | Initial
    | NormalState of 'T

/// Converts a (symbolic) NBA to one with an explicit alphabet
let convertToExplicitNBA (nba : NBA<'T, 'L>) = 

    let alphabet = 
        Util.computeBooleanPowerSet (nba.APs.Length)
        |> Seq.toList

    let newStates = 
        nba.States 
        |> Set.map NormalState
        |> Set.add Initial

    let newStep = 
        nba.States
        |> Set.toList
        |> List.map (fun x ->
            NormalState x, [
                // We iterate over every possible element in the alphabet that satsifies this guard formula
                for guard, s in nba.Step.[x] do 
                    for i in 0..alphabet.Length - 1 do 
                        if guard.Eval (fun j -> alphabet.[i].[j]) then 
                            (i, NormalState s)
            ]
            )
        |> Map.ofList
        |> Map.add Initial (
            [
                // The initial state of th explicit NBA has all transitions that can be taken from some initial state of the symbolic NBA
                for s in nba.InitialStates do 
                    for guard, s in nba.Step.[s] do 
                        for i in 0..alphabet.Length - 1 do 
                            if guard.Eval (fun j -> alphabet.[i].[j]) then 
                                (i, NormalState s)
            ]
        )

    let newAcceptingStates = 
        nba.AcceptingStates
        |> Set.map NormalState
        |> Set.add Initial

    let enba = 
        {
            ExplicitNBA.States = newStates
            InitialState = Initial
            Step = newStep
            Alphabet = alphabet
            AcceptingStates = newAcceptingStates
        }

    enba