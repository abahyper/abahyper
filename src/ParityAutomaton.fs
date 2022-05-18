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

module ParityAutomaton

open System.IO
open System.Collections.Generic

open BuchiAutomaton


/// A DPA consists of a set of states, a unique initial states, the list of APs,
/// a step function that maps states to a list of transitions (pairs of guard formula and successor state) and a coloring of each node
/// We assume that the automaton is deterministic
type DPA<'T, 'L when 'T: comparison and 'L: comparison> = 
    {
        States : Set<'T>
        InitialState : 'T
        APs: list<'L>
        Step: Map<'T, list<BooleanCombination<int> * 'T>>
        Colour : Map<'T, int>
    }

    /// Convert the states to the fixed type INT
    member this.ConvertStatesToInt ()  = 
        let idDict = new Dictionary<_,_>()
        let mutable currentId = 0
        for s in this.States do 
            idDict.Add(s, currentId)
            currentId <- currentId + 1
        
        let res = 
            {
                DPA.States = this.States |> Set.map (fun x -> idDict.[x]);
                InitialState = idDict.[this.InitialState];
                APs = this.APs;
                Step = this.Step |> Map.toSeq |> Seq.map (fun (k, v) -> idDict.[k], v |> List.map (fun (g, s) -> g, idDict.[s])) |> Map.ofSeq
                Colour = this.Colour |> Map.toSeq |> Seq.map (fun (k,v) -> idDict.[k], v) |> Map.ofSeq
            }

        res

    /// Map a function over the APs
    member this.ReplaceAPs<'U when 'U: comparison> (f : 'L -> 'U) = 
            {
                States = this.States;
                InitialState = this.InitialState
                APs = this.APs |> List.map f
                Step = this.Step
                Colour = this.Colour
            }

    /// Write this automaton in the HOA (HANOI) format
    member this.WriteHoaFormat (s : StringWriter) = 
        let idDict = new Dictionary<_,_>()
        let mutable currentId = 0
        for s in this.States do 
            idDict.Add(s, currentId)
            currentId <- currentId + 1
        
        let maxColour = 
            this.Colour |> Map.toSeq |> Seq.map snd |> Seq.max

        let rec createParityString c = 
            if c = 0 then 
                "Inf(0)"
            else 
                if c % 2 = 0 then 
                    "(Inf(" + string(c) + ") | " + createParityString(c-1) + ")"
                else
                    "(Fin(" + string(c) + ") & " + createParityString(c-1) + ")"

        s.WriteLine("HOA: v1")

        s.WriteLine ("States: " + string(idDict.Count))

        s.WriteLine ("Start: " + string(idDict.[this.InitialState]))

        s.WriteLine ("AP: " + string(this.APs.Length) + " " + List.fold (fun s x -> s + " \"" + string(x) + "\"") "" this.APs)

        s.WriteLine ("acc-name: parity max even " + string(maxColour + 1))

        s.WriteLine ("Acceptance: " + string(maxColour + 1) + " " + createParityString maxColour)

        s.WriteLine "--BODY--"

        for n in this.States do 
            s.WriteLine("State: " + string(idDict.[n]) + " {" + string(this.Colour.[n]) + "}")

            for (g, n') in this.Step.[n] do 
                s.WriteLine("[" + g.AsString() + "] " + string(idDict.[n']))

        s.WriteLine "--END--"

