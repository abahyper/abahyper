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

module ProductConstruction

open System.Collections.Generic

open TransitionSystem
open BuchiAutomaton
open Converter

let private swProduct = System.Diagnostics.Stopwatch()

/// Given a automaton,a list of system
/// and a list of indices construct the projection of the automaton on the transition systems
let constructAutomatonSystemProduct (aut : NBA<'Astate, 'L * int>) (tslist : list<TransitionSystem<'Tstates, 'L>>) (indexList : list<int>) = 
    swProduct.Restart()
    
    let copyToTsMapper = 
        indexList
        |> List.mapi (fun i j -> j, i)
        |> Map.ofList

    // Map the aps for the pos index into the position in ts
    let quickApIndexFinderPos = 
        aut.APs
        |> List.mapi (fun j (l, i) -> 
            if copyToTsMapper.Keys.Contains i then 
                let tsIndex = copyToTsMapper.[i]
                Some (j,  (tsIndex, tslist.[tsIndex].APs |> List.findIndex (fun l' -> l = l')))
            else
                None
            )
        |> List.choose id 
        |> Map.ofList

    // Compute the APs that will be used in the computed automaton where the indices in indexList are projected away
    let newAps = 
        aut.APs
        |> List.filter (fun (_, i) -> copyToTsMapper.Keys.Contains i |> not)

    // Map the index from the (old) aut.APs to the APs of the automaton we will construct
    let quickApIndexFinderRemaining =
        newAps
        |> List.mapi (fun i x -> aut.APs |> List.findIndex (fun y -> y = x), i)
        |> Map.ofList
        
    // Our new automaton operates on pairs of system states and automaton state
    let initStates : list<list<'Tstates> * 'Astate> = 
        [
             for tstates in (tslist |> List.map (fun x -> x.InitialStates |> seq) |> Util.cartesianProduct) do  
                for astate in aut.InitialStates do 
                    (tstates, astate)
        ]

    let queue = new Queue<_>(initStates)
    let allStates = new HashSet<_>(initStates)

    let stepDict = new Dictionary<_,_>()
    let accStates = new HashSet<_>()
    
    while queue.Count <> 0 do 
        let n = queue.Dequeue()
        let tstates, astate = n 

        let sucStates, apEvaluations = 
            tstates
            |> List.mapi (fun i x -> tslist.[i].Step.[x])
            |> List.unzip

        let allNextTStates = 
            sucStates
            |> List.map seq
            |> Util.cartesianProduct

        // This map fixes all propositions that refer to a system that used used in the projection
        let fixingMap = 
            quickApIndexFinderPos
            |> Map.map (fun _ (index, pos) -> apEvaluations.[index].[pos])

        let automatonSucs = aut.Step.[astate]
        let productSucs = new HashSet<_>()
        
        for guard, astate' in automatonSucs do 
            // We iterate over all outgoing transition and fix the value of the APs that are projected away (using fixingMap)
            let guardFixed = guard.FixValues fixingMap

            if guardFixed.IsSat() then 
                // We only consider this guard if it is actually sat (after having fixed the projected atoms)
                
                let remapped = guardFixed.Map (fun x -> quickApIndexFinderRemaining.[x])

                for tstates' in allNextTStates do 
                    productSucs.Add (remapped, (tstates', astate')) |> ignore

                    if allStates.Contains (tstates', astate') |> not then 
                        allStates.Add (tstates', astate') |> ignore
                        queue.Enqueue (tstates', astate')

        let asList = 
            productSucs
            |> Seq.toList

        stepDict.Add(n, asList)
        if aut.AcceptingStates.Contains astate then
            accStates.Add(n) |> ignore
        
    // Convert the step dict to a immutable map
    let imStepDict = 
        stepDict
        |> Seq.map (fun x -> x.Key, x.Value)
        |> Map.ofSeq

    let nba = 
        {
            NBA.States = allStates |> seq |> set;
            InitialStates = initStates |> set;
            APs = newAps; 
            Step = imStepDict;
            AcceptingStates = accStates |> set;
        }
    swProduct.Stop()
    {
        SystemCallResult.Result = nba;
        SystemCallResult.Time = 
            {
                IOTime = 0
                ToolTime = int(swProduct.ElapsedMilliseconds)
                HOATime = 0
            }
    }