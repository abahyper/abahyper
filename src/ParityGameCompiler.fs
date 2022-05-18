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

module ParityGameCompiler

open System 
open System.Collections.Generic

open Util
open TransitionSystem
open ParityAutomaton
open ParityGame


type PGState<'Tstate, 'Astate> =  
    | Regular of list<'Tstate> * list<'Tstate> * 'Astate
    | Chosen of list<'Tstate> * list<'Tstate> * 'Astate
    | Init of list<'Tstate>


let complieToPG<'Tstate, 'Astate, 'L when 'Tstate : comparison and 'Astate : comparison and 'L : comparison> (tslist :  list<TransitionSystem<'Tstate, 'L>>)  (prop : HyperDPA<'Astate, 'L * int>) = 

    let k, l = prop.QuantifierStructure
    let aut = prop.Automaton

    // Given the correct number of systems
    assert (tslist.Length = k + l)


    // ######################################################################################################
    // Compute the AP alignment

    // To make fast lookups this record the position in the list of aps for each ap
   
    // For each atomic proposution record the which copy and which copy within that propistion we refer to
    let autApMapping = 
        aut.APs
        |> List.map (fun (l, i) -> i, tslist.[i].APs |> List.findIndex (fun x -> x = l))
        |> List.toArray

    // ######################################################################################################

    let initialUStates = 
        tslist.[0..k-1]
        |> List.map (fun x -> x.InitialStates |> seq)
        |> Util.cartesianProduct

    let initialEStates = 
        tslist.[k..]
        |> List.map (fun x -> x.InitialStates |> seq)
        |> Util.cartesianProduct

    
    let initalStates = new HashSet<_>()

    let visited = new HashSet<_>()

    //let idDict = new Dictionary<_,_>()
    //let mutable currentId = 0

    let queue = new Queue<_>()

    for ustate in initialUStates do 
        // The initial state fixes only those of the univ copies
        let s = Init(ustate)
        //idDict.Add(s, currentId)
        queue.Enqueue s
        visited.Add s |> ignore
        
        initalStates.Add s |> ignore
        //currentId <- currentId + 1


    let propertyDict = new Dictionary<_,_>()

    while queue.Count <> 0 do 

        let s = queue.Dequeue() 
        //let id = idDict.[s] 

        let sucs, info, p, c = 
            match s with 
                | Init ustates -> 
                    let sucs = new HashSet<_>()

                    for estates in initialEStates do 
                        let sucState = Regular(ustates, estates, aut.InitialState)
                        (*
                        let idOfSuc = 
                            if idDict.ContainsKey sucState then 
                                idDict.[sucState]
                            else 
                                idDict.Add(sucState, currentId)
                                queue.Enqueue sucState

                                let tmp = currentId
                                currentId <- currentId + 1
                                tmp
                        *)
                        sucs.Add sucState |> ignore 

                    let info = "Init " + ustates.ToString()
                    
                    sucs, info, SYSTEM, aut.Colour.[aut.InitialState]

                | Regular(ustates, estates, astate) -> 

                    // #################### Compute the next automaton state ####################
                    let nextAstate = 
                        aut.Step.[astate]
                        |> List.find ( fun (guard, _) -> 
                            guard.Eval (fun x -> 
                                let index, pos = autApMapping.[x]
                                let _, apsat = 
                                    if index < k then 
                                        tslist.[index].Step.[ustates.[index]]
                                    else 
                                        tslist.[index].Step.[estates.[index - k]]
                                apsat.[pos]) 
                        )
                        |> snd


                    // #################### Compute the transition system sucessor for universal copies ####################

                    let allCombinationForUniv = 
                        ustates
                        |> List.mapi (fun i x -> 
                            let sucs, _ = tslist.[i].Step.[x]
                            sucs |> seq
                            )
                        |> Util.cartesianProduct

                    let sucs = new HashSet<_>()

                    for ustates' in allCombinationForUniv do 
                        let sucState = Chosen(ustates', estates, nextAstate)
                        (*
                        let idOfSuc = 
                            if idDict.ContainsKey sucState then 
                                idDict.[sucState]
                            else 
                                idDict.Add(sucState, currentId)
                                queue.Enqueue sucState

                                let tmp = currentId
                                currentId <- currentId + 1
                                tmp
                        *)
                        sucs.Add sucState |> ignore

                    let info = "Regular: " + ustates.ToString() + ", " + estates.ToString() + ", " + astate.ToString()
                    
                    sucs, info, ENV, aut.Colour.[astate]

                | Chosen(ustates, estates, astate) -> 
                    // #################### Compute the transition system sucessor for existential copies ####################

                    let allCombinationForExists = 
                        estates
                        |> List.mapi (fun i x -> 
                            let sucs, _ = tslist.[k + i].Step.[x]
                            sucs |> seq
                            )
                        |> Util.cartesianProduct

                    let sucs = new HashSet<_>()

                    for estates' in allCombinationForExists do 
                        let sucState = Regular(ustates, estates', astate)
                        (*
                        let idOfSuc = 
                            if idDict.ContainsKey sucState then 
                                idDict.[sucState]
                            else 
                                idDict.Add(sucState, currentId)
                                queue.Enqueue sucState

                                let tmp = currentId
                                currentId <- currentId + 1
                                tmp
                        *)
                        sucs.Add sucState |> ignore

                    let info = "Chosen: " + ustates.ToString() + ", " + estates.ToString() + ", " + astate.ToString()
                    
                    sucs, info, SYSTEM, aut.Colour.[astate]

        propertyDict.Add(s, (sucs, info, p, c))
        
        // Add to the queue if new state
        for s' in sucs do 
            if visited.Contains s' |> not then 
                visited.Add s' |> ignore 
                queue.Enqueue s'

                         
    let pg =          
        {
            ParityGame.InitialStates = initalStates;
            Properties = propertyDict;
        }

    pg
