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

module StrategyBasedVerification

open System
open System.Collections.Generic

open Util
open TransitionSystem
open ParityAutomaton
open LTL

/// Summarizes the time used in each step of SBV
type GameTimeSummary = 
    {
        LTL2DPATime : int;
        ProductConstructionTime : int;
        ParityGameSolvingTime : int;
        TotalTime : int
    }

    static member Zero = 
        {
            LTL2DPATime  = 0
            ProductConstructionTime = 0
            ParityGameSolvingTime = 0
            TotalTime = 0
        }

    static member (+) (a : GameTimeSummary, b: GameTimeSummary) =
        {
            LTL2DPATime  = a.LTL2DPATime + b.LTL2DPATime
            ProductConstructionTime = a.ProductConstructionTime + b.ProductConstructionTime
            ParityGameSolvingTime = a.ParityGameSolvingTime + b.ParityGameSolvingTime
            TotalTime = a.TotalTime + b.TotalTime
        }

    static member (/) (a : GameTimeSummary, b: int) =
        {
            LTL2DPATime  = a.LTL2DPATime / b
            ProductConstructionTime = a.ProductConstructionTime / b
            ParityGameSolvingTime = a.ParityGameSolvingTime / b
            TotalTime = a.TotalTime / b
        }

type Player = 
    | SYSTEM 
    | ENV

    member this.AsString() =    
        match this with
            | SYSTEM -> "0"
            | ENV -> "1"

    member this.Flip = 
        match this with
            | SYSTEM -> ENV
            | ENV -> SYSTEM

/// A parity game has a set of initial states and a mapping from states to successors, name, player and color
type ParityGame<'T when 'T : comparison> = 
    {
        InitialStates : HashSet<'T>
        Properties: Dictionary<'T, HashSet<'T> * String * Player * int>
    }

/// Solve the parity game using Zielonkas algorithm
let private solveParityGame (pg : ParityGame<'T>) =

    let predMap = new Dictionary<'T, HashSet<'T>>()

    for s in pg.Properties.Keys do 
        predMap.Add(s, new HashSet<'T>())

    for s in pg.Properties.Keys do 
        let sucs, _, _, _ = pg.Properties.[s]
        for s' in sucs do
            predMap.[s'].Add s |> ignore

    // We represent targets as indicator functions to avoids creation of to many sets
    let computeAttractor (currentArea : HashSet<'T>) (target : 'T -> bool) (player : Player) : HashSet<'T> =     
        let counterDict = new Dictionary<'T, Counter>()

        let attractor = new HashSet<'T>()
        let queue = new Queue<'T>()

        for s in currentArea do 
            let sucs, _, _, _ = pg.Properties.[s]
            // Count how many successors are contained in relevant. If all are in the attractor, we add the current state
            let count =     
                sucs 
                |> seq
                |> Seq.filter (fun x -> currentArea.Contains x)
                |> Seq.length
                
            counterDict.Add(s, new Counter(count))

            if target s then 
                queue.Enqueue s 
                attractor.Add s |> ignore

        while queue.Count <> 0 do 
            let s = queue.Dequeue() 
            for s' in predMap.[s] do 
                if currentArea.Contains s' then 
                    let _, _, p, _ = pg.Properties.[s']

                    if p = player then 
                        if attractor.Contains s' |> not then 
                            attractor.Add s' |> ignore
                            queue.Enqueue s'
                    else
                        // Controlled by the adversary 
                        counterDict.[s'].Dec()
                        if counterDict.[s'].Get = 0 then
                            // All edges point to winning region so we can add it 
                            if attractor.Contains s' |> not then 
                                attractor.Add s' |> ignore
                                queue.Enqueue s'

        attractor

    let rec solveRec (currentArea : HashSet<'T>)= 
        // Compute the max Colour of all remaining states
        let mutable maxColour = 0 
        for s in currentArea do 
            let _, _, _, c = pg.Properties.[s]
            if c > maxColour then 
                maxColour <- c 

        if maxColour = 0 then 
            // Won from all states 
            [(SYSTEM, new HashSet<_>(currentArea)); (ENV, new HashSet<_>())]
            |> Map.ofList
        else 
            let nodesWithColour = new HashSet<_>()

            for s in currentArea do 
                let _, _, _, c = pg.Properties.[s]
                if c = maxColour then 
                    nodesWithColour.Add s |> ignore

            let player = if maxColour % 2 = 0 then SYSTEM else ENV 

            let atc = 
                computeAttractor currentArea 
                    (fun x -> 
                        let _, _, _, c = pg.Properties.[x]
                        c = maxColour
                    )
                    player
            
            // Compute subgame
            for s in atc do 
                currentArea.Remove s |> ignore

            let w = solveRec currentArea

            // After solving add all states again
            for s in atc do 
                currentArea.Add s |> ignore
            
            if w.[player.Flip].Count = 0 then 
                [(player, new HashSet<_>(currentArea)); (player.Flip, new HashSet<_>())]
                |> Map.ofList
            else
                // Compute the second attractor
                let atc2 = 
                    computeAttractor currentArea  (fun x -> w.[player.Flip].Contains x) player.Flip

                for s in atc2 do 
                    currentArea.Remove s |> ignore

                let w' = solveRec currentArea

                // After solving add all states again
                for s in atc2 do 
                    currentArea.Add s |> ignore

                let tmp = w'.[player.Flip]

                for s in atc2 do 
                    tmp.Add s |> ignore

                [(player, w'.[player]); (player.Flip, tmp)]
                |> Map.ofList

    solveRec (new HashSet<_>(pg.Properties.Keys))

type private PGState<'Tstate, 'Astate> =  
    | Regular of list<'Tstate> * list<'Tstate> * 'Astate
    | Chosen of list<'Tstate> * list<'Tstate> * 'Astate
    | Init of list<'Tstate>


/// Given a list of systems, and a DPA compile to the parity game used during SBV
let private compileToPG<'Tstate, 'Astate, 'L when 'Tstate : comparison and 'Astate : comparison and 'L : comparison> (tslist :  list<TransitionSystem<'Tstate, 'L>>) (k, l) (aut : DPA<'Astate, 'L * int>) = 
    // Given the correct number of systems
    assert (tslist.Length = k + l)

    // Compute the AP alignment
    // To make fast lookups this record the position in the list of aps for each ap
    // For each atomic proposition record the which copy and which copy within that position we refer to
    let autApMapping = 
        aut.APs
        |> List.map (fun (l, i) -> i, tslist.[i].APs |> List.findIndex (fun x -> x = l))
        |> List.toArray

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

    let queue = new Queue<_>()

    for ustate in initialUStates do 
        // The initial state fixes only those of the univ copies
        let s = Init(ustate)
        queue.Enqueue s
        visited.Add s |> ignore
        
        initalStates.Add s |> ignore

    let propertyDict = new Dictionary<_,_>()

    while queue.Count <> 0 do 
        let s = queue.Dequeue() 
        let sucs, info, p, c = 
            match s with 
                | Init ustates -> 
                    let sucs = new HashSet<_>()

                    for estates in initialEStates do 
                        let sucState = Regular(ustates, estates, aut.InitialState)
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

                    // #################### Compute the transition system successor for universal copies ####################

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
                        sucs.Add sucState |> ignore

                    let info = "Regular: " + ustates.ToString() + ", " + estates.ToString() + ", " + astate.ToString()
                    
                    sucs, info, ENV, aut.Colour.[astate]

                | Chosen(ustates, estates, astate) -> 
                    // #################### Compute the transition system successor for existential copies ####################

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
                        sucs.Add sucState |> ignore

                    let info = "Chosen: " + ustates.ToString() + ", " + estates.ToString() + ", " + astate.ToString()
                    
                    sucs, info, SYSTEM, aut.Colour.[astate]

        propertyDict.Add(s, (sucs, info, p, c))
        
        // Add to the queue if this is a new state
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


/// Check if a given list of system satisfies a HyperLTL property using SBV
let modelCheckSBV (tslist : list<TransitionSystem<'T, 'L>>) (prop : HyperLTL<'L>) timeout = 

    let swDPAConstruction = System.Diagnostics.Stopwatch()
    let swProduct = System.Diagnostics.Stopwatch()
    let swGameSolver = System.Diagnostics.Stopwatch()
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    let blockqf = LTL.extractBlocks prop.QuantifierPrefix
    // Strategy-based verification is only applicable for \forall^*\exists^* properties
    assert (blockqf.Length = 2)

    let k, l = blockqf.[0], blockqf.[1]
    
    // Convert to a DPA
    swDPAConstruction.Start()
    let mainAut = Converter.convertLTLToDPASpot prop.LTLMatrix timeout
    swDPAConstruction.Stop()

    let res = 
        mainAut
        |> ReturnOption.map (fun x -> 
            let mainAut = x.Result

            // Compile to a PG
            swProduct.Start()
            let pg = compileToPG tslist (k, l) mainAut
            swProduct.Stop()

            // Solve the PG
            swGameSolver.Start()
            let ws = solveParityGame pg
            swGameSolver.Stop()

            let isWon =
                pg.InitialStates
                |> Seq.forall (fun x -> ws.[SYSTEM].Contains x)

            sw.Stop()

            isWon
        )

    let t = 
        {
            LTL2DPATime = int (swDPAConstruction.ElapsedMilliseconds)
            ProductConstructionTime = int (swProduct.ElapsedMilliseconds)
            ParityGameSolvingTime = int(swGameSolver.ElapsedMilliseconds)
            TotalTime = int(sw.ElapsedMilliseconds)
        }

    res, t
