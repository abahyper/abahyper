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

module TransitionSystem

open System.Collections.Generic


/// A Transition systems consist of a set of initial states,
/// a set of APs
/// and a Step function that maps each state to a set of successors and the evaluation of the APs
type TransitionSystem<'T, 'L when 'T : comparison and 'L : comparison> = 
    {
        InitialStates : HashSet<'T>
        APs : list<'L>
        Step : Dictionary<'T, HashSet<'T> * list<bool>>
    }

    /// Map a function on the list of APs
    member this.ReplaceAPs (f : 'L -> 'U) = 
        {
            InitialStates = this.InitialStates
            APs = this.APs |> List.map f
            Step = this.Step
        }

module Parser = 

    open FParsec 

    /// Parser for the AP evaluation at a given node
    let private apsatParser = 
        let trueParser = 
            charReturn 't' true 
        let falseParser = 
            charReturn 'f' false 
        skipChar '[' >>. spaces >>. many ((trueParser <|> falseParser) .>> spaces)  .>> spaces .>> skipChar ']'

    /// Parser for a single state in the system
    let private stateParser = 
        pstring "State:" >>.
            pipe3
                (spaces >>. pint32)
                (spaces >>. apsatParser)
                (spaces >>. many (pint32 .>> spaces))
                (fun id ap sucs -> (id, (new HashSet<_>(sucs), ap)))

    /// Parser for the body of a transition system
    let private bodyParser = 
        spaces >>. many (stateParser .>> spaces)
        |>> (fun x ->  
            let d = new Dictionary<_,_>()
            x 
            |> Seq.iter (fun (k, v) -> d.Add (k, v))
            d
        )

    /// Parser for the entire transition system
    let private tsParser = 
        pipe3
            (spaces >>. skipString "init" >>. spaces >>. many1 (pint32 .>> spaces))
            (spaces >>. skipString "aps" >>. spaces >>. many1 (Util.escapedStringParser .>> spaces))
            (spaces >>. skipString "--BODY--" >>. bodyParser)
            (fun init aps st -> 
                {
                    TransitionSystem.InitialStates = new HashSet<_>(init);
                    APs = aps;
                    Step = st
                }       
                )
    
    /// Given a string s, parse s into a transition system
    let parseTS (s: string) =
        let full = tsParser .>> spaces .>> eof
        let res = run full s
        match res with
            | Success (res, _, _) -> res
            | Failure (err, _, _) -> failwith err

module Random =
   
    /// Given a list of APs, a number of states, a transition density, and a count numberOfSamples, generate numberOfSamples many transition systems in the Erdős–Rényi–Gilbert model
    let computeRandomTS  (aps : list<'L>) numberOfStates transitionDensity (numberOfSamples : int) =
        
        /// Sample a single transition system in the Erdős–Rényi–Gilbert model
        let sampleTS()  = 
            // We always fix 0 as the unique initial state
            let initialStates = new HashSet<_>([0])

            let step = new Dictionary<_,_>()

            for n in 0..numberOfStates - 1 do
                // Each state is a successor with probability transitionDensity
                let sucs = 
                    [0..numberOfStates-1]
                    |> List.filter (fun _ -> Util.rnd.NextDouble() < transitionDensity)
                    
                // The evaluation of the APs is sampled uniformly
                let aps = 
                    List.init aps.Length (fun _ -> Util.rnd.NextDouble() < 0.5)

                
                step.Add(n, (new HashSet<_>(sucs), aps))

            // We ensure that each node has at least one successor so there are no finite paths in the system
            // If some node has no successor, we sample a uniform one
            for n in 0..numberOfStates - 1 do 
                let sucs, _ = step.[n]
                if sucs.Count = 0 then 
                    let s' = Util.rnd.Next(numberOfStates)
                    sucs.Add s' |> ignore


            // We have generated the random graph. To make sure it is connected, we connect all SCCs
            let mutable sccs = 
                SCC.computeSCC step.Keys (fun s -> step.[s] |> fst |> seq)
                |> List.map Set.toList
                
            
            let rec merge (sccids : int list) : unit = 
                // We compute a random permutation of the list of SCCs
                let randomsccids = List.sortBy (fun _ -> Util.rnd.Next()) sccids

                match randomsccids with 
                    | [] -> failwith ""
                    | [_] -> ()
                    | x::y::xs ->
                        // We add a edge between two random nodes of the first two SCCs
                        let i = Util.rnd.Next(sccs.[x].Length)
                        let j = Util.rnd.Next(sccs.[y].Length)

                        let sucs = step.[sccs.[x].[i]] |> fst
                        sucs.Add(sccs.[y].[j]) |> ignore
                        
                        // Recurse
                        merge (y::xs)

            // Connect all SCCs
            merge [0..sccs.Length - 1]

            {
                TransitionSystem.InitialStates = initialStates
                APs = aps 
                Step = step
            }

        // To generate numberOfSamples many systems, we just call sampleTS multiple times
        List.init numberOfSamples (fun _ -> sampleTS())