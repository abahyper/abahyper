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

module AutomatonBasedVerification

open System.Collections.Generic

open Util
open TransitionSystem
open LTL
open BuchiAutomaton
open Converter

let private swComplement = System.Diagnostics.Stopwatch()
let private swProduct = System.Diagnostics.Stopwatch()
let private swInclusion = System.Diagnostics.Stopwatch()
let private swEmptiness = System.Diagnostics.Stopwatch()
let private swLTLtoNBA = System.Diagnostics.Stopwatch()

let private timeComplement = new List<_>()
let private timeProduct = new List<_>()

/// A summary of the time spend in each step
type TimeSummaryTotal = 
    {
        LTL2NBATime : int; // Time spent to convert the LTL to a NBA
        ProductTime : list<int>; // Time spent in each product construction
        InclusionTime : int; // Time spent on the final inclusion check
        ComplementationTime : list<int>; // Time spent on each complementation
        EmptinessTime : int; // Time spent to check emptiness
        TotalTime : int // Overall time taken
    }
    
    member this.ComplementationTimeSum = 
        this.ComplementationTime |> List.sum

    member this.ProductTimeSum = 
        this.ProductTime |> List.sum

    static member Zero = 
        {
            LTL2NBATime  = 0
            ProductTime = []
            InclusionTime = 0
            ComplementationTime = []
            EmptinessTime = 0
            TotalTime = 0
        }

    static member (+) (a : TimeSummaryTotal, b: TimeSummaryTotal) =
        {
            LTL2NBATime  = a.LTL2NBATime + b.LTL2NBATime
            ProductTime = a.ProductTime @ b.ProductTime
            InclusionTime = a.InclusionTime + b.InclusionTime
            ComplementationTime = a.ComplementationTime @ b.ComplementationTime
            EmptinessTime = a.EmptinessTime + b .EmptinessTime
            TotalTime = a.TotalTime + b.TotalTime
        }

    static member (/) (a : TimeSummaryTotal, b: int) =
        {
            LTL2NBATime  = a.LTL2NBATime / b
            ProductTime = a.ProductTime |> List.map (fun x -> x / b) 
            InclusionTime = a.InclusionTime /b
            ComplementationTime = a.ComplementationTime |> List.map (fun x -> x / b) 
            EmptinessTime = a.EmptinessTime / b
            TotalTime = a.TotalTime / b
        }

/// All possible inclusion checks supported
type InclusionAlgorithm = 
    | SPOT 
    | BAIT 
    | RABIT
    | BAITwSPOT // preprocess the symbolic automaton with SPOT and then use BAIT
    | RABITwSPOT // preprocess the symbolic automaton with SPOT and then use RABIT
    
    member this.AsString = 
        match this with 
            | SPOT -> "SPOT"
            | BAIT -> "BAIT"
            | RABIT-> "RABIT"
            | BAITwSPOT -> "BAIT + SPOT"
            | RABITwSPOT -> "RABIT + SPOT"

/// All modes that are supported
/// This is either pure complementation or language inclusion on the last step
type Mode = 
    | COMP 
    | INCLUSION of InclusionAlgorithm

    member this.AsString = 
        match this with 
            | COMP -> "Comp"
            | INCLUSION a -> "Incl (" + a.AsString + ")"


/// Given a list of systems and a matching list of relevant propositions, construct an NBA that accepts the self composition of the system
let private constructAutomatonProduct (tslist : list<TransitionSystem<'T, 'L>>) (interestingAps : list<list<'L>>) = 
    // Assert that all interesting aps are also aps in the transition system
    assert(
        tslist
        |> List.map (fun x -> x.APs )
        |> List.zip interestingAps
        |> List.forall (fun (a, b) -> 
            a
            |> List.forall (fun x -> List.contains x b)
            )
        )

    let apMapping = 
        interestingAps
        |> List.mapi (fun i aplist -> 
            aplist
            |> List.map (fun a -> a, List.findIndex (fun a' -> a = a') tslist.[i].APs )
            |> Map.ofList
        )

    let allStates = 
        tslist
        |> List.map (fun x -> x.Step.Keys |> seq)
        |> Util.cartesianProduct
        |> set

    // The aps are the interesting ones indexed by their position
    let combinedAps = 
        interestingAps
        |> List.mapi (fun i x -> 
            x
            |> List.map (fun c -> c, i)
            )
        |> List.concat
    
    let allInitStates =
        tslist
        |> List.map (fun x -> x.InitialStates |> seq)
        |> Util.cartesianProduct
        |> set

    // For each product state the outgoing transitions are exactly guarded by the AP eval in the current state 
    let newStep = 
        allStates
        |> Set.map (fun tstates -> 
            let guard = 
                tstates
                |> List.mapi (fun i x -> 
                    let apEval = tslist.[i].Step.[x] |> snd

                    interestingAps.[i]
                    |> List.map (fun  a -> 
                        let b = apEval.[apMapping.[i].[a]]
                        let newApIndex = List.findIndex (fun c -> c = (a, i)) combinedAps
                        if b then BooleanCombination.Atom newApIndex else BooleanCombination.Neg (BooleanCombination.Atom newApIndex)

                        )
                    |> BooleanCombination<_>.constructAnd
                )
                |> BooleanCombination<_>.constructAnd

            let possibleSucs = 
                tstates
                |> List.mapi (fun i x -> tslist.[i].Step.[x] |> fst |> seq)
                |> Util.cartesianProduct
                |> Seq.toList
        
            let sucEntry = 
                possibleSucs
                |> List.map (fun x -> guard, x)
        
            tstates, sucEntry
            
        )
        |> Map.ofSeq

    {
        NBA.States = allStates
        InitialStates = allInitStates
        APs = combinedAps
        Step = newStep
        AcceptingStates = allStates
    }

/// Given a list of systems, check if their self composition is contained in a given NBA
let private inclusionTest (tslist : list<TransitionSystem<'Tstate, 'L>>) (aut : NBA<int, 'L * int>) a timeout = 

    // Map each index to the APs that are used by aut at that position
    let automatonAps = 
        aut.APs
        |> List.groupBy snd
        |> List.map (fun (i, l) -> i, List.map fst l)
        |> Map.ofList

    // Make sure that the automaton only references the position at most |tslist| - 1
    assert(automatonAps.Keys.Count = 0 || automatonAps.Keys |> seq |> Seq.max <= tslist.Length - 1)

    assert(
        automatonAps 
        |> Map.toSeq
        |> Seq.forall (fun (i, aps) -> aps |> List.forall (fun x -> List.contains x tslist.[i].APs))
    )

    // Compute an NBA that represent the product of the ts lists
    let product = 
        constructAutomatonProduct tslist ([0..tslist.Length - 1] |> List.map (fun x -> if automatonAps.ContainsKey x then automatonAps.[x] else [] ))
        |> (fun x -> x.ConvertStatesToInt())

    swInclusion.Start()
    // Check the containment using the algorithm that is required
    let res = 
        match a with 
            | SPOT -> 
                Converter.checkNBAContainmentSpot product aut timeout
            | BAIT -> 
                Converter.checkNBAContainmentBait product aut timeout
            | RABIT -> 
                Converter.checkNBAContainmentRabit product aut timeout
            | BAITwSPOT -> 
                Converter.simplifyNBAtoNBASpot product timeout
                |> ReturnOption.bind (fun x -> 
                    let product', t1 = x.AsPair
                    Converter.simplifyNBAtoNBASpot aut timeout
                    |> ReturnOption.bind (fun x -> 
                        let aut', t2 = x.AsPair
                        Converter.checkNBAContainmentBait product' aut' timeout
                        |> ReturnOption.map (fun x -> 
                            let r, t3 = x.AsPair

                            {
                                SystemCallResult.Result = r 
                                SystemCallResult.Time = t1 + t2 + t3
                            }
                        )
                    )
                )

            | RABITwSPOT -> 
                Converter.simplifyNBAtoNBASpot product timeout
                |> ReturnOption.bind (fun x -> 
                    let product', t1 = x.AsPair
                    Converter.simplifyNBAtoNBASpot aut timeout
                    |> ReturnOption.bind (fun x -> 
                        let aut', t2 = x.AsPair
                        Converter.checkNBAContainmentRabit product' aut' timeout
                        |> ReturnOption.map (fun x -> 
                            let r, t3 = x.AsPair

                            {
                                SystemCallResult.Result = r 
                                SystemCallResult.Time = t1 + t2 + t3
                            }
                        )
                    )
                )
    swInclusion.Stop()
    res


/// Recursive model checker for HyperLTL
/// We give the list of systems, the quantifier prefix in the block-format, the automaton constructed so far, a boolean flag that indicates if the automaton is negated so we return the opposite result,
/// the method to be used and the timeout
let rec private modelCheckComplementationRec (tslist : list<TransitionSystem<'Tstate, 'L>>) (qf : list<int>) (isNegated : bool) (aut : NBA<int, 'L * int>) m timeout = 

    // System Length and Formula Length Agree
    assert (tslist.Length = List.sum qf)

    if qf.Length = 0 then
        // The prefix is empty so we can directly check emptiness of aut
        assert (aut.APs.Length = 0)

        swEmptiness.Start()

        let isNotEmpty = 
            Converter.isNbaEmptyDFS aut 
            |> ReturnOption.map ( fun x -> not x.Result) 
        swEmptiness.Stop()
        
        // If negated we return the opposite result
        if isNegated then 
            ReturnOption.map not isNotEmpty
        else 
            isNotEmpty
            
    elif (match m with INCLUSION _ -> true | _ -> false) && qf.Length = 1 then
        // We use inclusion checks and the prefix contains only universal quantifiers (this is a global assumption)
        
        if isNegated then
            // In this case it is impossible that the automaton is negated as AbaHyper does not support alternation-free formulas
            failwith "This was a \forall^* property. better ways to model check"

        let a = match m with INCLUSION a -> a | _ -> failwith ""
        swInclusion.Start()
        let res = 
            inclusionTest tslist aut a timeout
            |> ReturnOption.map ( fun x -> x.Result) 
        swInclusion.Stop()

        res
    else
        // Determine what the type of the last quantifier is by checking the parity of the length of the prefix
        let lastQunatifierType = if qf.Length % 2 = 1 then FORALL else EXISTS

        // We need to complement the automaton if it is negated and we have exintial qunatfication or if it is non-negated and we have universal qunatification
        let needsComplement = (lastQunatifierType = EXISTS && isNegated) || (lastQunatifierType = FORALL && not isNegated)

        // If needed, complement the automaton
        let possiblyNegatedAut = 
            if needsComplement then 
                swComplement.Restart()
                let r = 
                    Converter.complementNBASpot aut timeout
                    |> ReturnOption.map ( fun x -> x.Result) 

                swComplement.Stop()
                timeComplement.Add (int swComplement.ElapsedMilliseconds)
                r
            else 
                Res aut
        
        // Compute the indices at which we start the projection
        let projStartIndex = qf[0..qf.Length-2] |> List.sum 
        let projEndIndex = List.sum qf - 1

        possiblyNegatedAut
        |> ReturnOption.bind (fun possiblyNegatedAut->
            // project the automaton on the transition systems
            swProduct.Restart()
            let nextAut =  
                ProductConstruction.constructAutomatonSystemProduct  possiblyNegatedAut tslist[projStartIndex..projEndIndex] [projStartIndex..projEndIndex]
                |> (fun x -> x.Result.ConvertStatesToInt())
            swProduct.Stop()
            timeProduct.Add(int swProduct.ElapsedMilliseconds)

            let isNegated = if lastQunatifierType = FORALL then true else false

            // Recurse with the remaining prefix. The automaton is negated iff the last qunatifier was \forall
            modelCheckComplementationRec tslist[0..projStartIndex-1] qf[0..qf.Length-2] isNegated nextAut m timeout
        )
    
// Check if a given list of system satisfies a block HyperLTL property. Performs the preprocessing and the calls the recursive checker
let private modelCheckInit (tslist : list<TransitionSystem<'T, 'L>>) (prop : BlockHyperLTL<'L>) (m : Mode) timeout = 
    // System Length and Formula Length Agree
    assert (tslist.Length = List.sum prop.QuantifierPrefix)

    let lastQunatifierType = if prop.QuantifierPrefix.Length % 2 = 1 then FORALL else EXISTS

    // If the innermost qunatifier is \forall, we include te first negation into the LTL property to safe one automaton complementation
    let mutable isNegated = 
        if lastQunatifierType = EXISTS then 
            false
        else 
            true

    // Construct a NBA from the LTl matrix (is needed, work on the negated matrix to save one complementation)
    swLTLtoNBA.Start()
    let mutable currentNBA =
        let f =    
            if lastQunatifierType = EXISTS then 
                prop.LTLMatrix
            else 
                LTL.Not (prop.LTLMatrix)
        Converter.convertLTLtoNBASpot f timeout
        |> ReturnOption.map ( fun x -> x.Result) 
    swLTLtoNBA.Stop()
    
    currentNBA
    |> ReturnOption.bind (fun currentNBA ->
        modelCheckComplementationRec tslist prop.QuantifierPrefix isNegated currentNBA m timeout
    )
    
    
// Check if a given list of system satisfies a HyperLTL property using a given method.
let modelCheckABV (tslist : list<TransitionSystem<'T, 'L>>) (prop : HyperLTL<'L>) m timeout = 
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    swLTLtoNBA.Reset()
    swEmptiness.Reset()
    swInclusion.Reset()
    swProduct.Reset()
    swComplement.Reset()

    timeComplement.Clear()
    timeProduct.Clear()
    
    // Convert the prefix to a block prefix
    let blockPrefix = extractBlocks prop.QuantifierPrefix

    // If the outermost quantifier is \exists, we negate everything so we can always work with a property starting with a \forall quantifier
    let shouldNegate = if prop.QuantifierPrefix.[0] = EXISTS then true else false

    let matrix = 
        if shouldNegate then 
            LTL.Not prop.LTLMatrix
        else 
            prop.LTLMatrix

    let blockProp = 
        {
            BlockHyperLTL.QuantifierPrefix = blockPrefix;
            LTLMatrix = matrix
        }

    let res = modelCheckInit tslist blockProp m timeout

    let res = 
        if shouldNegate then 
            ReturnOption.map not res
        else 
            res

    sw.Stop()
    
    let t = 
        {
            TotalTime = int(sw.ElapsedMilliseconds)
            LTL2NBATime = int(swLTLtoNBA.ElapsedMilliseconds)
            ProductTime = timeProduct |> seq |> Seq.toList
            InclusionTime = int(swInclusion.ElapsedMilliseconds)
            ComplementationTime = timeComplement |> seq |> Seq.toList
            EmptinessTime = int(swEmptiness.ElapsedMilliseconds)
        }

    res, t
