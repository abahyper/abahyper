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

module Converter 

open System.IO
open System.Collections.Generic

open Util
open BuchiAutomaton
open LTL

let private swIO = System.Diagnostics.Stopwatch()
let private swTool = System.Diagnostics.Stopwatch()
let private swHOA = System.Diagnostics.Stopwatch()



/// Collects the time taken by IO operations, the actual tool and the HOA parsing time
type TimeCollection = 
    {
        IOTime : int;
        ToolTime : int;
        HOATime : int
    }

    static member Zero = 
        {
        IOTime = 0
        ToolTime = 0
        HOATime = 0
        }

    member this.Time = 
        this.ToolTime

    static member (+) (a : TimeCollection, b: TimeCollection) =
        {
            IOTime = a.IOTime + b.IOTime;
            ToolTime = a.ToolTime + b.ToolTime;
            HOATime = a.HOATime + b.HOATime;
        }

/// The result of the system call together with the time information
type SystemCallResult<'T> = 
    {
        Result : 'T;
        Time : TimeCollection
    }

    member this.AsPair = 
        this.Result, this.Time

    static member Map f x = 
        {
            Result = f (x.Result);
            Time = x.Time
        }

/// Simplifies the NBA by calling spots autfilt
let simplifyNBAtoNBASpot (nba : NBA<'T, 'L>) timeout = 
    swIO.Restart()
    let sw = new StringWriter() 
    nba.WriteHoaFormat(sw)
    let s = sw.ToString() 
    let path = Util.mainPath + "/ymp.txt"
    File.WriteAllText(path, s)

    swIO.Stop()

    let arg = "--small --high -S -C -b " + path
    swTool.Restart()
    let res = Util.systemCall (Util.spotPath + "autfilt") arg timeout
    swTool.Stop()

    res 
    |> ReturnOption.map (fun res ->
        swHOA.Restart()
        // Parse the automaton returned by spot and convert to a NBA
        let hoa = HoaParser.Parser.parseHoaAutomaton res
        let nba' = HoaParser.Converter.convertToNba hoa
        
        let newAps =
            nba'.APs
            |> List.map (fun x -> List.find (fun y -> x = string y ) nba.APs)

        let resNBA = 
            {
                NBA.States = nba'.States
                InitialStates = nba'.InitialStates
                Step = nba'.Step
                AcceptingStates = nba'.AcceptingStates
                APs = newAps
            }
        swHOA.Stop()
        {
            SystemCallResult.Result = resNBA;
            SystemCallResult.Time = 
                {
                    IOTime = int(swIO.ElapsedMilliseconds);
                    ToolTime = int(swTool.ElapsedMilliseconds)
                    HOATime = int(swHOA.ElapsedMilliseconds)
                }
        }
    )

/// Complements an automaton using spot
let complementNBASpot (nba : NBA<'T, 'L>) timeout = 
    swIO.Restart()
    let sw = new StringWriter() 
    nba.WriteHoaFormat(sw)
    let s = sw.ToString() 
    let path = Util.mainPath + "/ymp.txt"
    File.WriteAllText(path, s)
    swIO.Stop()

    let arg = "--small --high -S -C -b --complement " + path

    swTool.Restart()
    let res = Util.systemCall (Util.spotPath + "autfilt") arg timeout
    swTool.Stop()

    res 
    |> ReturnOption.map (fun res ->
        swHOA.Restart()
        let hoa = HoaParser.Parser.parseHoaAutomaton res
        let nba' = HoaParser.Converter.convertToNba hoa

        let newAps =
            nba'.APs
            |> List.map (fun x -> List.find (fun y -> x = string y ) nba.APs)

        let resNBA = 
            {
                NBA.States = nba'.States
                InitialStates = nba'.InitialStates
                Step = nba'.Step
                AcceptingStates = nba'.AcceptingStates
                APs = newAps
            }
        swHOA.Stop()

        {
            SystemCallResult.Result = resNBA;
            SystemCallResult.Time = 
                {
                    IOTime = int(swIO.ElapsedMilliseconds);
                    ToolTime = int(swTool.ElapsedMilliseconds)
                    HOATime = int(swHOA.ElapsedMilliseconds)
                }
        }
    )

/// Convert a LTL formula to a NBA using spot
let convertLTLtoNBASpot<'L when 'L: comparison> (ltl : LTL<'L>) timeout  = 
    swIO.Restart()
    // Replace the APs so that spot can handle them
    let dict = new Dictionary<_,_>()
    let revdict = new Dictionary<_,_>()
    let mutable currentCount = 0
    
    // We rename the APs in the LTL formula so spot can parse them properly
    for a in ltl.AllAtoms do 
        dict.Add(a, "a" + string(currentCount))
        revdict.Add("a" + string(currentCount), a)
        currentCount <- currentCount + 1

    let simplifiedLtl = ltl.Map (fun x -> dict.[x])
    let ltlAsString = simplifiedLtl.Print id 
    swIO.Stop()
    let args = " -S -C -b \"" + ltlAsString + "\""

    swTool.Restart()
    let res = Util.systemCall (Util.spotPath + "ltl2tgba") args timeout
    swTool.Stop()

    res
    |> ReturnOption.map (fun res -> 
        swHOA.Restart()
        let hoaAut = HoaParser.Parser.parseHoaAutomaton res
        let nba = HoaParser.Converter.convertToNba hoaAut
        
        // Switch bak to the original APs
        let convertedNba = nba.ReplaceAPs (fun x -> revdict.[x])
        swHOA.Stop()

        {
            SystemCallResult.Result = convertedNba;
            SystemCallResult.Time = 
                {
                    IOTime = int(swIO.ElapsedMilliseconds);
                    ToolTime = int(swTool.ElapsedMilliseconds)
                    HOATime = int(swHOA.ElapsedMilliseconds)
                }
        }

    )

/// Convert a LTL formula to a DPA using spot
let convertLTLToDPASpot (ltl : LTL<'L>) timeout  = 
    swIO.Restart()
    // Replace the APs so that spot can handle them
    let dict = new Dictionary<_,_>()
    let revdict = new Dictionary<_,_>()
    let mutable currentCount = 0
    
    // We rename the APs in the LTL formula so spot can parse them properly
    for a in ltl.AllAtoms do 
        dict.Add(a, "a" + string(currentCount))
        revdict.Add("a" + string(currentCount), a)
        currentCount <- currentCount + 1

    let simplifiedLtl = ltl.Map (fun x -> dict.[x])
    let ltlAsString = simplifiedLtl.Print id 
    swIO.Stop()

    let args = " -D -p\"max even\" -S -C \"" + ltlAsString + "\""

    swTool.Restart()
    let res = Util.systemCall (Util.spotPath + "ltl2tgba") args timeout
    swTool.Stop()

    res
    |> ReturnOption.map (fun res -> 
        swHOA.Restart()
        let hoaAut = HoaParser.Parser.parseHoaAutomaton res
        let dpa = HoaParser.Converter.convertToDpa hoaAut
        // Switch bak to the original APs
        let convertedDpa = dpa.ReplaceAPs (fun x -> revdict.[x])
        swHOA.Stop()

        {
            SystemCallResult.Result = convertedDpa;
            SystemCallResult.Time = 
                {
                    IOTime = int(swIO.ElapsedMilliseconds);
                    ToolTime = int(swTool.ElapsedMilliseconds)
                    HOATime = int(swHOA.ElapsedMilliseconds)
                }
        }
    )

/// Check if a NBA is empty using spot
let isNbaEmptySpot (nba : NBA<'T, 'L>) timeout = 
    swIO.Restart()
    let sw = new StringWriter() 
    nba.WriteHoaFormat(sw)
    let s = sw.ToString() 
    let path = Util.mainPath + "/ymp.txt"
    File.WriteAllText(path, s)
    swIO.Stop()

    let args = "--is-empty " + path

    swTool.Restart()
    let res = Util.systemCall (Util.spotPath + "autfilt") args timeout

    swTool.Stop()

    res 
    |> ReturnOption.map (fun res -> 
        let resBool = 
            if res.Length = 0 then 
                // Automaton was filtered out, so is non empty
                false
            else
                true
            
        {
            SystemCallResult.Result = resBool;
            SystemCallResult.Time = 
                {
                    IOTime = int(swIO.ElapsedMilliseconds);
                    ToolTime = int(swTool.ElapsedMilliseconds)
                    HOATime = 0
                }
        }

        )

// Exception used to exit loops
exception private Found

/// Check if an NBA is empty using nested DFS
let isNbaEmptyDFS (nba : NBA<'T, 'L>) = 
    swTool.Restart()
    let U = new HashSet<_>()
    let V = new HashSet<_>()

    let pi = new Stack<_>()
    let e = new Stack<_>()

    let postMap = new Dictionary<_,_>()

    for s in nba.States do 
        let sucs = 
            nba.Step.[s]
            |> List.filter (fun (g, _) -> g.IsSat())
            |> List.map snd 
            |> set

        postMap.Add(s, new HashSet<_>(sucs))

    let cycleCheck s =  
        try
            e.Push s
            while e.Count <> 0 do 

                let s' = e.Peek()
                if postMap.[s'].Contains s then 
                    raise Found
                else 
                    if postMap.[s'].IsSubsetOf V |> not then
                        let s'' = postMap.[s'] |> seq |> Seq.find (fun x -> V.Contains x |> not)
                        V.Add s'' |> ignore 
                        e.Push s''
                    else 
                        e.Pop() |> ignore
            false
        with 
            | Found -> 
                true
            | _ -> reraise()

    let resBool = 
        try
            while nba.InitialStates |> Set.exists (fun x -> U.Contains x |> not) do

                let s0 = nba.InitialStates |> Set.toList |> List.find (fun x -> U.Contains x |> not)

                U.Add s0 |> ignore 
                pi.Push s0

                while pi.Count <> 0 do 
                    let s = pi.Peek()
                    if postMap.[s].IsSubsetOf U |> not then
                        let s' = postMap.[s] |> seq |> Seq.find (fun x -> U.Contains x |> not)
                        U.Add s' |> ignore 
                        pi.Push s'
                    else
                        pi.Pop() |> ignore
                        if nba.AcceptingStates.Contains s && cycleCheck s then 
                            raise Found

            true
        with 
            | Found -> 

                false 
            | _ -> reraise()
    
    swTool.Stop()

    {
            SystemCallResult.Result = resBool;
            SystemCallResult.Time = 
                {
                    IOTime = 0
                    ToolTime = int(swTool.ElapsedMilliseconds)
                    HOATime = 0
                }
        }
    |> Res


/// Given a set of NBAs we bring the so the same list of APs
let private bringNBAsToSameAps (autList : list<NBA<'T, 'L>>) =
    // The smallest set of Aps that contains every AP used by either automaton
    let combinedAps = 
        autList
        |> List.map (fun x -> x.APs)
        |> List.concat
        |> set 
        |> Set.toList

    // We remap the guards in the transitions to now work on the APs in combinedAps
    let finalNBA = 
        autList
        |> List.map (fun aut -> 
            let apAlignment i =
                List.findIndex (fun z -> z = aut.APs.[i]) combinedAps
            let newStep =
                aut.Step 
                |> Map.map (fun k x -> 
                    x 
                    |> List.map (fun (g, s) -> g.Map apAlignment, s)
                    )
            {aut with APs = combinedAps; Step = newStep}
            )

    finalNBA

/// Check automaton containment using BAIT
let checkNBAContainmentBait (nba1 : NBA<'T, 'L>) (nba2 : NBA<'T, 'L>) timeout = 
    swIO.Restart()
    let nba1, nba2 = 
        match bringNBAsToSameAps [nba1;nba2] with 
        | [a;b] -> a, b
        | _ -> failwith ""

    // Convert both to an explicit NBA
    let enba1 = BuchiAutomaton.convertToExplicitNBA nba1
    let enba2 = BuchiAutomaton.convertToExplicitNBA nba2

    let alphMapper = new Dictionary<_,_>()
    let mutable currentId = 0
    for l in enba1.Alphabet do 
        alphMapper.Add(l, string(currentId))
        currentId <- currentId + 1

    let sw1 = new StringWriter() 
    enba1.WriteBaFormat (fun x -> alphMapper.[x]) sw1
    let s1 = sw1.ToString() 

    let sw2 = new StringWriter() 
    enba2.WriteBaFormat (fun x -> alphMapper.[x]) sw2
    let s2 = sw2.ToString() 

    let path1 = Util.mainPath + "/aut1.ba"
    let path2 = Util.mainPath + "/aut2.ba"

    File.WriteAllText(path1, s1)
    File.WriteAllText(path2, s2)

    swIO.Stop()

    let arg = "-jar " + Util.baitJar + " -a " + path1 + " -b " + path2

    swTool.Restart()
    // Call BAIT
    let res = Util.systemCall "java" arg timeout
    swTool.Stop()

    res
    |> ReturnOption.bind (fun res ->
        // Check BAITs output
        if res.Contains "Inclusion holds: true" then 
            {
                SystemCallResult.Result = true;
                SystemCallResult.Time = 
                    {
                        IOTime = int(swIO.ElapsedMilliseconds);
                        ToolTime = int(swTool.ElapsedMilliseconds)
                        HOATime = 0
                    }
            }
            |> Res
        elif res.Contains "Inclusion holds: false" then 
            {
                SystemCallResult.Result = false;
                SystemCallResult.Time = 
                    {
                        IOTime = int(swIO.ElapsedMilliseconds);
                        ToolTime = int(swTool.ElapsedMilliseconds)
                        HOATime = 0
                    }
            }
            |> Res
        else 
            printfn "Unexpected Output %s" res
            None
        )

/// Check automaton containment using RABIT
let checkNBAContainmentRabit (nba1 : NBA<'T, 'L>) (nba2 : NBA<'T, 'L>) timeout = 
    swIO.Restart()
    let nba1, nba2 = 
        match bringNBAsToSameAps [nba1;nba2] with 
        | [a;b] -> a, b
        | _ -> failwith ""

    // Convert both to a explicit 
    let enba1 = BuchiAutomaton.convertToExplicitNBA nba1
    let enba2 = BuchiAutomaton.convertToExplicitNBA nba2

    let alphMapper = new Dictionary<_,_>()
    let mutable currentId = 0
    for l in enba1.Alphabet do 
        alphMapper.Add(l, string(currentId))
        currentId <- currentId + 1
    
    let sw1 = new StringWriter() 
    enba1.WriteBaFormat (fun x -> alphMapper.[x]) sw1
    let s1 = sw1.ToString() 

    let sw2 = new StringWriter() 
    enba2.WriteBaFormat (fun x -> alphMapper.[x]) sw2
    let s2 = sw2.ToString() 

    let path1 = Util.mainPath + "/aut1.ba"
    let path2 = Util.mainPath + "/aut2.ba"

    File.WriteAllText(path1, s1)
    File.WriteAllText(path2, s2)

    swIO.Stop()

    let arg = "-jar " + Util.rabitJar + " " + path1 + " " + path2 + " -fast"

    swTool.Restart()
    let res = Util.systemCall "java" arg timeout
    swTool.Stop()
    res
    |> ReturnOption.bind (fun res -> 
        if res.Contains "Not included." then 
            {
                SystemCallResult.Result = false;
                SystemCallResult.Time = 
                    {
                        IOTime = int(swIO.ElapsedMilliseconds);
                        ToolTime = int(swTool.ElapsedMilliseconds)
                        HOATime = 0
                    }
            }
            |> Res
        elif res.Contains "Included." then 
            {
                SystemCallResult.Result = true;
                SystemCallResult.Time = 
                    {
                        IOTime = int(swIO.ElapsedMilliseconds);
                        ToolTime = int(swTool.ElapsedMilliseconds)
                        HOATime = 0
                    }
            }
            |> Res
        else 
            printfn "Unexpected Output by RABIT: |%s|" res
            None
        )

/// Check automaton containment using SPOT
let checkNBAContainmentSpot (nba1 : NBA<'T, 'L>) (nba2 : NBA<'T, 'L>) timeout = 

    swIO.Restart()
    let sw1 = new StringWriter() 
    nba1.WriteHoaFormat(sw1)
    let s1 = sw1.ToString() 

    let sw2 = new StringWriter() 
    nba2.WriteHoaFormat(sw2)
    let s2 = sw2.ToString() 

    let path1 = Util.mainPath + "/ymp.txt"
    let path2 = Util.mainPath + "/ymp2.txt"

    File.WriteAllText(path1, s1)
    File.WriteAllText(path2, s2)

    swIO.Stop()

    let arg = "--included-in=" + path2 + " " + path1

    swTool.Restart()
    let res = Util.systemCall (Util.spotPath + "autfilt") arg timeout
    swTool.Stop()

    res
    |> ReturnOption.map (fun res -> 
        let resBool = if res = "" then false else true
        {
            SystemCallResult.Result = resBool;
            SystemCallResult.Time = 
                {
                    IOTime = int(swIO.ElapsedMilliseconds);
                    ToolTime = int(swTool.ElapsedMilliseconds)
                    HOATime = 0
                }
        }
    )
    