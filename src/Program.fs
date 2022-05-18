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

module Program

open System.IO

open LTL
open BitLanguage
open TransitionSystem
open CommandLineParser
open AutomatonBasedVerification
open PlotGenerator


let private verify (tslist : list<TransitionSystem<'T, string>>) (hyperltl : HyperLTL<string>) (m : Mode) timeout = 
    printfn "Started Verification with solver %s" m.AsString
    let res, t = AutomatonBasedVerification.modelCheckABV tslist hyperltl m timeout

    if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value)  then 
        if res.Get then 
            printfn "\n===== The property holds =====\n"
            printfn "Time %i" t.TotalTime
        else
            printfn "\n===== The property does NOT hold =====\n" 
            printfn "Time %i" t.TotalTime
    else 
        printfn "Timeout"


let private programVerification progpath hyperltlpath m  = 
    let sw = System.Diagnostics.Stopwatch()
    let totalsw = System.Diagnostics.Stopwatch()
    totalsw.Start()
    sw.Start()

    let hyperltlcontent = File.ReadAllText hyperltlpath 
    let progcontent = File.ReadAllText progpath 

    printfn "Read Input in: %ims" sw.ElapsedMilliseconds

    sw.Restart()

    let hyperltl = LTL.Parser.parseHyperltl Util.relVarParserBit hyperltlcontent
    let usedAps = hyperltl.LTLMatrix.AllAtoms |> Set.map fst |> Set.toList
    let prog = BitLanguage.Parser.parseProgram progcontent

    printfn "Parsed Input in: %ims" sw.ElapsedMilliseconds

    let relevantAps = 
        hyperltl.LTLMatrix.AllAtoms
        |> Set.map (fun (x, _) -> x)
        |> Set.toList

    assert (
        relevantAps
        |> List.forall (fun (v, i) -> 
            prog.DomainMap.ContainsKey v && prog.DomainMap.[v] > i
            ))

    sw.Restart()
    let ts = 
        BitLanguage.Compilation.compileProgramToTS prog relevantAps
        |> fun x -> x.ReplaceAPs (fun (n, i) -> n + "_" + string(i))

    printfn "Compiled Program to TS in: %ims" sw.ElapsedMilliseconds
    
    let tslist = List.init (hyperltl.QuantifierPrefix.Length) (fun _ -> ts)

    let hyperltl = 
        {
            HyperLTL.QuantifierPrefix = hyperltl.QuantifierPrefix
            HyperLTL.LTLMatrix = hyperltl.LTLMatrix.Map (fun ((n, i), j) -> n + "_" + string(i), j)
        }

    verify tslist hyperltl m


let private tsVerification tspath hyperltlpath m  = 
    let sw = System.Diagnostics.Stopwatch()
    sw.Start()

    let hyperltlcontent = File.ReadAllText hyperltlpath 
    let tscontent = File.ReadAllText tspath 

    printfn "Read Input in: %ims" sw.ElapsedMilliseconds

    sw.Restart()

    let hyperltl = LTL.Parser.parseHyperltl Util.relVarEscapedParser hyperltlcontent
    let ts = TransitionSystem.Parser.parseTS tscontent

    printfn "Parsed Input in: %ims" sw.ElapsedMilliseconds
    
    let tslist = List.init (hyperltl.QuantifierPrefix.Length) (fun _ -> ts)

    verify tslist hyperltl m


[<EntryPoint>]
let main args =
    
    let swtotal = System.Diagnostics.Stopwatch()
    swtotal.Start()
    
    // Parse the command line args
    let cmdArgs =
        match CommandLineParser.parseCommandLineArguments (Array.toList args) with
            | Ok x -> x
            | Error e ->
                   printfn "%s" e
                   exit 0
                   
    // By convention the config.conf file is located in the same directory as the HyPA executable
    // Get the path of the current binary
    let configPath = 
        System.IO.Path.GetDirectoryName(System.Reflection.Assembly.GetExecutingAssembly().Location) + "/config.conf"
                   
    // Check if the path to the config file is valid , i.e., the file exists
    if System.IO.FileInfo(configPath).Exists |> not then 
        printfn "The config.conf file does not exist in the same directory as the executable"
        exit 0               
    
    // Parse the config File
    let configContent = 
        try
            File.ReadAllText configPath
        with 
            | _ -> 
                printfn "Could not open config file"
                exit 0
           
    match CommandLineParser.parseConfigFile configContent with 
        | Ok x -> 
            if x.SpotPath.IsNone || x.BaitJarPath.IsNone || x.RabitJarPath.IsNone then
                printfn "The config.conf must specify the path to spot, rabit and bait"
                exit 0
               
            Util.spotPath <- x.SpotPath.Value
            Util.rabitJar <- x.RabitJarPath.Value
            Util.baitJar <- x.BaitJarPath.Value

            
            
            if Util.spotPath <> "" && (System.IO.DirectoryInfo(Util.spotPath).Exists |> not) then 
                printfn "The path to the spot directory is incorrect"
                exit 0
                
            if System.IO.FileInfo(Util.rabitJar).Exists |> not then 
                printfn "The path to the RABIT jar is incorrect"
                exit 0
                
            if System.IO.FileInfo(Util.baitJar).Exists |> not then 
                printfn "The path to the BAIT jar is incorrect"
                exit 0

        | Error r -> 
            printfn "%s" r
            exit 0
    
    // Check which method should be used, i.e., verify a program, verify a transition system or run a plotting experiment
    
    if cmdArgs.PropertyFile.IsSome && cmdArgs.ProgramFile.IsSome && cmdArgs.TSFile.IsNone && cmdArgs.Experiment.IsNone then
        // Check on a program
        let m = Option.defaultValue COMP cmdArgs.Mode
        
        programVerification cmdArgs.ProgramFile.Value cmdArgs.PropertyFile.Value m cmdArgs.Timeout
        
    elif cmdArgs.PropertyFile.IsSome && cmdArgs.TSFile.IsSome && cmdArgs.ProgramFile.IsNone && cmdArgs.Experiment.IsNone then
        // Check on a explicit TS
        let m = Option.defaultValue COMP cmdArgs.Mode
        
        tsVerification cmdArgs.TSFile.Value cmdArgs.PropertyFile.Value m cmdArgs.Timeout
    elif cmdArgs.Experiment.IsSome && cmdArgs.TSFile.IsNone && cmdArgs.ProgramFile.IsNone && cmdArgs.PropertyFile.IsNone then
        // Run an experiment
        
        let expName = cmdArgs.Experiment.Value
        
        if Map.containsKey expName PlotGenerator.experiments then
            // Run the experiment
            PlotGenerator.experiments.[expName] ()
        else
            printfn "The experiment \"%s\" does not exist." expName
            exit 0
    else
        printfn "The command line arguments are inconsistent. "
        exit 0
    
    swtotal.Stop()
    printfn "Entire execution took %is" (swtotal.ElapsedMilliseconds / 1000L)

    0
