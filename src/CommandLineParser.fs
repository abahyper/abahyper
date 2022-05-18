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

module CommandLineParser

open System
open System.Threading
open FParsec

open Util
open AutomatonBasedVerification

/// A configuration file only includes the (absolute) path to the external tools
type Configuration = 
    {
        SpotPath: option<String>
        BaitJarPath: option<String>
        RabitJarPath: option<String>
    }

    static member Default = 
        {
            SpotPath = Option.None
            BaitJarPath = Option.None
            RabitJarPath = Option.None
        }

/// The command line parameters given to AbaHyper
type CommandLineArguments = 
    {
        PropertyFile : option<string>
        TSFile : option<string>
        ProgramFile : option<string>
        Experiment : option<string>
        Mode : option<AutomatonBasedVerification.Mode>
        Timeout : option<int>
    }

    static member Default = 
        {
            PropertyFile = Option.None
            TSFile = Option.None
            ProgramFile = Option.None
            Experiment = Option.None
            Mode = Option.None
            Timeout = Option.None
        }

/// Parse the content of the config file
let parseConfigFile (s : string) =
    let configUpdateParser (config: Configuration) =
        let spotParser =
            skipString "spot=" >>. spaces >>. Util.escapedStringParser
            |>> (fun s -> Result.Ok { config with SpotPath = Some s })
            
        let baitParser =
            skipString "bait=" >>. spaces >>. Util.escapedStringParser
            |>> (fun s -> Result.Ok { config with BaitJarPath = Some s })
            
        let rabitParser =
            skipString "rabit=" >>. spaces >>. Util.escapedStringParser
            |>> (fun s -> Result.Ok { config with RabitJarPath = Some s })

        spaces
        >>. choice 
            [ 
                spotParser
                baitParser
                rabitParser
            ]
        .>> spaces

    let rec configParser (config: Configuration) =
        (attempt (configUpdateParser config) 
            >>= (fun x -> 
                match x with 
                    | Result.Ok r -> configParser r
                    | Result.Error _ -> preturn x
                )
        )
        <|>% (Result.Ok config)

    let p =
        spaces >>. skipString "[paths]" >>. spaces >>. configParser Configuration.Default 

    match run p s with
        | Success (res, _, _) -> res
        | Failure (err, _, _) -> Result.Error "Parsing Error in Configuration File"
        


/// Parse the list of command line args for AbaHyper
let parseCommandLineArguments (args : list<String>) =
    let rec parseArgumentsRec (args : list<String>) (opt : CommandLineArguments) = 

        match args with 
            | [] -> Result.Ok opt
            | x::xs -> 
                match x with 
                    | "-prop" -> 
                        match xs with 
                            | [] -> 
                                Result.Error "Option -prop must be followed by an argument" 
                            | y::ys -> 
                                parseArgumentsRec ys {opt with PropertyFile = Some(y)}
                                
                    | "-prog" -> 
                        match xs with 
                            | [] -> 
                                Result.Error "Option -prog must be followed by an argument" 
                            | y::ys -> 
                                parseArgumentsRec ys {opt with ProgramFile = Some(y)}
                                
                    | "-ts" -> 
                        match xs with 
                            | [] -> 
                                Result.Error "Option -ts must be followed by an argument" 
                            | y::ys -> 
                                parseArgumentsRec ys {opt with TSFile = Some(y)}

                    | "-e" -> 
                        match xs with 
                            | [] -> 
                                Result.Error "Option -e must be followed by an argument" 
                            | y::ys -> 
                                parseArgumentsRec ys { opt with Experiment = Some y }
                       
                    | "-m" -> 
                        match xs with 
                            | [] -> 
                                Result.Error "Option -m must be followed by an argument" 
                            | y::ys -> 
                                try     
                                    match y with 
                                        | "comp" -> parseArgumentsRec ys { opt with Mode = Some COMP }
                                        | "incl_spot" -> parseArgumentsRec ys { opt with Mode = Some (INCLUSION SPOT) }
                                        | "incl_bait" -> parseArgumentsRec ys { opt with Mode = Some (INCLUSION BAIT) }
                                        | "incl_rabit" -> parseArgumentsRec ys { opt with Mode = Some (INCLUSION RABIT) }
                                        | _ -> Result.Error ("Unsupported Mode: " + y)
                                with _ -> Result.Error ("Unsupported Mode: " + y)
                                
                    | "-t" -> 
                        match xs with 
                            | [] -> 
                                Result.Error "Option -t must be followed by an argument" 
                            | y::ys -> 
                                try     
                                    let vl = System.Int32.Parse y
                                    parseArgumentsRec ys { opt with Timeout = Some vl }
                                with _ -> Result.Error ("Unsupported timeout: " + y)

                    | _ -> Result.Error ("Option " + x + " is not supported" )
        
    parseArgumentsRec args CommandLineArguments.Default
                                