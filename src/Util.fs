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

module Util 

open System

open FParsec

let rnd = new Random(0)


/// The path were intermediate files are written to
let mutable mainPath = "."

/// The path were the spot binaries are located
let mutable spotPath = ""

// The path to the BAIT Jar file
let mutable baitJar = ""

/// The path to the RABIT Jar file
let mutable rabitJar = ""


/// A custom type that is a mixture of Result and Option
type ReturnOption<'T, 'L> = 
    | Res of 'T
    | Msg of 'L
    | None

    member this.IsSome = 
        match this with 
            | Res x -> true
            | _ -> false

     member this.DefaultWith f  = 
        match this with 
            | Res x -> x
            | _ -> f()

    static member defaultWith f (x : ReturnOption<'T,'L>) = 
        x.DefaultWith f

    member this.Get  = 
        match this with 
            | Res x -> x
            | _ -> failwith ""

    static member get (x : ReturnOption<'T,'L>) = 
        x.Get

    member this.Map f = 
        match this with 
            | Res x -> Res (f x)
            | Msg e -> Msg e
            | None -> None

    static member map f (x : ReturnOption<'T,'L>) = 
        x.Map f


    member this.Bind f = 
        match this with 
            | Res x -> f x 
            | Msg e -> Msg e
            | None -> None

    static member bind f (x : ReturnOption<'T,'L>) = 
        x.Bind f


/// Trace quantifiers in a HyperLTL formula
type TraceQuantifierType = 
    | FORALL 
    | EXISTS

    member this.Flip = 
        match this with 
            | FORALL -> EXISTS
            | EXISTS -> FORALL

type Counter(init : int) =
    let mutable a = init

    new () = Counter(0)

    member this.Reset() =   
        a <- 0

    member this.Get = a

    member this.Inc() =
        a <- a + 1

    member this.Inc(x) =
        a <- a + x
    
    member this.Dec() =
        a <- a - 1

    member this.Dec(x) =
        a <- a - x


/// Given a number n, computes all lists of booleans of length n 
let rec computeBooleanPowerSet n =
    if n = 0 then
        Seq.singleton []
    else
        let r = computeBooleanPowerSet (n-1)
        Seq.append (Seq.map (fun x -> true::x) r) (Seq.map (fun x -> false::x) r)

/// Compute the cartesian product
let rec cartesianProduct (LL: list<seq<'a>>) =
    match LL with
    | [] -> Seq.singleton []
    | L :: Ls ->
        seq {
            for x in L do
                for xs in cartesianProduct Ls -> x :: xs
        }

/// Compute the powerset of a given set
let powerset (s : Set<'a>) =
    let asList = Set.toList s 

    let rec computeFiniteChoices (A : list<'a>) =
        match A with
            | [] -> Seq.singleton Set.empty
            | x::xs ->
                let r = computeFiniteChoices xs
                Seq.append r (Seq.map (fun y -> Set.add x y) r)

    computeFiniteChoices asList

let ordinal n =
    match if n > 20 then n % 10 else n % 20 with
    | 1 -> string n + "st"
    | 2 -> string n + "nd"
    | 3 -> string n + "rd"
    | _ -> string n + "th"

// ################################################################################################
// Parser for variables used in the specification


// Parses everything between two '"'
let escapedStringParser : Parser<string, unit> = 
    skipChar '\"' >>. manyChars (satisfy (fun c -> c <> '\"')) .>> skipChar '\"'    

// A parser for the LTL atoms encoutered during ordianry use
let relVarParser : Parser<string * int, unit> =
    pipe3
        (many1Chars letter)
        (skipChar '_')
        pint32
        (fun x _ y -> x, y)


// A parser for the LTL atoms encoutered during ordianry use
let relVarEscapedParser : Parser<string * int, unit> = 
    pipe3
        escapedStringParser
        (skipChar '_')
        pint32
        (fun x _ y -> x, y)


// A parser for the LTL atoms encoutered during ordianry use
let relVarParserBit : Parser<(string * int) * int, unit>= 
    pstring "{" >>. 
        pipe5
            (spaces >>. many1Chars letter)
            (pchar '_')
            (pint32 .>> pstring "}")
            (pchar '_')
            pint32
            (fun x _ y _ z -> ((x, y), z))


// ################################################################################################
// System Calls

let systemCall cmd arg timeout =
    let p = new System.Diagnostics.Process();
    p.StartInfo.RedirectStandardOutput <- true
    p.StartInfo.RedirectStandardError <- true
    p.StartInfo.UseShellExecute <- false
    p.StartInfo.FileName <- cmd
    p.StartInfo.Arguments <- arg
    p.Start() |> ignore 

    // Add a timeout if needed
    let a = 
        match timeout with 
            | Option.None -> 
                true
            | Some t -> 
                p.WaitForExit(t)

    if a then 
        let err = p.StandardError.ReadToEnd() 

        if err <> "" then 
            None
        else 

            let res = p.StandardOutput.ReadToEnd()

            p.Kill true

            Res res
    else 
        p.Kill true
        None



