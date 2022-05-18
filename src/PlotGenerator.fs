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

module PlotGenerator

open System
open System.Collections.Generic

open XPlot.Plotly

open Util

open AutomatonBasedVerification
open StrategyBasedVerification


type WhichSize = SYS | PROP


/// The color pallet used to plot graphs
type Color = 
    | C1 
    | C2
    | C3
    | C4
    | C5
    | C6
    | C7 
    | C8
    | C9

    member this.AsRGB = 
        match this with 
            | C1 -> (253, 127, 111)
            | C2 -> (126, 176, 213)
            | C3 -> (178, 224, 97)
            | C4 -> (189, 126, 190)
            | C5 -> (255, 181, 90)
            | C6 -> (255, 238, 101)
            | C7 -> (190, 185, 219)
            | C8 -> (253, 204, 229)
            | C9 -> (139, 211, 199)

    member this.AsRGBString = 
        let r, g, b = this.AsRGB
        "rgb(" + string(r) + "," + string(g) + "," + string(b) + ")"

    member this.AsRGBAString a = 
        let r, g, b = this.AsRGB
        "rgba(" + string(r) + "," + string(g) + "," + string(b) + "," + string(a) + ")"


/// Display the success rate of different solvers in either system or property size
let successPerSizeAndMode (w : WhichSize) sizesA sizeB density numberOfInstances modes timeout =  
    let prefix = [FORALL; EXISTS]

    let numberOfProps = 10
    let numberOfSystems = 10
    let numberOfAps = 5

    let aps = 
        [1..numberOfAps]
        |> List.map (fun i -> Array.create i 'a' |> System.String.Concat)

    let resultDict = new Dictionary<_,_>()
   
    for s in sizesA do 
        printfn "======= Working on size %i =======" s

        let propList =  
            match w with 
                | SYS -> 
                    LTL.Random.getRandomHyperLTLOneByOne prefix (sizeB, sizeB) aps numberOfInstances
                | PROP -> 
                    LTL.Random.getRandomHyperLTLOneByOne prefix (s, s) aps numberOfInstances

        let systemList = 
            match w with 
                | SYS -> 
                    TransitionSystem.Random.computeRandomTS aps s (density s) numberOfInstances
                | PROP -> 
                    TransitionSystem.Random.computeRandomTS aps sizeB (density sizeB) numberOfInstances

        let combinationsToBeChecked = List.zip systemList propList
        
        for mode in modes do
            printfn "Working on mode %A" mode

            let mutable current = 0
            let mutable time = []

            for ts, prop in combinationsToBeChecked do 
                Console.SetCursorPosition(0, Console.CursorTop)
                let percent = current * 100 / combinationsToBeChecked.Length
                current <- current + 1
                printf "%i%%" percent
                let tslist = List.init prefix.Length (fun _ -> ts)
                
                let res, t = AutomatonBasedVerification.modelCheckABV tslist prop mode timeout
                
                if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value) then 
                    time <- (Some t.TotalTime)::time
                else 
                    time <- Option.None::time

            Console.SetCursorPosition(0, Console.CursorTop)

            resultDict.Add((mode, s), time)

    let successDict = new Dictionary<_,_>()

    for s in sizesA do 
        for m in modes do 
            let r = resultDict.[(m, s)]

            let filtereR = 
                r
                |> List.filter Option.isSome
                |> List.map Option.get
                |> List.sort

            let successRate = (filtereR.Length * 100) / r.Length

            successDict.Add((m, s), successRate)
            
    let colors = [C1;C2;C3;C4;C5;C6;C7;C8;C9]

    let traces = 
        modes 
        |> List.mapi (fun i m -> 
            let y = 
                sizesA 
                |> List.map (fun s -> 
                    successDict.[(m, s)]
                    )

            let trace =
                Scatter(
                    x = sizesA,
                    y = y,
                    name = m.AsString,
                    line = Line(color = colors.[i].AsRGBAString 1.0 )
                )
            trace
        )

    let legendStyle = 
        Legend(
            orientation="h",
            yanchor="bottom",
            y=1.02,
            xanchor="right",
            x=1
        )

    let styledLayout =
        Layout(
            yaxis = Yaxis(showline = true, title = "%",zeroline=false),
            xaxis = Xaxis(showline = true, title = (match w with SYS -> "System Size" | PROP -> "Property Size"),zeroline = false),
            legend = legendStyle
        )

    let chart =
        traces
        |> Chart.Plot
        |> Chart.WithLayout styledLayout
        |> Chart.WithWidth 700
        |> Chart.WithHeight 500

    let chartHtml = chart.GetHtml()

    let p = 
        match w with 
            | SYS -> Util.mainPath + "/plots/successPerModeAndSystemSize.html"
            | PROP -> Util.mainPath + "/plots/successPerModeAndPropSize.html"

    System.IO.File.WriteAllText(p, chartHtml)

/// A survival plot for fixed system and property size
let survivalPerMode systemSize density propSize numberOfInstances modes timeout =  
    let prefix = [FORALL; EXISTS]

    let numberOfAps = 5

    let aps = 
        [1..numberOfAps]
        |> List.map (fun i -> Array.create i 'a' |> System.String.Concat)

    let propList = LTL.Random.getRandomHyperLTLOneByOne prefix propSize aps numberOfInstances

    let systemList = 
        TransitionSystem.Random.computeRandomTS aps systemSize density numberOfInstances

    let combinationsToBeChecked = List.zip systemList propList

    let resultDict = new Dictionary<_,_>()

    for mode in modes do
        printfn "====== Working on mode %A ======" mode
        
        let mutable current = 0
        let mutable timeResults = []
        
        for ts, prop in combinationsToBeChecked do 
            Console.SetCursorPosition(0, Console.CursorTop)
            let percent = current * 100 / combinationsToBeChecked.Length
            current <- current + 1
            printf "%i%%" percent

            let tslist = List.init prefix.Length (fun _ -> ts)
            
            let res, t = AutomatonBasedVerification.modelCheckABV tslist prop mode timeout 
            
            if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value) then 
                timeResults <- (Some t.TotalTime) :: timeResults
            else 
                timeResults <- Option.None :: timeResults

        Console.SetCursorPosition(0, Console.CursorTop)

        resultDict.Add((mode, systemSize), timeResults) 
    
    let colors = [C1;C2;C3;C4;C5;C6;C7;C8;C9]

    let traces = 
        modes 
        |> List.mapi (fun i m -> 
            // Get the results for each 
            let ordered = 
                resultDict.[(m, systemSize)]
                |> List.filter Option.isSome
                |> List.map Option.get
                |> List.sort

            let x = [1..ordered.Length]

            let y = 
                x
                |> List.map (fun i -> 
                    let ms = 
                        ordered.[0..i-1]
                        |> List.sum
                    ms
                )
                |> List.map double 
                |> List.map (fun x -> x / 1000.0) // Convert to seconds

            let trace =
                Scatter(
                    x = x,
                    y = y,
                    name = m.AsString,
                    line = Line(color = colors.[i].AsRGBAString 1.0)
                )
            trace
        )

    let legendStyle = 
        Legend(
            yanchor="top",
            y=0.99,
            xanchor="right",
            x=0.99
        )

    let styledLayout =
        Layout(
            xaxis = Xaxis(title = "# of Instances", showline = true, zeroline = false),
            yaxis = Yaxis(showline = true, title = "Time in s", zeroline = false),
            legend = legendStyle
        )

    let chart =
        traces
        |> Chart.Plot
        |> Chart.WithLayout styledLayout
        |> Chart.WithWidth 700
        |> Chart.WithHeight 500

    let chartHtml = chart.GetHtml()
    System.IO.File.WriteAllText(Util.mainPath + "/plots/survivalPerMode.html", chartHtml)


    
/// Plot success and median time of different modes
let successRateAndMedianTimePerSizeAndMode (w : WhichSize) sizesA sizeB density numberOfInstances modes timeout =  
    let prefix = [FORALL; EXISTS]
    let numberOfAps = 5

    let aps = 
        [1..numberOfAps]
        |> List.map (fun i -> Array.create i 'a' |> System.String.Concat)

    let resultDict = new Dictionary<_,_>()
   
    for s in sizesA do 
        printfn "======= Working on size %i =======" s
        let propList = 
            match w with 
                | SYS -> 
                    LTL.Random.getRandomHyperLTLOneByOne prefix (sizeB, sizeB) aps numberOfInstances
                | PROP -> 
                    LTL.Random.getRandomHyperLTLOneByOne prefix (s, s) aps numberOfInstances

        let systemList = 
            match w with 
                | SYS -> 
                    TransitionSystem.Random.computeRandomTS aps s (density s) numberOfInstances
                | PROP -> 
                    TransitionSystem.Random.computeRandomTS aps sizeB (density sizeB) numberOfInstances

        let combinationsToBeChecked = List.zip systemList propList
        
        for mode in modes do
            printfn "Working on mode %A" mode

            let mutable current = 0
            let mutable time = []

            for ts, prop in combinationsToBeChecked do 
                Console.SetCursorPosition(0, Console.CursorTop)
                let percent = current * 100 / combinationsToBeChecked.Length
                current <- current + 1
                printf "%i%%" percent

                let tslist = List.init prefix.Length (fun _ -> ts)
                
                let res, t = AutomatonBasedVerification.modelCheckABV tslist prop mode timeout
               
                if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value) then 
                    time <- (Some t.TotalTime)::time
                else 
                    time <- Option.None::time

            Console.SetCursorPosition(0, Console.CursorTop)

            resultDict.Add((mode, s), time)

    let successDict = new Dictionary<_,_>()
    let medianDict = new Dictionary<_,_>()

    for s in sizesA do 
        for m in modes do 
            let r = resultDict.[(m, s)]

            let filtereR = 
                r
                |> List.filter Option.isSome
                |> List.map Option.get
                |> List.sort

            let successRate = (filtereR.Length * 100) / r.Length

            let median, low, high = 
                if filtereR.IsEmpty then 
                    0, 0, 0
                else 
                    let midPos = filtereR.Length / 2
                    let lowPos = filtereR.Length / 4
                    let highPos = filtereR.Length * 3 / 4

                    filtereR.[midPos], filtereR.[lowPos], filtereR.[highPos]

            successDict.Add((m, s), successRate)
            medianDict.Add((m, s), (median, low, high))

    let colors = 
        [
            (C1.AsRGBAString 1.0,C5.AsRGBAString 1.0,C5.AsRGBAString 0.35, C5.AsRGBAString 0.3);
            (C2.AsRGBAString 1.0,C7.AsRGBAString 1.0,C7.AsRGBAString 0.45, C7.AsRGBAString 0.4);
        ]

    let successRateTraces = 
        modes 
        |> List.mapi (fun i m -> 
            let y = 
                sizesA 
                |> List.map (fun s -> 
                    successDict.[(m, s)]
                    )
            let c, _, _, _ = colors.[i]

            let trace =
                Scatter(
                    x = sizesA,
                    y = y,
                    name = m.AsString + " Success",
                    line = Line(color = c),
                    yaxis="y",
                    mode="lines+markers",
                    opacity=0.8
                )
            trace
        )

    let areaTraces = 
        modes 
        |> List.mapi (fun i m -> 
            let ymedian, ylow, yhigh = 
                sizesA 
                |> List.map (fun s -> 
                    medianDict.[(m, s)]
                    )
                |> List.unzip3
            
            let _, _, cborder, cfill = colors.[i]

            let areaTrace =
                Scatter(
                    x = sizesA @ List.rev sizesA,
                    y = yhigh @ List.rev ylow,
                    name = "a" + m.AsString,
                    fill="toself",
                    fillcolor=cfill,
                    showlegend=false,
                    line=Line(color = cborder),
                    yaxis="y2",
                    mode="lines"
                )
            areaTrace
        )

    let medianTraces = 
        modes 
        |> List.mapi (fun i m -> 
            let ymedian, _, _ = 
                sizesA 
                |> List.map (fun s -> 
                    medianDict.[(m, s)]
                    )
                |> List.unzip3

            let _, c, _, _ = colors.[i]

            let medianTrace =
                Scatter(
                    x = sizesA ,
                    y = ymedian,
                    name = m.AsString + " Time",
                    line = Line(color = c),
                    yaxis="y2",
                    mode="lines+markers",
                    opacity=0.8
                )
            medianTrace
        )
 
    let legendStyle = 
        Legend(
            orientation="h",
            yanchor="bottom",
            y=1.02,
            xanchor="right",
            x=1
        )

    let styledLayout =
        Layout(
            xaxis = Xaxis(showline = true, title = (match w with SYS -> "System Size" | PROP -> "Property Size"),zeroline = false, anchor = "x"),
            yaxis = Yaxis(showline = true, title = "%",zeroline=false),
            yaxis2 = Yaxis(showline = true, title = "Time in ms",zeroline=false, anchor = "x", overlaying="y", side = "right"),
            legend = legendStyle
        )
        
    let chart =
        successRateTraces @ medianTraces @ areaTraces
        |> Chart.Plot
        |> Chart.WithLayout styledLayout
        |> Chart.WithWidth 700
        |> Chart.WithHeight 500

    let chartHtml = chart.GetHtml()

    let p = 
        match w with 
            | SYS -> Util.mainPath + "/plots/successAndMedianTimePerModeAndSystemSize.html"
            | PROP -> Util.mainPath + "/plots/successAndMedianTimePerModeAndPropSize.html"

    System.IO.File.WriteAllText(p, chartHtml)
    


/// Compute survival plot for different number of quantifier alternations
let survivalPerAlternation systemSize density propSize alternations numberOfInstances  timeout =  
    
    let rec generatePrefixFromAlternation k = 
        if k = 1 then 
            [FORALL;EXISTS]
        else 
            let recRes = generatePrefixFromAlternation (k - 1)
            let q = recRes.[recRes.Length - 1]
            recRes @ [q.Flip]

    let numberOfAps = 3

    let aps = 
        [1..numberOfAps]
        |> List.map (fun i -> Array.create i 'a' |> System.String.Concat)

    let resultDict = new Dictionary<_,_>()

    for alternation in alternations do 
        printfn "===== Working on alternation %i =====" alternation

        let prefix = generatePrefixFromAlternation alternation

        let propList = LTL.Random.getRandomHyperLTLOneByOne prefix propSize aps numberOfInstances

        let systemList = 
            TransitionSystem.Random.computeRandomTS aps systemSize density numberOfInstances

        let combinationsToBeChecked = List.zip systemList propList

        let mutable current = 0
        let mutable timeResults = []
        
        for ts, prop in combinationsToBeChecked do 
            Console.SetCursorPosition(0, Console.CursorTop)
            let percent = current * 100 / combinationsToBeChecked.Length
            current <- current + 1
            printf "%i%%" percent

            let tslist = List.init prefix.Length (fun _ -> ts)
            
            let res, t = AutomatonBasedVerification.modelCheckABV tslist prop COMP timeout 
            
            if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value) then 
                timeResults <- (Some t)::timeResults
            else 
                timeResults <- Option.None :: timeResults

        Console.SetCursorPosition(0, Console.CursorTop)

        resultDict.Add(alternation, timeResults)

    let colors = [C1;C2;C3;C4]

    let traces = 
        alternations 
        |> List.mapi (fun i a -> 
            let ordered = 
                resultDict.[a]
                |> seq 
                |> Seq.filter Option.isSome
                |> Seq.map Option.get
                |> Seq.map (fun x -> x.TotalTime)
                |> Seq.sort
                |> Seq.toList
            
            let x = [1..ordered.Length]

            let y = 
                x
                |> List.map (fun i -> 
                    ordered.[0..i-1]
                    |> List.sum
                )
                |> List.map double 
                |> List.map (fun x -> x / 1000.0)

            let trace =
                Scatter(
                    x = x,
                    y = y,
                    name = (if a = 1 then string(a) + " Alternation" else string(a) + " Alternations"),
                    line = Line(color = colors.[i].AsRGBAString 1.0)
                )
            trace
        )

    let legendStyle = 
        Legend(
            yanchor="top",
            y=0.99,
            xanchor="left",
            x=0.01
        )

    let styledLayout =
        Layout(
            xaxis = Xaxis(title = "# of Instances", showline = true, zeroline = false),
            yaxis = Yaxis(title = "Time in s", showline = true, zeroline = false),
            legend = legendStyle
        )

    let chart =
        traces
        |> Chart.Plot
        |> Chart.WithLayout styledLayout
        |> Chart.WithWidth 700
        |> Chart.WithHeight 500

    let chartHtml = chart.GetHtml()
    System.IO.File.WriteAllText(Util.mainPath + "/plots/survivalPerAlternation.html", chartHtml)



/// Compute Bar plot for the time used with different number of quantifier alternations
let complementationCostPerAlternation systemSize density propSize alternations numberOfInstances  timeout =  
    
    let rec generatePrefixFromAlternation k = 
        if k = 1 then 
            [FORALL;EXISTS]
        else 
            let recRes = generatePrefixFromAlternation (k - 1)
            let q = recRes.[recRes.Length - 1]
            recRes @ [q.Flip]

    let numberOfAps = 3

    let aps = 
        [1..numberOfAps]
        |> List.map (fun i -> Array.create i 'a' |> System.String.Concat)

    let resultDict = new Dictionary<_,_>()

    for alternation in alternations do 
        printfn "===== Working on alternation %i =====" alternation

        let prefix = generatePrefixFromAlternation alternation

        let propList = LTL.Random.getRandomHyperLTLOneByOne prefix propSize aps numberOfInstances

        let systemList = 
            TransitionSystem.Random.computeRandomTS aps systemSize density numberOfInstances

        let combinationsToBeChecked = List.zip systemList propList

        let mutable current = 0
        let mutable timeResults = []
        
        for ts, prop in combinationsToBeChecked do 
            Console.SetCursorPosition(0, Console.CursorTop)
            let percent = current * 100 / combinationsToBeChecked.Length
            current <- current + 1
            printf "%i%%" percent

            let tslist = List.init prefix.Length (fun _ -> ts)
            
            let res, t = AutomatonBasedVerification.modelCheckABV tslist prop COMP timeout 
            
            if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value) then 
                timeResults <- (Some t)::timeResults
            else 
                timeResults <- Option.None :: timeResults

        Console.SetCursorPosition(0, Console.CursorTop)

        resultDict.Add(alternation, timeResults)

    let colors = [C1;C2;C3;C4]

    let numberOfCombs = List.max alternations

    let x = alternations

    let traces =    
        [0..numberOfCombs - 1]
        |> List.mapi (fun j i -> 
            let y = 
                alternations
                |> List.map (fun a -> 
                    let r = 
                        resultDict.[a]
                        |> List.filter Option.isSome
                        |> List.map Option.get
                        |> List.map (fun x -> if i < x.ComplementationTime.Length then x.ComplementationTime.[i] else 0)
                        

                    let res = (List.sum r) / r.Length
                    res
                    )

            let trace =
                Bar(
                    x = x,
                    y = y,
                    name = Util.ordinal(i+1) + " Complementation",
                    legendgroup="COMP",
                    marker = Marker(color = colors.[j].AsRGBAString 1.0)
                )

            trace
        )
    
    let legendStyle = 
        Legend(
            yanchor="top",
            y=0.99,
            xanchor="left",
            x=0.01
        )

    let styledLayout =
        Layout(
            xaxis = Xaxis(title = "Quantifier Alternations", showline = true, zeroline = false),
            yaxis = Yaxis(title = "Time in ms", showline = true, zeroline = false),
            barmode = "stack",
            legend = legendStyle
        )

    let chart =
        traces
        |> Chart.Plot
        |> Chart.WithLayout styledLayout
        |> Chart.WithHeight 700
        |> Chart.WithWidth 500

    let chartHtml = chart.GetHtml()

    System.IO.File.WriteAllText(Util.mainPath + "/plots/complementationTimePerAlternation.html", chartHtml)


/// Compute % of satsfiaction and success rate of SBV
let successRateOfABVandSBVAndPositiveRate propSize systemSizes density numberOfInstances  timeout timeoutSBV = 
    let prefix = [FORALL; EXISTS]

    let numberOfAps = 5

    let aps = 
        [1..numberOfAps]
        |> List.map (fun i -> Array.create i 'a' |> System.String.Concat)

    let resultDict = new Dictionary<_,_>()

    for systemSize in systemSizes do 
        let systemList =  TransitionSystem.Random.computeRandomTS aps systemSize (density systemSize) numberOfInstances
               
        let propList = LTL.Random.getRandomHyperLTLOneByOne prefix (propSize,propSize) aps numberOfInstances

        let combinationsToBeChecked = List.zip systemList propList
        
        printfn "======= Working on size %i =======" systemSize

        let mutable current = 0

        let mutable timeComp = []
        let mutable timeStrat = []
        
        for ts, prop in combinationsToBeChecked do 
            Console.SetCursorPosition(0, Console.CursorTop)
            let percent = current * 100 / combinationsToBeChecked.Length
            current <- current + 1
            printf "%i%%" percent

            let tslist = List.init prefix.Length (fun _ -> ts)
            
            let res, t = AutomatonBasedVerification.modelCheckABV tslist prop COMP timeout

            if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value) then 
                timeComp <-  (Some (res.Get, t))::timeComp
            else 
                timeComp <-  Option.None::timeComp

            let resStrat, tStrat = StrategyBasedVerification.modelCheckSBV tslist prop timeoutSBV

            if resStrat.IsSome && (timeoutSBV.IsNone || tStrat.TotalTime <= timeoutSBV.Value) then 
                timeStrat <- (Some (resStrat.Get, tStrat))::timeStrat
            else    
                timeStrat <- Option.None::timeStrat
                
           
        Console.SetCursorPosition(0, Console.CursorTop)

        resultDict.Add(systemSize, (timeComp, timeStrat))

    let solvedPerSize = new Dictionary<_,_>()
    let satPerSize = new Dictionary<_,_>()
    let SBVSucessPerSize = new Dictionary<_,_>()

    for s in systemSizes do 

        let rINCL, rSTRAT = resultDict.[s]

        let rINCLFiltered = 
            rINCL
            |> List.filter Option.isSome
            |> List.map Option.get

        let solvedRate = (rINCLFiltered.Length * 100) / rINCL.Length

        let rINCLFilteredPos = 
            rINCLFiltered
            |> List.filter (fun (x, _) -> x)

        let posRate =  (rINCLFilteredPos.Length * 100) / rINCLFiltered.Length

        let t = 
            rSTRAT
            |> List.filter Option.isSome
            |> List.map Option.get
            |> List.filter (fun (x, _) -> x) 

        let SBVsuccessRate =  (t.Length * 100) / rSTRAT.Length

        solvedPerSize.Add(s, solvedRate)
        satPerSize.Add(s, posRate)
        SBVSucessPerSize.Add(s, SBVsuccessRate)

    
    let traceSucessABV =
        Scatter(
            x = systemSizes,
            y = (systemSizes
                |> List.map (fun s -> 
                    solvedPerSize.[s]
                    )
                ),
            line = Line(color = C1.AsRGBAString 1.0),
            name = "% solved using ABV"
        )

    let tracePosRate =
        Scatter(
            x = systemSizes,
            y = (systemSizes
                |> List.map (fun s -> 
                    satPerSize.[s]
                    )
                ),
            line = Line(color = C2.AsRGBAString 1.0),
            name = "% of Satisfaction"
        )

    let traceSBVSuccRate =
        Scatter(
            x = systemSizes,
            y = (systemSizes
                |> List.map (fun s -> 
                    SBVSucessPerSize.[s]
                    )
                ),
            line = Line(color = C3.AsRGBAString 1.0),
            name = "% solved using SBV"
        )

    let legendStyle = 
        Legend(
            orientation="h",
            yanchor="bottom",
            y=1.02,
            xanchor="right",
            x=1
        )

    let styledLayout =
        Layout(
            xaxis = Xaxis(title = "System Size", showline = true, zeroline=false),
            yaxis = Yaxis(title = "%", showline = true, zeroline = false),
            legend = legendStyle
        )

    let chart =
        [traceSucessABV;tracePosRate;traceSBVSuccRate]
        |> Chart.Plot
        |> Chart.WithLayout styledLayout
        |> Chart.WithHeight 350
        |> Chart.WithWidth 1000

    let chartHtml = chart.GetHtml()

    let p = Util.mainPath + "/plots/ratiosPerSystemSize.html"

    System.IO.File.WriteAllText(p, chartHtml)

/// Compare the time taken by SBV and ABV on varying system or property size
let compareABVandSBVTimePerSize (w : WhichSize) sizesA sizeB density numberOfInstances timeout = 
    let prefix = [FORALL; EXISTS]
    let numberOfAps = 5

    let aps = 
        [1..numberOfAps]
        |> List.map (fun i -> Array.create i 'a' |> System.String.Concat)

    let resultDict = new Dictionary<_,_>()

    for size in sizesA do 
        let systemList = 
            match w with 
                | SYS -> 
                    TransitionSystem.Random.computeRandomTS aps size (density size) numberOfInstances
                | PROP -> 
                    TransitionSystem.Random.computeRandomTS aps sizeB (density sizeB) numberOfInstances

        let propList = 
            match w with 
                | SYS -> 
                    LTL.Random.getRandomHyperLTLOneByOne prefix (sizeB,sizeB) aps numberOfInstances
                | PROP -> 
                    LTL.Random.getRandomHyperLTLOneByOne prefix (size,size) aps numberOfInstances

        printfn "======= Working on size %i =======" size

        let combinationsToBeChecked = List.zip systemList propList
        
        let mutable current = 0

        let mutable timeComp = []
        let mutable timeStrat = []
        
        for ts, prop in combinationsToBeChecked do 
            Console.SetCursorPosition(0, Console.CursorTop)
            let percent = current * 100 / combinationsToBeChecked.Length
            current <- current + 1
            printf "%i%%" percent

            let tslist = List.init prefix.Length (fun _ -> ts)
            
            let res, t = AutomatonBasedVerification.modelCheckABV tslist prop COMP timeout

            if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value) then 
                timeComp <-  (Some t)::timeComp
            else 
                timeComp <-  Option.None::timeComp

            let resStrat, tStrat = StrategyBasedVerification.modelCheckSBV tslist prop timeout

            if resStrat.IsSome && (timeout.IsNone || tStrat.TotalTime <= timeout.Value) then 
                timeStrat <- (Some tStrat)::timeStrat
            else    
                timeStrat <- Option.None::timeStrat
                
           
        Console.SetCursorPosition(0, Console.CursorTop)

        resultDict.Add(size, (timeComp, timeStrat))
        
    let freshResultDict = new Dictionary<_,_>()

    let freshSuccessResultDict = new Dictionary<_,_>()

    for s in sizesA do 

        let rINCL, rSTRAT = resultDict.[s]

        let rINCLSorted = 
            rINCL
            |> List.filter Option.isSome
            |> List.map Option.get
            |> List.sortBy (fun x -> x.TotalTime)

        let rSTRATSorted = 
            rSTRAT
            |> List.filter Option.isSome
            |> List.map Option.get
            |> List.sortBy (fun x -> x.TotalTime)

        let maxK = min rINCLSorted.Length rSTRATSorted.Length

        let resINCL = 
            rINCLSorted[0..maxK - 1]
            |> List.fold (+) TimeSummaryTotal.Zero 

        let resSTRAT = 
            rSTRATSorted[0..maxK - 1]
            |> List.fold (+) GameTimeSummary.Zero 

        let total = rINCL.Length

        freshResultDict.Add(s, (resINCL / maxK,resSTRAT / maxK))
        freshSuccessResultDict.Add(s, ((rINCLSorted.Length * 100) / total, (rSTRATSorted.Length * 100) / total))

    
    let systemSizesName = List.map (fun x -> string x) sizesA
    let x = [systemSizesName @ systemSizesName; (List.init sizesA.Length (fun _ -> "ABV")) @  (List.init sizesA.Length (fun _ -> "SBV"))]

    let yCompNBA = 
        (sizesA
        |> List.map (fun s -> 
            let r, _ = freshResultDict.[s]
            r.LTL2NBATime
            ))
        @ (List.init sizesA.Length (fun _ -> 0))

    
    let yCompConst = 
        (sizesA
        |> List.map (fun s -> 
            let r, _ = freshResultDict.[s]
            r.ProductTimeSum
            ))
        @ (List.init sizesA.Length (fun _ -> 0))

    let yCombInc = 
        (sizesA
        |> List.map (fun s -> 
            let r, _ = freshResultDict.[s]
            r.ComplementationTimeSum + r.EmptinessTime
            ))
        @ (List.init sizesA.Length (fun _ -> 0))


    let yStratDPA = 
        (List.init sizesA.Length (fun _ -> 0))
        @
        (sizesA
        |> List.map (fun s -> 
            let _, r = freshResultDict.[s]
            r.LTL2DPATime
            ))

    let yStratConst = 
        (List.init sizesA.Length (fun _ -> 0))
        @
        (sizesA
        |> List.map (fun s -> 
            let _, r = freshResultDict.[s]
            r.ProductConstructionTime
            ))

    let yStratSolve = 
        (List.init sizesA.Length (fun _ -> 0))
        @
        (sizesA
        |> List.map (fun s -> 
            let _, r = freshResultDict.[s]
            r.ParityGameSolvingTime
            ))

    let traceCompNBA =
        Bar(
            x = x,
            y = yCompNBA,
            marker = Marker(color = C1.AsRGBAString 1.0),
            name = "LTL to NBA",
            legendgroup="ABV"
        )

    let traceCompConst =
        Bar(
            x = x,
            y = yCompConst,
            name = "Product Construction",
            marker = Marker(color = C6.AsRGBAString 1.0),
            legendgroup="ABV"
        )
    
    let traceCompInc =
        Bar(
            x = x,
            y = yCombInc,
            name = "Inclusion Check",
            marker = Marker(color = C5.AsRGBAString 1.0),
            legendgroup="ABV"
        )

    let traceStratDPA =
        Bar(
            x = x,
            y = yStratDPA,
            name = "LTL to DPA",
            marker = Marker(color = C2.AsRGBAString 1.0),
            legendgroup="SBV"
        )

    let traceStratConst =
        Bar(
            x = x,
            y = yStratConst,
            name = "Game Construction",
            marker = Marker(color = C4.AsRGBAString 1.0),
            legendgroup="SBV"
        )

    let traceStratSolve =
        Bar(
            x = x,
            y = yStratSolve,
            name = "Game Solving",
            marker = Marker(color = C7.AsRGBAString 1.0),
            legendgroup="SBV"
        )

    let legendStyle = 
        Legend(
            yanchor="top",
            y=0.99,
            xanchor="left",
            x=0.01
        )

    let styledLayout =
        Layout(
            xaxis = Xaxis(showline = true, zeroline=false, title=(match w with SYS -> "System Size" | PROP -> "Property Size")),
            yaxis = Yaxis(showline = true, zeroline=false, title="Time in ms"),
            barmode = "stack",
            legend = legendStyle,
            margin=
                Margin(
                    b = 100
                )
        )

    let chart =
        [traceCompNBA;traceCompConst;traceCompInc;traceStratDPA;traceStratConst;traceStratSolve]
        |> Chart.Plot
        |> Chart.WithLayout styledLayout
        |> Chart.WithHeight 500
        |> Chart.WithWidth 500

    let chartHtml = chart.GetHtml()

    let p = 
        match w with 
            | SYS -> Util.mainPath + "/plots/SBVandABVTimePerSystemSize.html"
            | PROP -> Util.mainPath + "/plots/SBVandABVTimePerPropSize.html"

    System.IO.File.WriteAllText(p, chartHtml)

    
    
/// Compare the time taken by SBV and ABV on varying density
let compareABVandSBVTimePerDensity systemSize densities numberOfInstances timeout = 
    let prefix = [FORALL; EXISTS]
    let numberOfAps = 5
    let propSize = 20, 30
   
    let aps = 
        [1..numberOfAps]
        |> List.map (fun i -> Array.create i 'a' |> System.String.Concat)

    let resultDict = new Dictionary<_,_>()

    let resultDictSucess = new Dictionary<_,_>()

    for tranistionDensity in densities do 
        printfn "======= Working on density %f =======" tranistionDensity

        let propList = 
            LTL.Random.getRandomHyperLTLOneByOne prefix propSize aps numberOfInstances

        let systemList = 
            TransitionSystem.Random.computeRandomTS aps systemSize tranistionDensity numberOfInstances

        let combinationsToBeChecked = List.zip systemList propList

        let mutable current = 0

        let mutable timeComp = []
        let mutable timeStrat = []
        
        for ts, prop in combinationsToBeChecked do 
            Console.SetCursorPosition(0, Console.CursorTop)
            let percent = current * 100 / combinationsToBeChecked.Length
            current <- current + 1
            printf "%i%%" percent

            let tslist = List.init prefix.Length (fun _ -> ts)
            
            let res, t = AutomatonBasedVerification.modelCheckABV tslist prop (INCLUSION SPOT) timeout

            if res.IsSome && (timeout.IsNone || t.TotalTime <= timeout.Value) then 
                timeComp <-  (Some t)::timeComp
            else 
                timeComp <-  Option.None::timeComp

            let resStrat, tStrat = StrategyBasedVerification.modelCheckSBV tslist prop timeout

            if resStrat.IsSome && (timeout.IsNone || tStrat.TotalTime <= timeout.Value) then 
                timeStrat <- (Some tStrat)::timeStrat
            else    
                timeStrat <- Option.None::timeStrat
                
           
        Console.SetCursorPosition(0, Console.CursorTop)

        resultDict.Add(tranistionDensity, (timeComp, timeStrat))

    
    let freshResultDict = new Dictionary<_,_>()

    for density in densities do 

        let rINCL, rSTRAT = resultDict.[density]

        let rINCLSorted = 
            rINCL
            |> List.filter Option.isSome
            |> List.map Option.get
            |> List.sortBy (fun x -> x.TotalTime)

        let rSTRATSorted = 
            rSTRAT
            |> List.filter Option.isSome
            |> List.map Option.get
            |> List.sortBy (fun x -> x.TotalTime)

        let maxK = min rINCLSorted.Length rSTRATSorted.Length

        let resINCL = 
            rINCLSorted[0..maxK - 1]
            |> List.fold (+) TimeSummaryTotal.Zero 

        let resSTRAT = 
            rSTRATSorted[0..maxK - 1]
            |> List.fold (+) GameTimeSummary.Zero 

        freshResultDict.Add(density, (resINCL / maxK,resSTRAT / maxK))

    
    let systemSizesName = List.map (fun x -> string x) densities
    let x = [systemSizesName @ systemSizesName; (List.init densities.Length (fun _ -> "ABV")) @  (List.init densities.Length (fun _ -> "SBV"))]

    let yCompNBA = 
        (densities
        |> List.map (fun s -> 
            let r, _ = freshResultDict.[s]
            r.LTL2NBATime
            ))
        @ (List.init densities.Length (fun _ -> 0))

    let yCompConst = 
        (densities
        |> List.map (fun s -> 
            let r, _ = freshResultDict.[s]
            r.ProductTimeSum
            ))
        @ (List.init densities.Length (fun _ -> 0))

    let yCombInc = 
        (densities
        |> List.map (fun s -> 
            let r, _ = freshResultDict.[s]
            r.InclusionTime
            ))
        @ (List.init densities.Length (fun _ -> 0))


    let yStratDPA = 
        (List.init densities.Length (fun _ -> 0))
        @
        (densities
        |> List.map (fun s -> 
            let _, r = freshResultDict.[s]
            r.LTL2DPATime
            ))

    let yStratConst = 
        (List.init densities.Length (fun _ -> 0))
        @
        (densities
        |> List.map (fun s -> 
            let _, r = freshResultDict.[s]
            r.ProductConstructionTime
            ))

    let yStratSolve = 
        (List.init densities.Length (fun _ -> 0))
        @
        (densities
        |> List.map (fun s -> 
            let _, r = freshResultDict.[s]
            r.ParityGameSolvingTime
            ))

    let traceCompNBA =
        Bar(
            x = x,
            y = yCompNBA,
            marker = Marker(color = C1.AsRGBAString 1.0),
            name = "LTL to NBA",
            legendgroup="ABV"
        )

    let traceCompConst =
        Bar(
            x = x,
            y = yCompConst,
            name = "Product Construction",
            marker = Marker(color = C6.AsRGBAString 1.0),
            legendgroup="ABV"
        )
    
    let traceCompInc =
        Bar(
            x = x,
            y = yCombInc,
            name = "Inclusion Check",
            marker = Marker(color = C5.AsRGBAString 1.0),
            legendgroup="ABV"
        )

    let traceStratDPA =
        Bar(
            x = x,
            y = yStratDPA,
            name = "LTL to DPA",
            marker = Marker(color = C2.AsRGBAString 1.0),
            legendgroup="SBV"
        )

    let traceStratConst =
        Bar(
            x = x,
            y = yStratConst,
            name = "Game Construction",
            marker = Marker(color = C4.AsRGBAString 1.0),
            legendgroup="SBV"
        )

    let traceStratSolve =
        Bar(
            x = x,
            y = yStratSolve,
            name = "Game Solving",
            marker = Marker(color = C7.AsRGBAString 1.0),
            legendgroup="SBV"
        )

    let legendStyle = 
        Legend(
            yanchor="top",
            y=0.99,
            xanchor="left",
            x=0.01
        )

    let styledLayout =
        Layout(
            xaxis = Xaxis(title = "Transition Density", showline = true,zeroline=false),
            yaxis = Yaxis(title = "Time in ms", showline = true,zeroline=false),
            barmode = "stack",
            legend = legendStyle
        )

    let chart =
        [traceCompNBA; traceCompConst; traceCompInc;  traceStratDPA;traceStratConst;traceStratSolve]
        |> Chart.Plot
        |> Chart.WithLayout styledLayout
        |> Chart.WithHeight 500
        |> Chart.WithWidth 700


    let timeChartHtml = chart.GetHtml()
    System.IO.File.WriteAllText(Util.mainPath + "/plots/SBVandABVTimePerDensity.html", timeChartHtml)

// All experiments currently supported. Add new experiments to this list
let experiments =
    [
        ("successSystemSize",
            fun () ->
                successPerSizeAndMode SYS [10..10..100] 20 (fun n -> 10.0 / double(n)) 100 [Mode.COMP; Mode.INCLUSION SPOT; Mode.INCLUSION BAIT; Mode.INCLUSION RABIT] (Some 10000)
        )
        
        ("survivalSystemSize",
            fun () ->
                survivalPerMode 30 0.2 (20, 20) 100 [Mode.COMP; Mode.INCLUSION SPOT; Mode.INCLUSION BAIT; Mode.INCLUSION RABIT] (Some 10000)
        )
        
        ("successAndMedianTimeSystemSize",
            fun () ->
                successRateAndMedianTimePerSizeAndMode SYS [100..100..2000] 20 (fun n -> 10.0 / double(n)) 30 [Mode.INCLUSION SPOT; Mode.INCLUSION RABIT] (Some 10000)
        )
        
        ("survivalAlternation",
            fun () ->
                survivalPerAlternation 30 0.1 (20, 30) [1..4] 100 (Some 5000)
        )
        
        ("complementationCostAlternation",
            fun () ->
                complementationCostPerAlternation 30 0.1 (20, 30) [1..4] 100 (Some 5000)
        )
        
        ("successAndPositiveRate",    
            fun () ->
                successRateOfABVandSBVAndPositiveRate 15 [10..10..100] (fun n -> 4.0 / double(n)) 100 (Some 10000) (Some 10000)
        );
        
        ("ABVandSBVTimeSystem",
            fun () ->
                compareABVandSBVTimePerSize SYS [10..10..60] 20 (fun n -> 4.0 / double(n)) 100 (Some 5000)
        )
        
        ("ABVandSBVTimeProperty",
            fun () ->
                compareABVandSBVTimePerSize PROP [10..10..50] 30 (fun n -> 4.0 / double(n)) 100 (Some 5000)
        )
        
        ("ABVandSBVTimeDensity",   
            fun () ->
                compareABVandSBVTimePerDensity 20 [0.01;0.02;0.1;0.3;0.5;0.8] 100 (Some 5000)
        )
    ]
    |> Map.ofList
