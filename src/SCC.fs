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

module SCC

open System.Collections.Generic


/// Given a graph, compute all SCC of that graph
let computeSCC (nodes : seq<'T>) (forwardEdges: 'T -> seq<'T>) =
    let backwardEgdes = new Dictionary<_,_>()
    for s in nodes do 
        backwardEgdes.Add(s, new HashSet<_>())
    
    let visited = new HashSet<_>()

    let l = new Stack<_>()

    let rec visit n =
        if visited.Contains n |> not then
            visited.Add n |> ignore

            for n' in forwardEdges n do
                visit n'
                backwardEgdes.[n'].Add n |> ignore
            l.Push n

    for n in nodes do
        visit n

    let wasAssigned = new HashSet<_>()
   
    let rec assign (n : 'T) : Set<'T> =
        if wasAssigned.Contains n |> not then
            wasAssigned.Add n |> ignore

            let temp =
                [ for n' in backwardEgdes.[n] do
                      assign n' ]
                |> Set.unionMany

            Set.add n temp
        else
            Set.empty

    let mutable components = []

    for n in l do
        if wasAssigned.Contains n |> not then
            components <- assign n :: components

    components |> List.rev

