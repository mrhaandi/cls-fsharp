module CLS.Experiments.BenchmarkUtil

open System

open CLS.Model.ID
open CLS.Model.Type

open CLS.Algorithm.Type
open CLS.Algorithm.CombinatorTerm
open CLS.Algorithm.Inhabitation
//open CLS.Algorithm.InhabitationNoII

let duration f = 
    let timer = new System.Diagnostics.Stopwatch()
    timer.Start()
    let returnValue = f()
    timer.Stop()
    printfn " duration: %i ms" timer.ElapsedMilliseconds
    returnValue

 //let toType<'a> (input:'a) : IntersectionType = 
//    match box input with
//    | :? ID as id -> Constructor(id, [])

let getConst (id : ID) = Constructor(id, [])
let getIntersect (taus : IntersectionType list) = taus |> List.map simplifyType |> intersectSimplifiedTypes
let getBox (tau : IntersectionType) = Constructor("Box", [simplifyType tau])
let getRecord (entries : (ID*IntersectionType) list) = Constructor("Record", [intersectSimplifiedTypes (List.map (fun (label, entry) -> Constructor(label, [simplifyType entry])) entries)])
let getBracket (tau : IntersectionType) = Constructor("Bracket", [simplifyType tau])
let rec getArrow = function | [] -> failwith "Empty Arrow" | [tau] -> tau | tau::tail -> Arrow(tau, getArrow tail)


let emptyLogger level message = ()
let printLogger level (message : Lazy<string>) = printfn "%s" (message.Force())

let runExperiment (maxTreeDepth : int) (atomicSubtypes : ID -> ID -> bool) (environment : Environment) (goal : IntersectionType) = 
    printfn "type environment: "
    for (id, sigma) in environment do printfn "%s : %O" id sigma
    printfn "type environment size %O" (List.length environment)
    printfn "goal type: "
    printfn "%O" goal
    printfn "goal type size %O" (getTypeSize goal)
    //let getAllInhabitantsInContext = getAllInhabitants printLogger isSubtype context
    let getAllInhabitantsInContext = getAllInhabitants maxTreeDepth emptyLogger atomicSubtypes environment
    let grammar = duration (fun _ -> getAllInhabitantsInContext goal)
    let inhabitants = listMinimalCombinatorTerms 6 grammar goal
    if (inhabitants.Length = 0) then printfn "no inhabitants found"
    else
        printfn "some inhabitants:"
        for term in inhabitants do 
            printfn "%O" term
            printfn "term size %O" (combinatorTermSize term)
    printfn "done"
    ()