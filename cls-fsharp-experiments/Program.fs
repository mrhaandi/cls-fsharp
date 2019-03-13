open System.Threading

open CLS.Experiments.ServiceComposition
open CLS.Experiments.MixinComposition
open CLS.Experiments.ProcessSynthesis
open CLS.Experiments.TwoCounterAutomaton
open CLS.Experiments.FiniteFunctionComposition
open CLS.Experiments.LabyrinthExploration
open CLS.Experiments.Runner

[<EntryPoint>]
let main argv =
    printfn "(CL)S-F# Service Composition Experiments"
    let stackSizeInBytes : int = 1024*1024*32

    printfn "Select one of the following experiments:"
    printfn "1: Service Composition"
    printfn "2: Mixin Composition"
    printfn "3: Process Synthesis"
    printfn "4: Two Counter Automaton Simulation"
    printfn "5: Labyrinth Exploration"

    printfn "7: Finite Function Composition"
    printfn "8: Runner"

    let key = System.Console.ReadKey().KeyChar
    printfn "\n"

    match key with
    | '1' -> 
        let thread = new Thread(run_ServiceComposition, stackSizeInBytes)
        thread.Start()
    | '2' -> 
        let thread = new Thread(run_MixinComposition, stackSizeInBytes)
        thread.Start()
    | '3' -> 
        let thread = new Thread(run_ProcessSynthesis, stackSizeInBytes)
        thread.Start()
    | '4' -> 
        let thread = new Thread(run_TwoCounterAutomaton, stackSizeInBytes)
        thread.Start()
    | '5' -> 
        let thread = new Thread(run_LabyrinthExploration, stackSizeInBytes)
        thread.Start()
    | '7' -> 
        let thread = new Thread(run_FiniteFunctionComposition, stackSizeInBytes)
        thread.Start()
    | '8' -> 
        let thread = new Thread(run_Runner, stackSizeInBytes)
        thread.Start()
    | _ ->  printfn "\nERROR: No experiment selected"

    while true do
        System.Console.ReadKey() |> ignore
    0
