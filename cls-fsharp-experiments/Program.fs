open System.Threading

open CLS.Experiments.ServiceComposition
open CLS.Experiments.RecordCalculus
open CLS.Experiments.ProcessSynthesis

[<EntryPoint>]
let main argv =
    printfn "(CL)S-F# Service Composition Experiments"
    let stackSizeInBytes : int = 1024*1024*32

    printfn "Select one of the following experiments:"
    printfn "1: Service Composition"
    printfn "2: Record Calculus"
    printfn "3: Process Synthesis"

    match System.Console.ReadKey().KeyChar with
    | '1' -> 
        printfn "\n"
        let thread = new Thread(run_ServiceComposition, stackSizeInBytes)
        thread.Start()
    | '2' -> 
        printfn "\n"
        let thread = new Thread(run_RecordCalculus, stackSizeInBytes)
        thread.Start()
    | '3' -> 
        printfn "\n"
        let thread = new Thread(run_ProcessSynthesis, stackSizeInBytes)
        thread.Start()
    | _ ->  printfn "\nERROR: No experiment selected"

    while true do
        System.Console.ReadKey() |> ignore
    0
