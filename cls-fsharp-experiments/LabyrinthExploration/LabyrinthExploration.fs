module CLS.Experiments.LabyrinthExploration

open System

open CLS.Model.Type
open CLS.Experiments.BenchmarkUtil

let run_LabyrinthExploration () = 
    //n*n as size of labyrinth
    let n = 24
    //wall probability 1/p
    let p = 4

    let rand = new Random(1337)
    //construct random labyrinth
    let labyrinth = [for i = 0 to (n-1) do for j = 0 to (n-1) do if (rand.Next(p) > 0) || ((i,j) = (0,0)) || ((i,j) = (n-1,n-1)) then yield (i, j)]

    for i = 0 to n-1 do
        
        for j = 0 to n-1 do
            if List.contains (i, j) labyrinth then printf "true, " else printf "false, "
        printf "\n"

    printfn "Labyrinth:"
    for i = 0 to n-1 do
        printf "|"
        for j = 0 to n-1 do
            if (i, j) = (0, 0) then printf "S"
            else if (i, j) = (n-1, n-1) then printf "G"
            else if List.contains (i, j) labyrinth then printf "." else printf "X"
        printfn "|"
    
    let Zero = getConst "zero"
    let Succ x = Constructor("s", [x])
    let rec num i = if i = 0 then Zero else Succ (num (i-1))

    let alpha = Var "alpha"
    let beta = Var "beta"
    let Pos x y = Constructor("pos", [x; y])

    let Free x y = Constructor("free", [x; y])
    
    let isSubtype x y = x = y

    let context = 
        [
            ("Left", getArrow [Pos alpha (Succ beta); Free alpha beta; Pos alpha beta]);
            ("Right", getArrow [Pos alpha beta; Free alpha (Succ beta); Pos alpha (Succ beta)]);      
            ("Up", getArrow [Pos (Succ alpha) beta; Free alpha beta; Pos alpha beta]);
            ("Down", getArrow [Pos alpha beta; Free (Succ alpha) beta; Pos (Succ alpha) beta]);
            ("Start", Pos (num 0) (num 0))
        ] @ [for (x, y) in labyrinth do yield ((sprintf "isFree(%d,%d)" x y), Free (num x) (num y))]
            
    let goal = Pos (num (n-1)) (num (n-1))

    runExperiment (n+n+3) isSubtype context goal