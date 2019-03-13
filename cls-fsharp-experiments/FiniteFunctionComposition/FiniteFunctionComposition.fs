module CLS.Experiments.FiniteFunctionComposition

open CLS.Model.Type
open CLS.Experiments.BenchmarkUtil

let run_FiniteFunctionComposition () = 
    //number of atoms 0 .. (n-1)
    let n : int = 30
    //number of arguments in composition (at least 2)
    let m : int = 2


    let num i = getConst (i.ToString())
    let alpha i j = Var ("alpha_" + i.ToString() + "^" + j.ToString())
    //let alpha i = Var ("alpha" + i.ToString())
    //let beta i = Var ("beta" + i.ToString())
    //let gamma i = Var ("gamma" + i.ToString())

    let Int = getConst "Int"
    let Function = getConst "Function"
    let Mapping (i : int) (j : int) = Arrow(getConst (i.ToString()), getConst (j.ToString()))

    let isSubtype x y = x = y

    let context = [
        ("Id", getIntersect (Arrow(Int, Int) :: Function :: [for i in [0 .. n-1] do yield Mapping i i]));
        ("Succ", getIntersect (Arrow(Int, Int) :: Function :: [for i in [0 .. n-1] do yield Mapping i ((i+1) % n)]));
        ("Pred", getIntersect (Arrow(Int, Int) :: Function :: [for i in [0 .. n-1] do yield Mapping i ((i+n-1) % n)]));
        ("Rev", getIntersect (Arrow(Int, Int) :: Function :: [for i in [0 .. n-1] do yield Mapping i (n-1-i)]));
        ("Compose", getIntersect 
            ((getArrow [Arrow(Int, Int); Arrow(Int, Int); Arrow(Int, Int)]) ::
            (getArrow [Function; Function; Function]) ::
            [for i in [0 .. n-1] do yield (getArrow ([Arrow(num i, alpha i 1)] @ [for j in [1 .. m-1] do yield Arrow(alpha i j, alpha i (j+1))] @ [getBracket (Arrow(num i, alpha i m))]))]))
        ]

    
    //let goal = getIntersect [for i in [0 .. n-1] do yield Mapping i i]
    let goal = getIntersect [for i in [0 .. n-1] do yield Mapping i ((i+1) % n)]
    //let goal = getIntersect [for i in [0 .. n-1] do yield Mapping i ((n+n-3-i) % n)]

    runExperiment 2 isSubtype context goal