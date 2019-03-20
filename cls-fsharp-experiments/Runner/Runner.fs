module CLS.Experiments.Runner

//based on
//M. Pennekamp. Simulation von Berechnungsmodellen innerhalb des Softwaresyntheseframeworks CLS. Bachelor Thesis, TU Dortmund University.

open CLS.Model.Type
open CLS.Experiments.BenchmarkUtil

let run_Runner () = 
    let grnd = getConst "grnd"
    let air1 = getConst "air1"
    let air2 = getConst "air2"
    let fall = getConst "fall"
    let dead = getConst "dead"

    let epsilon = getConst "epsilon"

    let State s = Constructor("St",[s])
    let Word v = Constructor("Word",[v])

    let g v = Constructor("g",[v])
    let b v = Constructor("b",[v])

    let alpha = Var ("alpha")

    let transition s c t = getArrow [getArrow [State t; Word alpha]; State s; Word (c alpha)]

    let fin_ty = getArrow [State(grnd); Word(epsilon)]
    let run_ty = getArrow [getArrow [State(grnd); Word(alpha)]; Word(alpha)]


    let isSubtype x y = x = y


    let context = [
        ("Fin[grnd]", fin_ty);
        ("Run[grnd]", run_ty);
        ("run", transition grnd g grnd);
        ("jump", transition grnd b air1);
        ("fall", transition air1 g grnd);
        ("jump", transition air1 b air2);
        ("fall", transition air2 g fall);
        ("die", transition air2 b dead);
        ("fall", transition fall g grnd);
        ("die", transition fall b dead);
        ("stayDead", transition dead g dead);
        ("stayDead", transition dead b dead)] 

    
    let getWord (v : string) = v |> Seq.rev |> Seq.fold (fun t -> fun c -> if c = 'b' then b t else g t) epsilon |> Word
    //let goal = Word(b(b(g(g(epsilon)))))
    //let goal = getWord "bbgg"

    let goal = getWord (String.replicate 20 "bbgg")

    runExperiment 4000 isSubtype context goal