module CLS.Experiments.ServiceComposition

//based on Section 4.3 in
//J. Rehof. Towards Combinatory Logic Synthesis. In BEAT 2013, 1st International Workshop on Behavioural Types. ACM, 2013.

open CLS.Model.Type
open CLS.Experiments.BenchmarkUtil

let run_ServiceComposition () = 
    let alpha = Var ("alpha")
    let arrayOfAlpha = Constructor("Array", [alpha])
    let graphOfAlpha = Constructor("Graph", [alpha])
    let graphOfTasks = Constructor("Graph", [getConst "Task"])
    let arrayOfTasks = Constructor("Array", [getConst "Task"])
    let alphaToBool = Arrow(alpha, getConst "bool")
    //let alphaToBool = Intersect(Set.ofList [Arrow(alpha, getConst "bool"); getConst "Chooser"])
    let alphaToAlphaToBool = getIntersect [Arrow(alpha, Arrow(alpha, getConst "bool")); getConst "Order"]
    let subtypingRelation = [("PartialOrder", "Order"); ("TotalOrder", "Order")]
    let isSubtype x y = x = y || List.exists (fun c -> c = (x,y)) subtypingRelation

    let context = [
        ("Circ", getArrow [Arrow(Var("X"), Var("Y")); Arrow(Var("Y"), Var("Z")); getBracket (Arrow(Var("X"), Var("Z")))]);
        ("Dia", getArrow [getArrow [Var("X"); Var("Y"); Var("Z")]; Arrow(Var("X"), Var("Y")); getBracket (Arrow(Var("X"), Var("Z")))]);

        ("F", getIntersect [getArrow [arrayOfAlpha; alphaToBool; arrayOfAlpha]; getConst "Filter"]);
        ("S", Arrow(getIntersect [getArrow [arrayOfAlpha; alphaToBool; arrayOfAlpha]; getConst "Filter"], 
                getIntersect [getArrow [alphaToAlphaToBool; arrayOfAlpha; arrayOfAlpha]; 
                                      getArrow [getConst "TotalOrder"; Omega; getConst "Sorted"]; 
                                      getArrow [getConst "PartialOrder"; Omega; getConst "TopSorted"]]));
        //OLD G WITH NO BRACKETS (can construct alpha -> bool via G(_, _))
        ("G", Arrow(graphOfAlpha, getIntersect [alphaToAlphaToBool; getConst "PartialOrder"]));
        //NEW G WITH BRACKETS
        //("G", Arrow(graphOfAlpha, getBracket (getIntersect [alphaToAlphaToBool; getConst "PartialOrder"])));

        ("N", Arrow(graphOfAlpha, arrayOfAlpha));
        
        ("Connect", getIntersect [getConst "int"; getConst "SessionID"]);
        ("ReqTransaction", getArrow[getIntersect [getConst "int"; getConst "UserID"];
                                    getIntersect [getConst "int"; getConst "SessionID"]; 
                                        getIntersect [arrayOfTasks; getConst "TopSorted"]; 
                                            getIntersect [getConst "int"; getConst "TID"]]);
        ("EndTransaction", Arrow(getIntersect [getConst "int"; getConst "TID"], Constructor("Array", [getIntersect [getConst "int"; getConst "Result"]])));
        ("MyID", getIntersect [getConst "int"; getConst "UserID"]);
        //USED ONLY IN NON-ARROW RESULTS
        //("GetTasks", graphOfTasks)
        ] 



    //q, no need for °...
    //let goal = Constructor("Array", [getIntersect [getConst "int"; getConst "Result"]])
    
    //q0, result: Y °' X ° EndTransaction
    let goal = Arrow(graphOfTasks, Constructor("Array", [getIntersect [getConst "int"; getConst "Result"]]))
    //result: Circ(G(GetTasks()), F(EndTransaction(ReqTransaction(MyID(), Connect(), S(F(), G(GetTasks()), N(GetTasks()))))))
    //q1, result: FlipCirc Y X
    //let goal = Arrow(graphOfTasks, getIntersect [getConst "int"; getConst "TID"])
    //q2, result: Y = FlipDia N (Circ G SF)
    //let goal = Arrow(graphOfTasks, getIntersect [arrayOfTasks; getConst "TopSorted"])
    //q3, result: Circ G SF
    //let goal = Arrow(graphOfTasks, Arrow(arrayOfTasks, getIntersect [arrayOfTasks; getConst "TopSorted"]))
    //let goal = Arrow(graphOfTasks, getIntersect [Arrow(getConst "Task", Arrow(getConst "Task", getConst "bool")) ;getConst "Order"; getConst "PartialOrder"])

    (*
    //q4, result: SF
    let goal = Arrow(getIntersect [Arrow(Omega, Arrow(Omega, getConst "bool")); getConst "PartialOrder"; getConst "Order"], 
                Arrow(Constructor("Array", [getConst "Task"]), 
                    getIntersect [Constructor("Array", [getConst "Task"]); getConst "TopSorted"]))
    //*)

    runExperiment 4 isSubtype context goal