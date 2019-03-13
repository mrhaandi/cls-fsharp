module CLS.Experiments.MixinComposition

open CLS.Model.Type
open CLS.Experiments.BenchmarkUtil

let run_MixinComposition () = 
    let record fields = Constructor("Record", [getIntersect fields])

    let alpha_get = Var ("alpha_get")
    let alpha_set = Var ("alpha_set")
    let alpha_succ = Var ("alpha_succ")
    let alpha_succ2 = Var ("alpha_succ2")
    let alpha_compare = Var ("alpha_compare")

    let get t = Constructor("get", [t])
    let set t = Constructor("set", [t])
    let succ t = Constructor("succ", [t])
    let succ2 t = Constructor("succ2", [t])
    let compare t = Constructor("compare", [t])
    
    let Int = getConst "Int"
    let Even = getConst "Even"
    let Odd = getConst "Odd"
    let EvenInt = getIntersect [Int; Even]
    let OddInt = getIntersect [Int; Odd]
    let Bool = getConst "Bool"
    let IntToRecord fields = Arrow(Int, record fields)
    let EvenIntToRecord fields = Arrow(EvenInt, record fields)
    let OddIntToRecord fields = Arrow(OddInt, record fields)
    
    let alpha = Var "alpha"
    let String = getConst "String"
    let StringToRecord fields = Arrow(String, record fields)
    let Plain = getConst "Plain"
    let Time = getConst "Time"
    let Enc t = Constructor("Enc", [t])
    let Sign t = Constructor("Sign", [t])

    let isSubtype x y = x = y

    let context = [
        ("Num", getIntersect [
            IntToRecord [get Int; succ Int; set (getIntersect [Arrow(Int, Int);Arrow(Even, Even); Arrow(Odd, Odd)])];
            EvenIntToRecord [get EvenInt; succ OddInt];
            OddIntToRecord [get OddInt; succ EvenInt]]);
        
       
        ("Comparable", getIntersect [
            Arrow(IntToRecord [get Int], IntToRecord [compare (Arrow(record [get Int], Bool))]);
            Arrow(IntToRecord [get alpha_get], IntToRecord [get alpha_get]);
            Arrow(IntToRecord [set alpha_set], IntToRecord [set alpha_set]);
            Arrow(IntToRecord [succ alpha_succ], IntToRecord [succ alpha_succ]);
            Arrow(IntToRecord [succ2 alpha_succ2], IntToRecord [succ2 alpha_succ2])]);
        ("Succ2", getIntersect [
            Arrow(IntToRecord [succ Int], IntToRecord [succ2 Int]);
            Arrow(IntToRecord [get alpha_get], IntToRecord [get alpha_get]);
            Arrow(IntToRecord [set alpha_set], IntToRecord [set alpha_set]);
            Arrow(IntToRecord [succ alpha_succ], IntToRecord [succ alpha_succ]);
            Arrow(IntToRecord [compare alpha_compare], IntToRecord [compare alpha_compare]);
            Arrow(getIntersect [EvenIntToRecord [succ OddInt]; OddIntToRecord [succ EvenInt]], 
                getIntersect [EvenIntToRecord [succ2 EvenInt]; OddIntToRecord [succ2 OddInt]])]);
        ("SuccDelta", getIntersect [
            Arrow(IntToRecord [get Int; set (Arrow(Int, Int))], IntToRecord [succ (Arrow(Int, Int))]);
            Arrow(IntToRecord [get alpha_get], IntToRecord [get alpha_get]);
            Arrow(IntToRecord [set alpha_set], IntToRecord [set alpha_set]);
            Arrow(IntToRecord [succ2 alpha_succ2], IntToRecord [succ2 alpha_succ2]);
            Arrow(IntToRecord [compare alpha_compare], IntToRecord [compare alpha_compare])]);
        ("Parity", getIntersect [
            Arrow(IntToRecord [succ2 Int], IntToRecord [succ Int]);
            Arrow(IntToRecord [get alpha_get], IntToRecord [get alpha_get]);
            Arrow(IntToRecord [set alpha_set], IntToRecord [set alpha_set]);
            Arrow(IntToRecord [succ2 alpha_succ2], IntToRecord [succ2 alpha_succ2]);
            Arrow(IntToRecord [compare alpha_compare], IntToRecord [compare alpha_compare]);
            Arrow(getIntersect [EvenIntToRecord [succ2 EvenInt]; OddIntToRecord [succ2 OddInt]], 
                getIntersect [EvenIntToRecord [succ EvenInt]; OddIntToRecord [succ OddInt]])]);

        ("Reader", StringToRecord [get (getIntersect [String; Plain])]);
        ("Enc", Arrow(StringToRecord [get (getIntersect [String; alpha])], StringToRecord [get (getIntersect [String; Enc alpha])]));
        ("Sign", Arrow(StringToRecord [get (getIntersect [String; alpha])], StringToRecord [get (getIntersect [String; alpha; Sign alpha])]));
        ("Time", Arrow(StringToRecord [get (getIntersect [String; alpha])], StringToRecord [get (getIntersect [String; alpha; Time])]));
        ] 

    
    //Section 5.2. Mixin Composition, p. 27
    //let goal = IntToRecord [succ Int; compare (Arrow(record [get Int], Bool)); succ2 Int]

    //Section 5.2. Mixin Composition, p. 28
    //let goal = IntToRecord [succ (Arrow(Int, Int)); succ2 Int]

    //Section 5.3. Semantic Types, p. 29
    //let goal = EvenIntToRecord [succ EvenInt]

    //Section 5.3. Semantic Types, p. 30
    let goal = StringToRecord [get (getIntersect [String; Enc (getIntersect [Plain; Time; Sign (getIntersect [Plain; Time])])])]
    //let goal = StringToRecord [get (getIntersect [String; Enc (Enc (Enc Plain))])]

    runExperiment 4000 isSubtype context goal