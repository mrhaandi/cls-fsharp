module CLS.Experiments.TwoCounterAutomaton

open CLS.Model.Type
open CLS.Experiments.BenchmarkUtil

let run_TwoCounterAutomaton () = 
    let alpha = Var ("alpha")
    let beta = Var ("beta")
    let c t = Constructor("c", [t])
    let d t = Constructor("d", [t])
    let zero = Constructor("zero", [])
    let s t = Constructor("s", [t])
    let config (state, x, y) = Arrow(x, Arrow(y, state))

    let alphaToBool = Arrow(alpha, getConst "bool")
    //let alphaToBool = Intersect(Set.ofList [Arrow(alpha, getConst "bool"); getConst "Chooser"])
    let alphaToAlphaToBool = getIntersect [Arrow(alpha, Arrow(alpha, getConst "bool")); getConst "Order"]
    

    let isSubtype x y = x = y

    let context = [
        ("DEC_c_p_p1", Arrow(config(Constructor("p1", []), c(alpha), d(beta)), config(Constructor("p", []), c(s(alpha)), d(beta))));
        ("Z_c_p1_twoCounter_accept", Arrow(config(Constructor("twoCounter_accept", []), c(zero), d(beta)), config(Constructor("p1", []), c(zero), d(beta))));
        ("NZ_c_p1_p2", Arrow(config (Constructor("p2", []), c(s(alpha)), d(beta)), config(Constructor("p1", []), c(s(alpha)), d(beta))));
        ("INC_c_p2_p3", Arrow(config(Constructor("p3", []), c(s(alpha)), d(beta)), config(Constructor("p2", []), c(alpha), d(beta))));
        ("NZ_c_p3_md1p", Arrow(config (Constructor("md1p", []), c(s(alpha)), d(beta)), config(Constructor("p3", []), c(s(alpha)), d(beta))));
        ("Z_c_p3_p4", Arrow(config(Constructor("p4", []), c(zero), d(beta)), config(Constructor("p3", []), c(zero), d(beta))));
        ("DEC_c_md1p_md2p", Arrow(config(Constructor("md2p", []), c(alpha), d(beta)), config(Constructor("md1p", []), c(s(alpha)), d(beta))));
        ("NZ_c_md2p_md4p", Arrow(config (Constructor("md4p", []), c(s(alpha)), d(beta)), config(Constructor("md2p", []), c(s(alpha)), d(beta))));
        ("Z_c_md2p_md3p", Arrow(config(Constructor("md3p", []), c(zero), d(beta)), config(Constructor("md2p", []), c(zero), d(beta))));
        ("INC_c_md3p_p4", Arrow(config(Constructor("p4", []), c(s(alpha)), d(beta)), config(Constructor("md3p", []), c(alpha), d(beta))));
        ("DEC_c_md4p_md5p", Arrow(config(Constructor("md5p", []), c(alpha), d(beta)), config(Constructor("md4p", []), c(s(alpha)), d(beta))));
        ("INC_d_md5p_p3", Arrow(config(Constructor("p3", []), c(alpha), d(s(beta))), config(Constructor("md5p", []), c(alpha), d(beta))));
        ("Z_c_p4_p5", Arrow(config(Constructor("p5", []), c(zero), d(beta)), config(Constructor("p4", []), c(zero), d(beta))));
        ("NZ_c_p5_cp1p_copyBack_0", Arrow(config (Constructor("cp1p_copyBack_0", []), c(s(alpha)), d(beta)), config(Constructor("p5", []), c(s(alpha)), d(beta))));
        ("Z_c_p5_cp2p_copyBack_0", Arrow(config(Constructor("cp2p_copyBack_0", []), c(zero), d(beta)), config(Constructor("p5", []), c(zero), d(beta))));
        ("DEC_c_cp1p_copyBack_0_p5", Arrow(config(Constructor("p5", []), c(alpha), d(beta)), config(Constructor("cp1p_copyBack_0", []), c(s(alpha)), d(beta))));
        ("NZ_d_cp2p_copyBack_0_cp3p_copyBack_0", Arrow(config(Constructor("cp3p_copyBack_0", []), c(alpha), d(s(beta))), config(Constructor("cp2p_copyBack_0", []), c(alpha), d(s(beta)))));
        ("Z_d_cp2p_copyBack_0_p", Arrow(config(Constructor("p", []), c(alpha), d(zero)), config(Constructor("cp2p_copyBack_0", []), c(alpha), d(zero))));
        ("DEC_d_cp3p_copyBack_0_cp4p_copyBack_0", Arrow(config(Constructor("cp4p_copyBack_0", []), c(alpha), d(beta)), config(Constructor("cp3p_copyBack_0", []), c(alpha), d(s(beta)))));
        ("INC_c_cp4p_copyBack_0_cp2p_copyBack_0", Arrow(config(Constructor("cp2p_copyBack_0", []), c(s(alpha)), d(beta)), config(Constructor("cp4p_copyBack_0", []), c(alpha), d(beta))));
        ("NZ_c_p4_p6", Arrow(config (Constructor("p6", []), c(s(alpha)), d(beta)), config(Constructor("p4", []), c(s(alpha)), d(beta))));
        ("NZ_c_p6_cp1p_copyBack_1", Arrow(config (Constructor("cp1p_copyBack_1", []), c(s(alpha)), d(beta)), config(Constructor("p6", []), c(s(alpha)), d(beta))));
        ("Z_c_p6_cp2p_copyBack_1", Arrow(config(Constructor("cp2p_copyBack_1", []), c(zero), d(beta)), config(Constructor("p6", []), c(zero), d(beta))));
        ("DEC_c_cp1p_copyBack_1_p6", Arrow(config(Constructor("p6", []), c(alpha), d(beta)), config(Constructor("cp1p_copyBack_1", []), c(s(alpha)), d(beta))));
        ("NZ_d_cp2p_copyBack_1_cp3p_copyBack_1", Arrow(config(Constructor("cp3p_copyBack_1", []), c(alpha), d(s(beta))), config(Constructor("cp2p_copyBack_1", []), c(alpha), d(s(beta)))));
        ("Z_d_cp2p_copyBack_1_q", Arrow(config(Constructor("q", []), c(alpha), d(zero)), config(Constructor("cp2p_copyBack_1", []), c(alpha), d(zero))));
        ("DEC_d_cp3p_copyBack_1_cp4p_copyBack_1", Arrow(config(Constructor("cp4p_copyBack_1", []), c(alpha), d(beta)), config(Constructor("cp3p_copyBack_1", []), c(alpha), d(s(beta)))));
        ("INC_c_cp4p_copyBack_1_cp2p_copyBack_1", Arrow(config(Constructor("cp2p_copyBack_1", []), c(s(alpha)), d(beta)), config(Constructor("cp4p_copyBack_1", []), c(alpha), d(beta))));
        ("DEC_c_q_q1", Arrow(config(Constructor("q1", []), c(alpha), d(beta)), config(Constructor("q", []), c(s(alpha)), d(beta))));
        ("Z_c_q1_twoCounter_fail", Arrow(config(Constructor("twoCounter_fail", []), c(zero), d(beta)), config(Constructor("q1", []), c(zero), d(beta))));
        ("NZ_c_q1_q2", Arrow(config (Constructor("q2", []), c(s(alpha)), d(beta)), config(Constructor("q1", []), c(s(alpha)), d(beta))));
        ("INC_c_q2_q3", Arrow(config(Constructor("q3", []), c(s(alpha)), d(beta)), config(Constructor("q2", []), c(alpha), d(beta))));
        ("NZ_c_q3_md1q", Arrow(config (Constructor("md1q", []), c(s(alpha)), d(beta)), config(Constructor("q3", []), c(s(alpha)), d(beta))));
        ("Z_c_q3_q4", Arrow(config(Constructor("q4", []), c(zero), d(beta)), config(Constructor("q3", []), c(zero), d(beta))));
        ("DEC_c_md1q_md2q", Arrow(config(Constructor("md2q", []), c(alpha), d(beta)), config(Constructor("md1q", []), c(s(alpha)), d(beta))));
        ("NZ_c_md2q_md4q", Arrow(config (Constructor("md4q", []), c(s(alpha)), d(beta)), config(Constructor("md2q", []), c(s(alpha)), d(beta))));
        ("Z_c_md2q_md3q", Arrow(config(Constructor("md3q", []), c(zero), d(beta)), config(Constructor("md2q", []), c(zero), d(beta))));
        ("INC_c_md3q_q4", Arrow(config(Constructor("q4", []), c(s(alpha)), d(beta)), config(Constructor("md3q", []), c(alpha), d(beta))));
        ("DEC_c_md4q_md5q", Arrow(config(Constructor("md5q", []), c(alpha), d(beta)), config(Constructor("md4q", []), c(s(alpha)), d(beta))));
        ("INC_d_md5q_q3", Arrow(config(Constructor("q3", []), c(alpha), d(s(beta))), config(Constructor("md5q", []), c(alpha), d(beta))));
        ("Z_c_q4_q5", Arrow(config(Constructor("q5", []), c(zero), d(beta)), config(Constructor("q4", []), c(zero), d(beta))));
        ("NZ_c_q5_cp1q_copyBack_0", Arrow(config (Constructor("cp1q_copyBack_0", []), c(s(alpha)), d(beta)), config(Constructor("q5", []), c(s(alpha)), d(beta))));
        ("Z_c_q5_cp2q_copyBack_0", Arrow(config(Constructor("cp2q_copyBack_0", []), c(zero), d(beta)), config(Constructor("q5", []), c(zero), d(beta))));
        ("DEC_c_cp1q_copyBack_0_q5", Arrow(config(Constructor("q5", []), c(alpha), d(beta)), config(Constructor("cp1q_copyBack_0", []), c(s(alpha)), d(beta))));
        ("NZ_d_cp2q_copyBack_0_cp3q_copyBack_0", Arrow(config(Constructor("cp3q_copyBack_0", []), c(alpha), d(s(beta))), config(Constructor("cp2q_copyBack_0", []), c(alpha), d(s(beta)))));
        ("Z_d_cp2q_copyBack_0_q", Arrow(config(Constructor("q", []), c(alpha), d(zero)), config(Constructor("cp2q_copyBack_0", []), c(alpha), d(zero))));
        ("DEC_d_cp3q_copyBack_0_cp4q_copyBack_0", Arrow(config(Constructor("cp4q_copyBack_0", []), c(alpha), d(beta)), config(Constructor("cp3q_copyBack_0", []), c(alpha), d(s(beta)))));
        ("INC_c_cp4q_copyBack_0_cp2q_copyBack_0", Arrow(config(Constructor("cp2q_copyBack_0", []), c(s(alpha)), d(beta)), config(Constructor("cp4q_copyBack_0", []), c(alpha), d(beta))));
        ("NZ_c_q4_q6", Arrow(config (Constructor("q6", []), c(s(alpha)), d(beta)), config(Constructor("q4", []), c(s(alpha)), d(beta))));
        ("NZ_c_q6_cp1q_copyBack_1", Arrow(config (Constructor("cp1q_copyBack_1", []), c(s(alpha)), d(beta)), config(Constructor("q6", []), c(s(alpha)), d(beta))));
        ("Z_c_q6_cp2q_copyBack_1", Arrow(config(Constructor("cp2q_copyBack_1", []), c(zero), d(beta)), config(Constructor("q6", []), c(zero), d(beta))));
        ("DEC_c_cp1q_copyBack_1_q6", Arrow(config(Constructor("q6", []), c(alpha), d(beta)), config(Constructor("cp1q_copyBack_1", []), c(s(alpha)), d(beta))));
        ("NZ_d_cp2q_copyBack_1_cp3q_copyBack_1", Arrow(config(Constructor("cp3q_copyBack_1", []), c(alpha), d(s(beta))), config(Constructor("cp2q_copyBack_1", []), c(alpha), d(s(beta)))));
        ("Z_d_cp2q_copyBack_1_p", Arrow(config(Constructor("p", []), c(alpha), d(zero)), config(Constructor("cp2q_copyBack_1", []), c(alpha), d(zero))));
        ("DEC_d_cp3q_copyBack_1_cp4q_copyBack_1", Arrow(config(Constructor("cp4q_copyBack_1", []), c(alpha), d(beta)), config(Constructor("cp3q_copyBack_1", []), c(alpha), d(s(beta)))));
        ("INC_c_cp4q_copyBack_1_cp2q_copyBack_1", Arrow(config(Constructor("cp2q_copyBack_1", []), c(s(alpha)), d(beta)), config(Constructor("cp4q_copyBack_1", []), c(alpha), d(beta))));
        ("FIN_twoCounter_accept", config(Constructor("twoCounter_accept", []), c(alpha), d(beta)))
        ] 

    
    let constructGoal (input : string) =
        let x = "1" + new string(Array.rev (input.ToCharArray()))
        let inputNumber = System.Convert.ToInt32(x, 2)
        let mutable encoded_number = zero
        for i = 1 to inputNumber do
            encoded_number <- s encoded_number
        config(Constructor("p", []), c(encoded_number), d(zero))

    //input = "1" (+ "1" as termination token: [1 @ rev(1)]_2 = [11]_2 = 3), odd parity : no inhabitants
    //let goal = config(Constructor("p", []), c(s(s(s(zero)))), d(zero))
    
    //input = "110" (+ "1" as termination token: [1 @ rev(110)]_2 = [1011]_2 = 3), even parity : at least one inhabitant
    //let goal = config(Constructor("p", []), c(s(s(s(s(s(s(s(s(s(s(s(zero)))))))))))), d(zero))
    
    //input = "1001000110", time : 86s
    //let goal = constructGoal "1001000110"

    //input = "100100011", time : 29s
    //let goal = constructGoal "100100011"

    //input = "100100011", time : 29s
    let goal = constructGoal "100000011"

    //input = "10100011", odd parity : no inhabitants
    //let goal = constructGoal "10000011"

    //input = "10100011"
    //let goal = constructGoal "10100011"

    //input = "1010011"
    //let goal = constructGoal "1010011"

    //input = "101011"
    //let goal = constructGoal "101011"

    //input = "10111"
    //let goal = constructGoal "10111"

    //input = "1001"
    //let goal = constructGoal "1001"

    //input = "11"
    //let goal = constructGoal "11"
    runExperiment 4000 isSubtype context goal