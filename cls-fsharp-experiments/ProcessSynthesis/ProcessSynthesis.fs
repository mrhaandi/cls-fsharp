module CLS.Experiments.ProcessSynthesis

open CLS.Model.Type
open CLS.Experiments.BenchmarkUtil
open CLS.Algorithm

//binds weakest (supposed to be used for scala types only)
let ( **=> ) (source : IntersectionType) (target : IntersectionType) =
  getConst ("'" + (Arrow(source, target)).ToString() + "'")

//right associative
let ( ^-> ) (source : IntersectionType) (target : IntersectionType) =
  Arrow(source, target)

//binds strongest
let (-&) (left : IntersectionType) (right : IntersectionType) =
  getIntersect [left; right] |> Type.simplifyType

let run_ProcessSynthesis () = 
    let Zero = getConst "Zero"
    let One = getConst "One"

    let Sensors x = Constructor("Sensors", [x])
    let Robot x = Constructor("Robot", [x])
    let Motor x = Constructor("Motor", [x])
    let StopSensor x = Constructor("StopSensor", [x])
    let Job x = Constructor("Job", [x])
    let Direction x = Constructor("Direction", [x])
    let SensorOp x = Constructor("SensorOp", [x])

    let car = Robot (getConst "car")
    let twoLightSensors = Sensors (getConst "twoLightSensors")
    let m2 = Motor (getConst "m2")
    let m3 = Motor (getConst "m3")
    let touchSensor = StopSensor (getConst "touchSensor")
    let followsLine = Job (getConst "followsLine")
    let forward = Direction (getConst "forward")
    let turnRight = Direction (getConst "turnRight")
    let turnLeft = Direction (getConst "turnLeft")
    let stop = Direction (getConst "stop")
    let rightLightSensor = StopSensor (getConst "rightLightSensor")
    let leftLightSensor = StopSensor (getConst "leftLightSensor")
    let read = SensorOp (getConst "read")
    let set = SensorOp (getConst "set")

    let proc = getConst "proc"
    let condition = getConst "condition"


    let result = getConst "result"
    let guarded = getConst "guarded"
    
    let jobProc = getConst "jobProc"
   
    
    let abort = getConst "abort"
    let request = getConst "request"
    let evaluated = getConst "evaluated"


    let moveProc = getConst "moveProc"
    let wsBuildFct = getConst "wsBuildFct"
  
    let robotProgram = getConst "robotProgram"

    let Pair (x, y) = Constructor("Pair", [x; y])
    let Tuple2 (x, y) = Constructor("Tuple2", [x; y])
    let Triple (x, y, z) = Constructor("Triple", [x; y; z])

    let WsArrows_this_WsCallSpecType = getConst "WsArrows_this_WsCallSpecType" 
    let play_api_libs_ws_WSResponse = getConst "play_api_libs_ws_WSResponse"
    let WsMovementProc_this_WsCallSpecType = getConst "WsMovementProc_this_WsCallSpecType"
    let WsMovementProc_this_ControlMotorsSpecType = getConst "WsMovementProc_this_ControlMotorsSpecType"
    let java_lang_Runnable = getConst "java_lang_Runnable"
    let WsInit_this_WsCallSpecType = getConst "WsInit_this_WsCallSpecType"
    let CarRobotProgramBase_this_WsCallSpecType = getConst "CarRobotProgramBase_this_WsCallSpecType"
    let CarRobotProgramBase_this_ControlMotorsSpecType = getConst "CarRobotProgramBase_this_ControlMotorsSpecType"
    let WsInit_this_TlSensorsSpecType = getConst "WsInit_this_TlSensorsSpecType"
    let WsProcResult_this_TlSensorsSpecType = getConst "WsProcResult_this_TlSensorsSpecType"
    let WsProcResult_this_WsCallSpecType = getConst "WsProcResult_this_WsCallSpecType"
    let WsProcResult_this_TlSensorsReadResultType = getConst "WsProcResult_this_TlSensorsReadResultType"
    let WsProcResult_this_TouchSensorSpecType = getConst "WsProcResult_this_TouchSensorSpecType"
    let WsProcResult_this_TouchSensorReadResultType = getConst "WsProcResult_this_TouchSensorReadResultType"
    let WsUtil_this_WsCallSpecType = getConst "WsUtil_this_WsCallSpecType"

    let scala_Unit = getConst "scala_Unit"
    let scala_Int = getConst "scala_Int"
    let scala_Boolean = getConst "scala_Boolean"
    let String = getConst "String"
    let scala_xml_Elem = getConst "scala_xml_Elem"
    
    let scala_concurrent_Future x = Constructor("scala_concurrent_Future", x)
    let java_util_concurrent_Callable x = Constructor("java_util_concurrent_Callable", x)


    let alpha = Sensors (Var "alpha") //sensor configuration: twoLightSensors
    let gamma = Robot (Var "gamma") //robot shape: car
    let alpha1 = Motor (Var "alpha1") //motor: m2, m3
    let beta = StopSensor (Var "beta")
    let delta = Job (Var "delta")
    let beta2 = Direction (Var "beta2")
    let beta1 = Direction (Var "beta1")
    let alpha0 = StopSensor (Var "alpha0")

    let gamma0 = SensorOp (Var "gamma0")

    let dualSensors = Var "dualSensors"
    let stopSensor = Var "stopSensor"
    
    let isSubtype x y = x = y

    let context = 
        [
            ("StopCondition", scala_Int **=> scala_Boolean -& touchSensor -& condition -& abort -& car);
            
            ("ArrowComposeWsEval2", (WsArrows_this_WsCallSpecType **=> Pair(scala_concurrent_Future[play_api_libs_ws_WSResponse], String) ^-> (Pair(scala_concurrent_Future[play_api_libs_ws_WSResponse], String)) **=> scala_Unit ^-> WsArrows_this_WsCallSpecType **=> scala_Unit) -& ((alpha0 -& gamma0 ^-> alpha0 -& gamma0 -& request) ^-> (alpha0 -& gamma0 -& request ^-> alpha0 -& gamma0 -& evaluated) ^-> alpha0 -& gamma0 ^-> alpha0 -& gamma0 -& evaluated) -& ((alpha1 -& beta1 ^-> alpha1 -& beta1 -& request) ^-> (alpha1 -& beta1 -& request ^-> alpha1 -& beta1 -& evaluated) ^-> alpha1 -& beta1 ^-> alpha1 -& beta1 -& evaluated));
            
            ("M2Forward", Pair(Triple(String, String, scala_xml_Elem), String) -& m2 -& forward);
            
            ("TouchSensorReadCombinator", Pair(Triple(String, String, scala_xml_Elem), String) -& touchSensor -& read);
            
            ("SetCombinator", (Pair(Triple(String, String, scala_xml_Elem), String) ^-> Pair(Triple(String, String, scala_xml_Elem), String) ^-> Pair(WsUtil_this_WsCallSpecType, WsUtil_this_WsCallSpecType)) -& (leftLightSensor -& gamma0 ^-> rightLightSensor -& gamma0 ^-> Tuple2(leftLightSensor -& gamma0, rightLightSensor -& gamma0)) -& (m2 -& stop ^-> m3 -& stop ^-> Tuple2(m2 -& stop, m3 -& stop)) -& (m2 -& stop ^-> m3 -& forward ^-> Tuple2(m2 -& stop, m3 -& forward)) -& (m2 -& forward ^-> m3 -& stop ^-> Tuple2(m2 -& forward, m3 -& stop)) -& (m2 -& forward ^-> m3 -& forward ^-> Tuple2(m2 -& forward, m3 -& forward)));
            
            ("RightLightSensorReadCombinator", Pair(Triple(String, String, scala_xml_Elem), String) -& rightLightSensor -& read);
            
            ("MovementProc", (Pair(WsMovementProc_this_WsCallSpecType, WsMovementProc_this_WsCallSpecType) ^-> WsMovementProc_this_ControlMotorsSpecType **=> Pair(scala_Unit, scala_Unit) ^-> scala_Unit) -& (Tuple2(m2 -& stop, m3 -& forward) ^-> (Tuple2(m2 -& stop, m3 -& forward) ^-> turnRight -& car -& evaluated) ^-> turnRight -& car -& proc) -& (Tuple2(m2 -& forward, m3 -& forward) ^-> (Tuple2(m2 -& forward, m3 -& forward) ^-> forward -& car -& evaluated) ^-> forward -& car -& proc) -& (Tuple2(m2 -& stop, m3 -& stop) ^-> (Tuple2(m2 -& stop, m3 -& stop) ^-> stop -& car -& evaluated) ^-> stop -& car -& proc) -& (Tuple2(m2 -& forward, m3 -& stop) ^-> (Tuple2(m2 -& forward, m3 -& stop) ^-> turnLeft -& car -& evaluated) ^-> turnLeft -& car -& proc));
            
            ("ConditionalMovesProc", ((Pair(scala_Int, scala_Int)) **=> scala_Unit ^-> (Pair(scala_Int, scala_Int)) **=> scala_Unit ^-> (Pair(scala_Int, scala_Int)) **=> scala_Unit ^-> (Pair(scala_Int, scala_Int)) **=> Pair(Pair(scala_Unit, scala_Unit), scala_Unit)) -& ((twoLightSensors -& read -& result ^-> guarded -& twoLightSensors -& followsLine -& turnRight -& car -& proc) ^-> (twoLightSensors -& read -& result ^-> guarded -& twoLightSensors -& followsLine -& turnLeft -& car -& proc) ^-> (twoLightSensors -& read -& result ^-> guarded -& twoLightSensors -& followsLine -& forward -& car -& proc) ^-> twoLightSensors -& followsLine -& car -& moveProc));
            
            ("EvalCall2", (Pair(scala_concurrent_Future[play_api_libs_ws_WSResponse], String)) **=> scala_Unit -& (alpha1 -& beta1 -& request ^-> alpha1 -& beta1 -& evaluated));
            
            ("WsSensorCall", (Triple(String, String, scala_xml_Elem)) **=> scala_concurrent_Future[play_api_libs_ws_WSResponse] -& wsBuildFct);
            
            ("BetaProc", (Pair(Triple(String, String, scala_xml_Elem), String) ^-> WsInit_this_WsCallSpecType **=> scala_Int ^-> java_lang_Runnable) -& (touchSensor -& set ^-> (touchSensor -& set ^-> touchSensor -& set -& evaluated) ^-> touchSensor -& set -& proc));
            
            ("StopProc", (Pair(CarRobotProgramBase_this_WsCallSpecType, CarRobotProgramBase_this_WsCallSpecType) ^-> CarRobotProgramBase_this_ControlMotorsSpecType **=> Pair(scala_Unit, scala_Unit) ^-> java_lang_Runnable) -& (Tuple2(m2 -& stop, m3 -& stop) ^-> (Tuple2(m2 -& stop, m3 -& stop) ^-> stop -& car -& evaluated) ^-> stop -& car -& proc));
            
            ("ArrowComposeWsEval", (WsArrows_this_WsCallSpecType **=> Pair(scala_concurrent_Future[play_api_libs_ws_WSResponse], String) ^-> (Pair(scala_concurrent_Future[play_api_libs_ws_WSResponse], String)) **=> scala_Int ^-> WsArrows_this_WsCallSpecType **=> scala_Int) -& ((alpha0 -& gamma0 ^-> alpha0 -& gamma0 -& request) ^-> (alpha0 -& gamma0 -& request ^-> alpha0 -& gamma0 -& evaluated) ^-> alpha0 -& gamma0 ^-> alpha0 -& gamma0 -& evaluated) -& ((alpha1 -& beta1 ^-> alpha1 -& beta1 -& request) ^-> (alpha1 -& beta1 -& request ^-> alpha1 -& beta1 -& evaluated) ^-> alpha1 -& beta1 ^-> alpha1 -& beta1 -& evaluated));
            
            ("M3Stop", Pair(Triple(String, String, scala_xml_Elem), String) -& m3 -& stop);
            
            ("ArrowFirstWsRequestBuildEval", ((Triple(String, String, scala_xml_Elem)) **=> scala_concurrent_Future[play_api_libs_ws_WSResponse] ^-> (Pair(Triple(String, String, scala_xml_Elem), String)) **=> Pair(scala_concurrent_Future[play_api_libs_ws_WSResponse], String)) -& (wsBuildFct ^-> alpha0 -& gamma0 ^-> alpha0 -& gamma0 -& request) -& (wsBuildFct ^-> alpha1 -& beta1 ^-> alpha1 -& beta1 -& request));
            
            ("ConditionTwoLightSensorsTurnLeft", (Pair(scala_Int, scala_Int)) **=> scala_Boolean -& condition -& twoLightSensors -& followsLine -& turnLeft -& car);
            
            ("RightLightSensorInitCombinator", Pair(Triple(String, String, scala_xml_Elem), String) -& rightLightSensor -& set);
            
            ("MoveProcCombinator", (java_util_concurrent_Callable[Pair(scala_Int, scala_Int)] ^-> (Pair(scala_Int, scala_Int)) **=> Pair(Pair(scala_Unit, scala_Unit), scala_Unit) ^-> java_lang_Runnable) -& (twoLightSensors -& read -& proc ^-> twoLightSensors -& followsLine -& car -& moveProc ^-> twoLightSensors -& followsLine -& car -& read -& moveProc));
            
            ("ConditionTwoLightSensorsTurnRight", (Pair(scala_Int, scala_Int)) **=> scala_Boolean -& condition -& twoLightSensors -& followsLine -& turnRight -& car);
            
            ("GuardedProcCombinator", (scala_Unit ^-> (Pair(scala_Int, scala_Int)) **=> scala_Boolean ^-> (Pair(scala_Int, scala_Int)) **=> scala_Unit) -& (beta2 -& car -& proc ^-> condition -& twoLightSensors -& followsLine -& beta2 -& car ^-> twoLightSensors -& read -& result ^-> guarded -& twoLightSensors -& followsLine -& beta2 -& car -& proc));
            
            //("AlphaProc", (Pair(WsInit_this_WsCallSpecType, WsInit_this_WsCallSpecType) ^-> WsInit_this_TlSensorsSpecType **=> Pair(scala_Int, scala_Int) ^-> java_lang_Runnable) -& (Tuple2(leftLightSensor -& gamma0, rightLightSensor -& gamma0) ^-> (Tuple2(leftLightSensor -& gamma0, rightLightSensor -& gamma0) ^-> twoLightSensors -& gamma0 -& evaluated) ^-> twoLightSensors -& gamma0 -& proc));
            
            ("AlphaProc", (Pair(WsInit_this_WsCallSpecType, WsInit_this_WsCallSpecType) ^-> WsInit_this_TlSensorsSpecType **=> Pair(scala_Int, scala_Int) ^-> java_lang_Runnable) -& (Tuple2(leftLightSensor -& set, rightLightSensor -& set) ^-> (Tuple2(leftLightSensor -& set, rightLightSensor -& set) ^-> twoLightSensors -& set -& evaluated) ^-> twoLightSensors -& set -& proc));
            
            ("M3Forward", Pair(Triple(String, String, scala_xml_Elem), String) -& m3 -& forward);
            
            ("ArrowComposeWsControlSensor", (WsArrows_this_WsCallSpecType **=> scala_concurrent_Future[play_api_libs_ws_WSResponse] ^-> scala_concurrent_Future[play_api_libs_ws_WSResponse] **=> scala_Unit ^-> WsArrows_this_WsCallSpecType **=> scala_Unit) -& ((alpha1 -& beta1 ^-> alpha1 -& beta1 -& request) ^-> (alpha1 -& beta1 -& request ^-> alpha1 -& beta1 -& evaluated) ^-> alpha1 -& beta1 ^-> alpha1 -& beta1 -& evaluated));
            
            ("LeftLightSensorInitCombinator", Pair(Triple(String, String, scala_xml_Elem), String) -& leftLightSensor -& set);
            
            ("M2Stop", Pair(Triple(String, String, scala_xml_Elem), String) -& m2 -& stop);
            
            ("TouchSensorResult", (java_util_concurrent_Callable[scala_Int] ^-> scala_Int) -& (stopSensor -& gamma0 -& proc ^-> stopSensor -& gamma0 -& result));
            
            ("ArrowTwoSens", (WsArrows_this_WsCallSpecType **=> scala_Int ^-> WsArrows_this_WsCallSpecType **=> scala_Int ^-> (Pair(WsArrows_this_WsCallSpecType, WsArrows_this_WsCallSpecType)) **=> Pair(scala_Int, scala_Int)) -& ((leftLightSensor -& gamma0 ^-> leftLightSensor -& gamma0 -& evaluated) ^-> (rightLightSensor -& gamma0 ^-> rightLightSensor -& gamma0 -& evaluated) ^-> Tuple2(leftLightSensor -& gamma0, rightLightSensor -& gamma0) ^-> twoLightSensors -& gamma0 -& evaluated));
            
            ("ArrowComposeWsLightSensor", (WsArrows_this_WsCallSpecType **=> scala_concurrent_Future[play_api_libs_ws_WSResponse] ^-> scala_concurrent_Future[play_api_libs_ws_WSResponse] **=> scala_Int ^-> WsArrows_this_WsCallSpecType **=> scala_Int) -& ((alpha0 -& gamma0 ^-> alpha0 -& gamma0 -& request) ^-> (alpha0 -& gamma0 -& request ^-> alpha0 -& gamma0 -& evaluated) ^-> alpha0 -& gamma0 ^-> alpha0 -& gamma0 -& evaluated));
            
            ("ConditionTwoLightSensorsForward", (Pair(scala_Int, scala_Int)) **=> scala_Boolean -& condition -& twoLightSensors -& followsLine -& forward -& car);
            
            ("CreateRobotProgram", (java_lang_Runnable ^-> java_lang_Runnable ^-> java_lang_Runnable ^-> java_lang_Runnable ^-> java_lang_Runnable) -& (proc -& alpha -& set ^-> proc -& beta -& set ^-> alpha -& beta -& gamma -& delta -& jobProc ^-> proc -& gamma -& stop ^-> alpha -& beta -& gamma -& delta -& robotProgram));
            
            ("EvalCall", (Pair(scala_concurrent_Future[play_api_libs_ws_WSResponse], String)) **=> scala_Int -& (alpha0 -& gamma0 -& request ^-> alpha0 -& gamma0 -& evaluated));
            
            ("ReadCallable", (java_util_concurrent_Callable[Pair(scala_Int, scala_Int)] ^-> Pair(scala_Int, scala_Int)) -& (dualSensors -& gamma0 -& proc ^-> dualSensors -& gamma0 -& result));
            
            ("StopsOnTouchInitCombinator", Pair(Triple(String, String, scala_xml_Elem), String) -& touchSensor -& set);
            
            ("LeftLightSensorReadCombinator", Pair(Triple(String, String, scala_xml_Elem), String) -& leftLightSensor -& read);
            
            ("ApplyCombinatorTwoLightSensors", (Pair(WsProcResult_this_WsCallSpecType, WsProcResult_this_WsCallSpecType) ^-> WsProcResult_this_TlSensorsSpecType **=> WsProcResult_this_TlSensorsReadResultType ^-> java_util_concurrent_Callable[WsProcResult_this_TlSensorsReadResultType]) -& (Tuple2(leftLightSensor -& gamma0, rightLightSensor -& gamma0) ^-> (Tuple2(leftLightSensor -& gamma0, rightLightSensor -& gamma0) ^-> twoLightSensors -& gamma0 -& evaluated) ^-> twoLightSensors -& gamma0 -& proc));
            
            ("JobProcCombinator", (java_util_concurrent_Callable[scala_Int] ^-> scala_Int **=> scala_Boolean ^-> java_lang_Runnable ^-> java_lang_Runnable) -& (touchSensor -& read -& proc ^-> touchSensor -& condition -& abort -& car ^-> twoLightSensors -& followsLine -& car -& read -& moveProc ^-> twoLightSensors -& touchSensor -& car -& followsLine -& jobProc));
            
            ("ArrowSplitMovementFunctions", (WsArrows_this_WsCallSpecType **=> scala_Unit ^-> WsArrows_this_WsCallSpecType **=> scala_Unit ^-> (Pair(WsArrows_this_WsCallSpecType, WsArrows_this_WsCallSpecType)) **=> Pair(scala_Unit, scala_Unit)) -& ((m2 -& forward ^-> m2 -& forward -& evaluated) ^-> (m3 -& forward ^-> m3 -& forward -& evaluated) ^-> Tuple2(m2 -& forward, m3 -& forward) ^-> forward -& car -& evaluated) -& ((m2 -& stop ^-> m2 -& stop -& evaluated) ^-> (m3 -& stop ^-> m3 -& stop -& evaluated) ^-> Tuple2(m2 -& stop, m3 -& stop) ^-> stop -& car -& evaluated) -& ((m2 -& forward ^-> m2 -& forward -& evaluated) ^-> (m3 -& stop ^-> m3 -& stop -& evaluated) ^-> Tuple2(m2 -& forward, m3 -& stop) ^-> turnLeft -& car -& evaluated) -& ((m2 -& stop ^-> m2 -& stop -& evaluated) ^-> (m3 -& forward ^-> m3 -& forward -& evaluated) ^-> Tuple2(m2 -& stop, m3 -& forward) ^-> turnRight -& car -& evaluated));
            
            ("ApplyCombinatorTouchSensor", (Pair(Triple(String, String, scala_xml_Elem), String) ^-> WsProcResult_this_TouchSensorSpecType **=> WsProcResult_this_TouchSensorReadResultType ^-> java_util_concurrent_Callable[WsProcResult_this_TouchSensorReadResultType]) -& (touchSensor -& gamma0 ^-> (touchSensor -& gamma0 ^-> touchSensor -& gamma0 -& evaluated) ^-> touchSensor -& gamma0 -& proc));
        ]
            
    let goal = twoLightSensors -& touchSensor -& car -& followsLine -& robotProgram

    runExperiment 1000 isSubtype context goal