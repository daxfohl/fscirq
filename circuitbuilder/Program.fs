open System
open DynamicInvoke

let inline (^%) f = f

module Map =
  let set k f m = Map.change k (function None -> None | Some v -> Some ^% f v) m
  let singleton k v = Map.empty |> Map.add k v

let getpath root name = 
  if String.IsNullOrEmpty root then name
  elif String.IsNullOrEmpty name then root
  else root + "." + name

type Qubit = int ref
type Args =
| CVal of bool
| CObj of Map<string, Args>
  with  
  member this.get path =
    if String.IsNullOrEmpty path then this
    else
      match this with
      | CObj m ->
          let split = path.Split(".")
          m.[split.[0]].get (String.Join('.', Array.tail split))
      | _ -> failwith "Not an object"
  member this.b path =
    match this.get path with
    | CVal b -> b
    | _ -> failwith "Not a cval"

type ArgsParam =
| ArgsParam of int

type InputArgs =
| ALocal of string
| AArgsParam of ArgsParam * string

type BoolParam =
| BoolParam of int

type InputBool =
| BBool of bool
| BLocal of string
| BParam of BoolParam
| BArgsParam of ArgsParam * string

type QubitParam =
| QubitParam of int

type InputQubit =
| QQubit of Qubit
| QParam of QubitParam

type Input =
| IQubit of InputQubit
| IBool of InputBool
| IArgs of InputArgs

type Param =
| PQubit of QubitParam
| PBool of BoolParam
| PArg of ArgsParam
let toparam = function
| PQubit x -> box x
| PBool x -> box x
| PArg x -> box x

let argsparamcounter = ref 0
let newArgsParam() = 
  incr argsparamcounter
  PArg ^% ArgsParam(!argsparamcounter)
let boolparamcounter = ref 0
let newBoolParam() = 
  incr boolparamcounter
  PBool ^% BoolParam(!boolparamcounter)
let qubitparamcounter = ref 0
let newQubitParam() = 
  incr qubitparamcounter
  PQubit ^% QubitParam(!qubitparamcounter)

type Operation =
| Subcircuit of name:string * circuit:obj * inputs:Input list
| Gate of qubit:InputQubit
| GateIf of qubit:InputQubit * b:InputBool
| Measure of name:string * qubit:InputQubit

type Value =
| VQubit of Qubit
| VArg of Args
| VBool of bool

type Circuit = string * Operation list

let rec runOp paramvals localvalues op =
  let objlocalvalues = CObj localvalues
  let qval = function
  | QQubit q -> q
  | QParam p ->  let (VQubit q) = paramvals |> Map.find ^% PQubit p in q
  let bval = function
  | BBool b -> b
  | BLocal path -> objlocalvalues.b path
  | BParam p -> let (VBool b) = paramvals |> Map.find ^% PBool p in b
  | BArgsParam (p, path) -> let (VArg a) = paramvals |> Map.find ^% PArg p in a.b path
  let aval = function
  | ALocal path -> objlocalvalues.get path
  | AArgsParam (p, path) -> let (VArg a) = paramvals |> Map.find ^% PArg p in a.get path
  match op with
  | Measure (name, q) ->
    let q = qval q
    Map.add name (CVal (!q % 2 = 0)) localvalues
  | Gate q ->
    let q = qval q
    incr q
    localvalues
  | GateIf (q, b) ->
    let b = bval b
    if b then runOp paramvals localvalues (Gate q) else localvalues
  | Subcircuit (name, circuitFactory, inputs) ->
    let reify = function
    | IQubit q -> newQubitParam(), VQubit (qval q)
    | IBool b -> newBoolParam(), VBool (bval b)
    | IArgs a -> newArgsParam(), VArg (aval a)
    let oinputs = List.map reify inputs
    let inputparams = oinputs |> List.map fst |> List.map toparam
    let _, circuit = dynamicFunction circuitFactory inputparams :?> Circuit
    let parameters = oinputs |> Map.ofList
    let resp = List.fold (runOp parameters) Map.empty circuit
    Map.add name (CObj resp) localvalues
let run parameters = List.fold (runOp parameters) Map.empty

type ParamVal =
| PVPath of string
| PVValue of Value
let rec flattenOp (paramPaths: Map<Param, ParamVal>) path op =
  let fullpath = getpath path
  match op with
  | Measure (name, q) -> [Measure (fullpath name, q)]
  | Gate q -> [Gate q]
  | GateIf (q, b) -> [GateIf (q, b)]
  | Subcircuit (name, circuitFactory, inputs) ->
    let localize = function
    | IQubit q ->
      match q with
      | QQubit q -> newQubitParam(), PVValue ^% VQubit q
      | QParam p -> PQubit p, paramPaths |> Map.find ^% PQubit p
    | IBool b ->
      match b with
      | BBool b -> newBoolParam(), PVValue ^% VBool b
      | BLocal path' -> newBoolParam(), PVPath ^% fullpath path'
      | BParam p -> PBool p, paramPaths |> Map.find ^% PBool p
      | BArgsParam (p, path') ->
        (PArg p,
          match paramPaths |> Map.find ^% PArg p with
            | PVPath x -> PVPath ^% getpath x path'
            | PVValue v -> PVValue v)
    | IArgs a ->
      match a with
      | ALocal path' -> newArgsParam(), PVPath ^% fullpath path'
      | AArgsParam (p, path') -> 
        (PArg p,
          match paramPaths |> Map.find ^% PArg p with
            | PVPath x -> PVPath ^% getpath x path'
            | PVValue v -> PVValue v)
    let oinputs = inputs |> List.map localize
    let inputparams = oinputs |> List.map fst |> List.map toparam
    let _, circuit = dynamicFunction circuitFactory inputparams :?> Circuit
    let parameters = oinputs |> Map.ofList
    let simplifyB = function
    | BBool b -> BBool b
    | BLocal path' -> BLocal path'
    | BParam p -> 
      match oinputs |> List.find (fun (p', _) -> p' = PBool p) |> snd with
      | PVPath p -> BLocal p
      | PVValue (VBool b) -> BBool b
    | BArgsParam (p, path') -> 
      match oinputs |> List.find (fun (p', _) -> p' = PArg p) |> snd with
      | PVPath p -> BLocal (getpath p path')
      | PVValue (VBool b) -> BBool b

    let simplify op =
      match op with
      | GateIf (q, b) -> GateIf (q, simplifyB b)
      | Measure (name, q) -> Measure (name, q)
      | Gate q -> Gate q
      | Subcircuit (name, circuitFactory, inputs) -> Subcircuit (name, circuitFactory, inputs)
    circuit |> List.map simplify |> List.collect ^% (flattenOp parameters) ^% fullpath name
let flatten parameters = List.collect ^% (flattenOp parameters) null



let subsubcircuit q =
  "subsubcircuit",
  [
    Gate ^% QParam q
    Measure ("m1", QParam q)
    Gate ^% QParam q
    Measure ("m2", QParam q)
    Gate ^% QParam q
    Measure ("m3", QParam q)
  ]

let doit q c =
  "doit",
  [
    GateIf (QParam q, BArgsParam(c, "m1"))
  ]

let doit2 q b =
  "doit2",
  [
    GateIf (QParam q, BParam b)
  ]

let doit3 q b =
  "doit3",
  [
    Subcircuit ("z3", doit2, [IQubit ^% QParam q; IBool ^% BParam b])
  ]
  
let doit4 q b =
  "doit4",
  [
    Subcircuit ("z4", doit3, [IQubit ^% QParam q; IBool ^% BParam b])
  ]
    
let doit5 q =
  "doit5",
  [
    Subcircuit ("z5", doit4, [IQubit ^% QParam q; IBool ^% BBool false])
  ]

let subcircuit q =
  "subcircuit",
  [
    Subcircuit ("a", subsubcircuit, [IQubit ^% QParam q])
    Subcircuit ("b", subsubcircuit, [IQubit ^% QParam q])
    Subcircuit ("c", subsubcircuit, [IQubit ^% QParam q])
    Subcircuit ("x", doit, [IQubit ^% QParam q; IArgs (ALocal "b")])
    //Subcircuit ("y", doit2, [IQubit ^% QParam q; IBool (BLocal "b.m1")])
    //Subcircuit ("z", doit2, [IQubit ^% QParam q; IBool (BBool false)])
    //Subcircuit ("z2", doit2, [IQubit ^% QParam q; IBool (BBool true)])
  ]

let circuit q =
  "circuit",
  [
    Subcircuit ("a", subcircuit, [IQubit ^% QParam q])
    Subcircuit ("b", subcircuit, [IQubit ^% QParam q])
    Subcircuit ("c", subcircuit, [IQubit ^% QParam q])
    Subcircuit ("x", doit, [IQubit ^% QParam q; IArgs (ALocal "c.b")])
  ]
  
let zzz q =
  "zzz",
  [
    Subcircuit ("a", subsubcircuit, [IQubit ^% QParam q])
    Subcircuit ("x", doit, [IQubit ^% QParam q; IArgs (ALocal "a")])
    Subcircuit ("x1", doit2, [IQubit ^% QParam q; IBool (BBool false)])
    Subcircuit ("x2", doit2, [IQubit ^% QParam q; IBool (BLocal "a.m1")])
    Subcircuit ("x3", doit4, [IQubit ^% QParam q; IBool (BLocal "a.m1")])
    Subcircuit ("x3", doit5, [IQubit ^% QParam q])
  ]
  
type QasmLine = string
type QasmLines = QasmLine list
type Register =
| ROutput of string
| RBool of string
| RQubit of string
  with
  member this.name() =
    match this with
    | ROutput name -> name
    | RBool name -> name
    | RQubit name -> name
let getargname (r:Register) = r.name()
type Registers = Register list
type OperationDef = QasmLine * Registers
type CircuitDef = QasmLines * Registers
type CircuitName = string
type CircuitDefMap = Map<CircuitName, CircuitDef>
type WasmState = QubitParam list * BoolParam list * CircuitDefMap
let rec wasmOp (state:WasmState) (op:Operation): OperationDef * WasmState =
  let qparams, bparams, subcircuits = state
  let getindex a = List.findIndex ^% fun a' -> a = a'
  let qname = function
  | QParam a -> sprintf "Q%d" ^% getindex a qparams
  let qof = function | QParam a -> a
  match op with
  | Measure (name, q) -> ("M " + name + " <- " + qname q, [ROutput name; RQubit (qname q)]), state
  | Gate q -> ("G " + qname q, [RQubit(qname q)]), state
  | GateIf (q, b) ->
    let bpart, bregs, bparams =
      match b with
      | BBool b -> b.ToString(), [], []
      | BLocal path -> path, [ROutput path], []
      | BParam a -> let name = sprintf "B%d" ^% getindex a bparams in name, [RBool (name)], [a]
      | BArgsParam (args, path) -> failwith "not yet"
    ("G " + qname q + " IF " + bpart, (RQubit(qname q))::bregs), state
  | Subcircuit (name, circuitFactory, inputs) ->
    let localize = function
    | IQubit q ->
      match q with
      | QQubit q -> newQubitParam()
      | QParam p -> PQubit p
    | IBool b ->
      match b with
      | BBool b -> newBoolParam()
      | BLocal path' -> newBoolParam()
      | BParam p -> PBool p
      | BArgsParam (p, path') -> PArg p
    | IArgs a ->
      match a with
      | ALocal path' -> newArgsParam()
      | AArgsParam (p, path') ->  PArg p
    let oinputs = inputs |> List.map localize
    let inputparams = oinputs |> List.map toparam
    let circuit = dynamicFunction circuitFactory inputparams :?> Circuit
    let circuitname = fst circuit
    let subqparams = oinputs |> List.choose(fun p -> match p with | PQubit q -> Some q | _ -> None)
    let subbparams = oinputs |> List.choose(fun p -> match p with | PBool b -> Some b | _ -> None)
    let circuits = wasmCircuit (subqparams, subbparams, subcircuits) circuit
    let registers = Map.find circuitname circuits |> snd
    let qargs = subqparams |> List.map(fun p -> RQubit(sprintf "Q%d" ^% getindex p qparams))
    let bargs = subbparams |> List.map(fun p -> RBool(sprintf "Q%d" ^% getindex p bparams))
    let rargs = registers |> List.choose(fun r -> match r with | ROutput n -> Some(ROutput(getpath name n)) | _ -> None)
    let args = List.concat [qargs;bargs;rargs]
    let str = "CALL " + circuitname + " " + String.Join(' ', args |> List.map getargname)
    (str, args), (qparams, bparams, circuits)
and wasmCircuit (state:WasmState) (circuit:Circuit): CircuitDefMap =
  let name, ops = circuit
  let output, (qparams, bparams, subcircuits) = List.mapFold wasmOp state ops
  subcircuits |> Map.add name (List.map fst output, List.concat [List.mapi (fun i _ -> RQubit (sprintf "Q%d" i)) qparams; List.mapi (fun i _ -> RBool (sprintf "B%d" i)) bparams;  List.collect snd output] |> List.distinct)
  
  
let doit0 q0 q1 =
  "doit0",
  [
    Measure ("m1", QParam q1)
    Measure ("m0", QParam q0)
    GateIf (QParam q0, BLocal "m1")
  ]
  
let doit00 q b =
  "doit00",
  [
    GateIf (QParam q, BParam b)
  ]
  
  
let xxx q =
  "xxx",
  [
    Measure ("m1", QParam q)
    Subcircuit ("x3", doit00, [IQubit ^% QParam q; IBool ^% BLocal "m1"])
  ]

  
let doit000 q a =
  "doit000",
  [
    GateIf (QParam q, BArgsParam(a, "m1"))
  ]
  
let xxx0 q =
  "xxx0",
  [
    Measure ("m1", QParam q)
    Subcircuit ("x3", doit000, [IQubit ^% QParam q; IArgs ^% ALocal ""])
  ]


let doit0000 q a =
  "doit0000",
  [
    GateIf (QParam q, BArgsParam(a, ""))
  ]

let xxx00 q =
  "xxx00",
  [
    Measure ("m1", QParam q)
    Subcircuit ("x3", doit0000, [IQubit ^% QParam q; IArgs ^% ALocal "m1"])
  ]

[<EntryPoint>]
let main argv =
  //let q = ref 0
  //let qubitparam = newQubitParam()
  //let x = run (Map.singleton qubitparam (VQubit q)) [Subcircuit("ASDFASGADGFSDFGSD", circuit, [IQubit (QQubit q)])]
  //printfn "%A" x
  //printfn "%A" q
  //let decompose sc =
  //  let xs = flatten (Map.singleton (PQubit (QubitParam 0)) (PVPath "BBBBBBBBBBBB")) [Subcircuit("x", sc, [IQubit (QParam (QubitParam 0))])]
  //  for x in xs do
  //    printfn "%A" x
  //  printfn ""
    
  //decompose doit0
  //decompose xxx
  //decompose xxx0
  //decompose xxx00
  //decompose zzz
  let wasm = wasmCircuit ([QubitParam 0; QubitParam 1], [], Map.empty) ("adsf", [Subcircuit("x", doit0, [IQubit (QParam (QubitParam 0));IQubit (QParam (QubitParam 1))])])
  for x in wasm do
    let name, (output, args) = x.Deconstruct()
    printfn ""
    printfn "def %s %A:" name ^% List.map id args
    printfn "  %s" (String.Join("\n  ", output))
  let expectedargs =
    [ 
      "Q0";
      "C_a_a_m1"; "C_a_a_m2"; "C_a_a_m3";
      "C_a_b_m1"; "C_a_b_m2"; "C_a_b_m3";
      "C_a_c_m1"; "C_a_c_m2"; "C_a_c_m3";
      "C_b_a_m1"; "C_b_a_m2"; "C_b_a_m3";
      "C_b_b_m1"; "C_b_b_m2"; "C_b_b_m3";
      "C_b_c_m1"; "C_b_c_m2"; "C_b_c_m3";
      "C_c_a_m1"; "C_c_a_m2"; "C_c_a_m3";
      "C_c_b_m1"; "C_c_b_m2"; "C_c_b_m3";
      "C_c_c_m1"; "C_c_c_m2"; "C_c_c_m3";
    ]

  let expectedoutput = 
    [
      "CALL subcircuit Q0 C_a_a_m1 C_a_a_m2 C_a_a_m3 C_a_b_m1 C_a_b_m2 C_a_b_m3 C_a_c_m1 C_a_c_m2 C_a_c_m3"
      "CALL subcircuit Q0 C_b_a_m1 C_b_a_m2 C_b_a_m3 C_b_b_m1 C_b_b_m2 C_b_b_m3 C_b_c_m1 C_b_c_m2 C_b_c_m3"
      "CALL subcircuit Q0 C_c_a_m1 C_c_a_m2 C_c_a_m3 C_c_b_m1 C_c_b_m2 C_c_b_m3 C_c_c_m1 C_c_c_m2 C_c_c_m3"
      "CALL doit Q0 C_c_b_m1"
    ]

  0
