open System
open DynamicInvoke

let inline (^%) f = f

module Map =
  let set k f m = Map.change k (function None -> None | Some v -> Some ^% f v) m
  let singleton k v = Map.empty |> Map.add k v

let getpath root name = if String.IsNullOrEmpty root then name else root + "." + name
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
| APConst of Args
| APGlobal of string

type InputArgs =
| ALocal of string
| AArgsParam of ArgsParam * string
  with
  member this.get (localArgs:Args) =
    match this with
    | AArgsParam (APConst args, path) -> args.get path
    | ALocal path -> localArgs.get path
    | _ -> failwith "Not a value"

type BoolParam =
| BPConst of bool
| BPGlobal of string
  with 
  member this.get() =
    match this with
    | BPConst b -> b
    | _ -> failwith "Not a value"

type InputBool =
| BBool of bool
| BLocal of string
| BParam of BoolParam
| BArgsParam of ArgsParam * string
  with 
  member this.get (localargs: Args) =
    match this with
    | BBool b -> b
    | BLocal path -> localargs.b path
    | BParam bparam -> bparam.get()
    | BArgsParam (APConst args, path) -> args.b path
    | _ -> failwith "Not a value"

type QubitParam =
| QPConst of Qubit
  with 
  member this.get() =
    match this with
    | QPConst q -> q

type InputQubit =
| QParam of QubitParam
  with 
  member this.get () =
    match this with
    | QParam qparam -> qparam.get()

type Input =
| IQubit of InputQubit
| IBool of InputBool
| IArgs of InputArgs

type Operation =
| Subcircuit of name:string * circuit:obj * inputs:Input list
| Gate of qubit:InputQubit
| GateIf of qubit:InputQubit * b:InputBool
| Measure of name:string * qubit:InputQubit

type Circuit = string * Operation list


type QasmLine = string
type QasmLines = QasmLine list
type Register = string
type Registers = Register list
type OperationDef = QasmLine * Registers
type CircuitDef = QasmLines * Registers
type CircuitName = string
type CircuitDefMap = Map<CircuitName, CircuitDef>
let rec wasmOp inputs (subcircuits:CircuitDefMap) (op:Operation): OperationDef * CircuitDefMap =
  let argname a = sprintf "ARG_%d" (inputs |> List.findIndex ^% fun a' -> obj.ReferenceEquals(a, a'))
  match op with
  | Measure (name, q) ->
    ("M C[" + name + "] <- Q[" + argname q + "]", [name; argname q]), subcircuits
  | Gate q ->
    ("G Q[" + argname q + "]", [argname q]), subcircuits
  | GateIf (q, b) ->
    let bpart, bargs =
      match b with
      | BBool b -> b.ToString(), []
      | BLocal path -> "C_" + path, []
      | BParam bparam -> bparam.get()
      | BArgsParam (APConst args, path) -> args.b path
      | BArgs (args, path) -> 
        let bname = argname args + path
        "C[" + bname + "]", [bname]
    ("G Q[" + argname q + "] IF " + bpart, (argname q)::bargs), subcircuits
  | Subcircuit (name, circuitFactory, inputs) ->
    let localize = function
    | IQubit _ -> box ^% QQubit ^% ref 0
    | IBool _ -> box ^% BBool false
    | IArgs _ -> box ^% AArgs ^% CVal false
    let oinputs = inputs |> List.map localize
    let circuit = dynamicFunction circuitFactory oinputs :?> Circuit
    let circuitname = fst circuit
    let circuits = wasmCircuit subcircuits circuit
    let args = Map.find circuitname circuits |> snd |> List.map ^% fun p -> name + "." + p
    let str = "CALL " + circuitname + " " + String.Join(' ', args)
    (str, args), circuits
and wasmCircuit (subcircuits:CircuitDefMap) (circuit:Circuit): CircuitDefMap =
  let name, ops = circuit
  let folder = wasmOp []
  let output, subcircuits = List.mapFold folder subcircuits ops
  subcircuits |> Map.add name (List.map fst output, List.collect snd output |> List.distinct)


let rec runOp args op =
  let objargs = CObj args
  match op with
  | Measure (name, q) ->
    let q = q.get ()
    Map.add name (CVal (!q % 2 = 0)) args
  | Gate q ->
    let q = q.get ()
    incr q
    args
  | GateIf (q, b) ->
    let b = b.get objargs
    if b then runOp args (Gate q) else args
  | Subcircuit (name, circuitFactory, inputs) ->
    let reify inputs =
      let args = CObj args
      match inputs with
      | IQubit q -> box ^% QPConst ^% q.get ()
      | IBool b -> box ^% BPConst ^% b.get args
      | IArgs a -> box ^% APConst ^% a.get args
    let oinputs = List.map reify inputs
    let _, circuit = dynamicFunction circuitFactory oinputs :?> Circuit
    let resp = List.fold runOp Map.empty circuit
    Map.add name (CObj resp) args
let run = List.fold runOp


let rec flattenOp path op =
  let rootpath = getpath path
  match op with
  | Measure (name, q) -> [Measure (rootpath name, q)]
  | Gate q -> [Gate q]
  | GateIf (q, b) -> [GateIf (q, b)]
  | Subcircuit (name, circuitFactory, inputs) ->
    let localize = function
    | IQubit q ->
      box ^%
      match q with
      | QParam p -> p
    | IBool b ->
      box ^%
      match b with
      | BBool c -> BPConst c
      | BLocal path' -> BPGlobal ^% rootpath path'
      | BParam p -> p
      | BArgsParam (APGlobal path, path') -> BPGlobal ^% getpath path path'
    | IArgs a ->
      box ^%
      match a with
      | ALocal path' -> APGlobal ^% rootpath path'
      | AArgsParam (APGlobal path, path') -> APGlobal ^% getpath path path'
      | _ -> failwith "Not a value"
    let oinputs = inputs |> List.map localize
    let _, circuit = dynamicFunction circuitFactory oinputs :?> Circuit
    circuit |> List.collect ^% flattenOp ^% rootpath name
let flatten = List.collect ^% flattenOp null



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

let subcircuit q =
  "subcircuit",
  [
    Subcircuit ("a", subsubcircuit, [IQubit ^% QParam q])
    Subcircuit ("b", subsubcircuit, [IQubit ^% QParam q])
    Subcircuit ("c", subsubcircuit, [IQubit ^% QParam q])
    Subcircuit ("x", doit, [IQubit ^% QParam q; IArgs (ALocal "b")])
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
  ]

[<EntryPoint>]
let main argv =
  let q = ref 0
  let x = run Map.empty ^% snd ^% circuit ^% QPConst q
  printfn "%A" x
  printfn "%A" q
  printfn "%A" ^% flatten ^% snd ^% zzz (QPConst q)
  let wasm = wasmCircuit Map.empty ^% circuit ^% QPConst q
  let output, args = wasm.["circuit"]
  printfn "%A" output
  printfn "%A" args
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