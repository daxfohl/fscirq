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
  | QVal of Qubit
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
  member this.q path =
    match this.get path with
    | QVal q -> q
    | _ -> failwith "Not a qval"

type InputArgs =
  | AArgs of Args
  | ALocal of string
  | AGlobal of string
  with
  member this.get (localArgs:Args) =
    match this with
    | AArgs args -> args
    | ALocal path -> localArgs.get path
    | AGlobal path -> localArgs.get path
  member this.sub path =
    match this with
    | AArgs args -> AArgs ^% args.get path
    | ALocal root -> ALocal ^% getpath root path
    | AGlobal root -> AGlobal ^% getpath root path
type InputQubit =
  | QQubit of Qubit
  | QArgs of InputArgs * string
  | QLocal of string
  | QGlobal of string
  with
  member this.get (localArgs:Args) =
    match this with
    | QQubit q -> q
    | QArgs (args, path) -> (args.get localArgs).q path
    | QLocal path -> localArgs.q path
    | QGlobal path -> localArgs.q path
  static member fromArgs(inputArgs, path) =
    match inputArgs with
    | AArgs args -> QQubit (args.q path)
    | ALocal root -> QLocal ^% getpath root path
    | AGlobal root -> QGlobal ^% getpath root path

type InputBool =
  | BBool of bool
  | BArgs of InputArgs * string
  | BLocal of string
  | BGlobal of string
  with
  member this.get (localArgs:Args) =
    match this with
    | BBool b -> b
    | BArgs (args, path) -> (args.get localArgs).b path
    | BLocal path -> localArgs.b path
    | BGlobal path -> localArgs.b path
    
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
let rec runOp args op =
  let objargs = CObj args
  match op with
  | Measure (name, q) ->
    let q = q.get objargs
    Map.add name (CVal (!q % 2 = 0)) args
  | Gate q ->
    let q = q.get objargs
    incr q
    args
  | GateIf (q, b) ->
    let b = b.get objargs
    if b then runOp args (Gate q) else args
  | Subcircuit (name, circuitFactory, inputs) ->
    let reify inputs =
      let args = CObj args
      match inputs with
      | IQubit q -> box ^% QQubit ^% q.get args
      | IBool b -> box ^% BBool ^% b.get args
      | IArgs a -> box ^% AArgs ^% a.get args
    let oinputs = List.map reify inputs
    let _, circuit = dynamicFunction circuitFactory oinputs :?> Circuit
    let resp = List.fold runOp Map.empty circuit
    Map.add name (CObj resp) args
let run = List.fold runOp


let rec flattenOp path op =
  let getpath = getpath path
  match op with
  | Measure (name, q) ->
    [Measure (getpath name, q)]
  | Gate q ->
    [Gate q]
  | GateIf (q, b) ->
    [GateIf (q, b)]
  | Subcircuit (name, circuitFactory, inputs) ->
    let localize = function
    | IQubit q ->
      match q with
      | QLocal path' -> box (QGlobal ^% getpath path')
      | _ -> box q
    | IBool b ->
      match b with
      | BLocal path' -> box (BGlobal ^% getpath path')
      | _ -> box b
    | IArgs a ->
      match a with
      | ALocal path' -> box (AGlobal ^% getpath path')
      | _ -> box a
    let oinputs = inputs |> List.map localize
    let _, circuit = dynamicFunction circuitFactory oinputs :?> Circuit
    circuit |> List.collect ^% flattenOp ^% getpath name
let flatten = List.collect ^% flattenOp null



let subsubcircuit q =
  "subsubcircuit",
  [
    Gate q
    Measure ("m1", q)
    Gate q
    Measure ("m2", q)
    Gate q
    Measure ("m3", q)
  ]

let doit q c =
  "doit",
  [
    GateIf (q, BArgs(c, "m1"))
  ]

let doit2 q b =
  "doit2",
  [
    GateIf (q, b)
  ]

let doit3 q b =
  "doit3",
  [
    Subcircuit ("z3", doit2, [IQubit q; IBool b])
  ]

let doit4 q b =
  "doit4",
  [
    Subcircuit ("z4", doit3, [IQubit q; IBool b])
  ]

let subcircuit q =
  "subcircuit",
  [
    Subcircuit ("a", subsubcircuit, [IQubit q])
    Subcircuit ("b", subsubcircuit, [IQubit q])
    Subcircuit ("c", subsubcircuit, [IQubit q])
    Subcircuit ("x", doit, [IQubit q; IArgs (ALocal "b")])
  ]

let circuit q =
  "circuit",
  [
    Subcircuit ("a", subcircuit, [IQubit q])
    Subcircuit ("b", subcircuit, [IQubit q])
    Subcircuit ("c", subcircuit, [IQubit q])
    Subcircuit ("x", doit, [IQubit q; IArgs (ALocal "c.b")])
  ]
  
let zzz q =
  "zzz",
  [
    Subcircuit ("a", subsubcircuit, [IQubit q])
    Subcircuit ("x", doit, [IQubit q; IArgs (ALocal "a")])
    Subcircuit ("x1", doit2, [IQubit q; IBool (BBool false)])
    Subcircuit ("x2", doit2, [IQubit q; IBool (BLocal "a.m1")])
    Subcircuit ("x3", doit4, [IQubit q; IBool (BLocal "a.m1")])
  ]


let rec wasmOp inputs subcircuits op =
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
      | BArgs (args, path) -> 
        let bname = argname args + path
        "C[" + bname + "]", [bname]
      | BLocal path -> "C[" + path + "]", []
      | BGlobal path -> "C[global::" + path + "]", []
    ("G Q[" + argname q + "] IF " + bpart, (argname q)::bargs), subcircuits
  | Subcircuit (name, circuitFactory, inputs) ->
    let localize = function
    | IQubit _ -> box ^% QQubit ^% ref 0
    | IBool _ -> box ^% BBool false
    | IArgs _ -> box ^% AArgs ^% CVal false
    let oinputs = inputs |> List.map localize
    let circuit = dynamicFunction circuitFactory oinputs :?> Circuit
    let circuitname = fst circuit
    let circuits = wasmCircuit oinputs subcircuits circuit
    let args = Map.find circuitname circuits |> snd |> List.map ^% fun p -> name + "." + p
    let str = "CALL " + circuitname + " " + String.Join(' ', args)
    (str, args), circuits
and wasmCircuit inputs subcircuits circuit =
  let name, ops = circuit
  let folder = wasmOp inputs
  let output, subcircuits = ops |> List.mapFold folder subcircuits
  subcircuits |> Map.add name (List.map fst output, List.collect snd output |> List.distinct)

[<EntryPoint>]
let main argv =
  let q = ref 0
  let x = run Map.empty ^% snd ^% circuit ^% QQubit q
  printfn "%A" x
  printfn "%A" ^% flatten ^% snd ^% zzz ^% QQubit q
  let wasm = wasmCircuit [QQubit q] Map.empty ^% circuit ^% QQubit q
  let output, args = wasm.["circuit"]
  // spec:
  // first the input args, in same order as spec, subpaths in order of use in fn
  // then output args, in order of use in fn
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

  printfn "%A" output
  printfn "%A" args
  0