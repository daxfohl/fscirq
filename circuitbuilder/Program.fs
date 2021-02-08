open System
open DynamicInvoke

let inline (^%) f = f

module Map =
  let set k f m = Map.change k (function None -> None | Some v -> Some ^% f v) m
  let singleton k v = Map.empty |> Map.add k v

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

type InputQubit =
  | QQubit of Qubit
  | QArgs of Args * string
  | QLocal of string
  with
    member this.get (localArgs:Args) =
      match this with
        | QQubit q -> q
        | QArgs (args, path) -> args.q path
        | QLocal path -> localArgs.q path

type InputBool =
  | BBool of bool
  | BArgs of Args * string
  | BLocal of string
  with
    member this.get (localArgs:Args) =
      match this with
        | BBool b -> b
        | BArgs (args, path) -> args.b path
        | BLocal path -> localArgs.b path

type InputArgs =
  | AArgs of Args * string
  | ALocal of string
  with
    member this.get (localArgs:Args) =
      match this with
        | AArgs (args, path) -> args.get path
        | ALocal path -> localArgs.get path
        
type Input =
  | IQubit of InputQubit
  | IBool of InputBool
  | IArgs of InputArgs
  with
    member this.get args =
      match this with
        | IQubit q -> box ^% q.get args
        | IBool b -> box ^% b.get args
        | IArgs a -> box ^% a.get args

type Operation =
  | Subcircuit of name:string * circuit:obj * inputs:Input list
  | Gate of qubit:InputQubit
  | GateIf of qubit:InputQubit * b:InputBool
  | Measure of name:string * qubit:InputQubit


let rec runOp args = function
  | Measure (name, q) ->
      let q = q.get (CObj args)
      Map.add name (CVal (!q % 2 = 0)) args
  | Gate q ->
      let q = q.get (CObj args)
      incr q
      args
  | GateIf (q, b) ->
      let b = b.get (CObj args)
      if b then runOp args (Gate q) else args
  | Subcircuit (name, circuitFactory, inputs) ->
      let oinputs = inputs |> List.map (fun i -> i.get (CObj args))
      let circuit = dynamicFunction circuitFactory oinputs :?> Operation list
      let resp = List.fold runOp Map.empty circuit
      Map.add name (CObj resp) args

let run = List.fold runOp
let subsubcircuit q =
  [
    Gate (QQubit q)
    Measure ("m1", QQubit q)
    Gate (QQubit q)
    Measure ("m2", QQubit q)
    Gate (QQubit q)
    Measure ("m3", QQubit q)
  ]

let doit q c =
  [
    GateIf (QQubit q, BArgs(c, "b.m1"))
  ]

let subcircuit q =
  [
    Subcircuit ("a", subsubcircuit, [IQubit (QQubit q)])
    Subcircuit ("b", subsubcircuit, [IQubit (QQubit q)])
    Subcircuit ("c", subsubcircuit, [IQubit (QQubit q)])
    Subcircuit ("x", doit, [IQubit (QQubit q); IArgs (ALocal "b")])
  ]

let circuit q =
  [
    Subcircuit ("a", subcircuit, [IQubit (QQubit q)])
    Subcircuit ("b", subcircuit, [IQubit (QQubit q)])
    Subcircuit ("c", subcircuit, [IQubit (QQubit q)])
    Subcircuit ("x", doit, [IQubit (QQubit q); IArgs (ALocal "c.b")])
  ]


[<EntryPoint>]
let main argv =
  let q = ref 0
  let x = run Map.empty (circuit q)
  printfn "%A" x
  0 // return an integer exit code
