open System
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
        

  
type ArgsMap = (string * string) list

type Circuit = Operation list
and Operation =
  | Subcircuit of args:ArgsMap * circuit:Circuit * name:string
  | Gate of qubit:string
  | GateIf of qubit:string * path:string
  | Measure of qubit:string * name:string



let rec run args circuit =
  circuit |> List.fold runOp args
and runOp args operation =
  match operation with
  | Measure (q, name) ->
      let q = (CObj args).q q
      Map.add name (CVal (!q % 2 = 0)) args
  | Gate q ->
      incr ^% (CObj args).q q
      args
  | GateIf (q, cvar) ->
      if (CObj args).b cvar then runOp args (Gate q) else args
  | Subcircuit (argmap, circuit, name) ->
      let qcargs = argmap |> List.map (fun (k, v) -> k, (CObj args).get v) |> Map.ofList
      let resp = run qcargs circuit
      Map.add name (CObj resp) args

let subsubcircuit =
  [
    Gate "q"
    Measure ("q", "m1")
    Gate "q"
    Measure ("q", "m2")
    Gate "q"
    Measure ("q", "m3")
  ]

let doit =
  [
    GateIf ("q", "c.m1")
  ]

let subcircuit =
  [
    Subcircuit ((["q", "q"]), subsubcircuit, "a")
    Subcircuit ((["q", "q"]), subsubcircuit, "b")
    Subcircuit ((["q", "q"]), subsubcircuit, "c")
    Subcircuit ((["q", "q"; "c", "b"]), doit, "x")
  ]

let circuit =
  [
    Subcircuit ((["q", "q"]), subcircuit, "a")
    Subcircuit ((["q", "q"]), subcircuit, "b")
    Subcircuit ((["q", "q"]), subcircuit, "c")
    Subcircuit ((["q", "q"; "c", "b.b"]), doit, "x")
  ]


[<EntryPoint>]
let main argv =
  let q = ref 0
  let x = run (Map.singleton "q" (QVal q)) circuit
  printfn "%A" x
  0 // return an integer exit code
