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

type Operation =
  | Subcircuit of name:string * circuit:Operation list * args:ArgsMap
  | Gate of qubit:string
  | GateIf of qubit:string * path:string
  | Measure of name:string * qubit:string



let rec runOp args = function
  | Measure (name, q) ->
      let q = (CObj args).q q
      Map.add name (CVal (!q % 2 = 0)) args
  | Gate q ->
      incr ^% (CObj args).q q
      args
  | GateIf (q, cvar) ->
      if (CObj args).b cvar then runOp args (Gate q) else args
  | Subcircuit (name, circuit, argmap) ->
      let qcargs = argmap |> List.map (fun (k, v) -> k, (CObj args).get v) |> Map.ofList
      let resp = List.fold runOp qcargs circuit
      Map.add name (CObj resp) args

let run = List.fold runOp

let subsubcircuit =
  [
    Gate "q"
    Measure ("m1", "q")
    Gate "q"
    Measure ("m2", "q")
    Gate "q"
    Measure ("m3", "q")
  ]

let doit =
  [
    GateIf ("q", "c.m1")
  ]

let subcircuit =
  [
    Subcircuit ("a", subsubcircuit, ["q", "q"])
    Subcircuit ("b", subsubcircuit, ["q", "q"])
    Subcircuit ("c", subsubcircuit, ["q", "q"])
    Subcircuit ("x", doit, ["q", "q"; "c", "b"])
  ]

let circuit =
  [
    Subcircuit ("a", subcircuit, ["q", "q"])
    Subcircuit ("b", subcircuit, ["q", "q"])
    Subcircuit ("c", subcircuit, ["q", "q"])
    Subcircuit ("x", doit, ["q", "q"; "c", "c.b"])
  ]


[<EntryPoint>]
let main argv =
  let q = ref 0
  let x = run (Map.singleton "q" (QVal q)) circuit
  printfn "%A" x
  0 // return an integer exit code
