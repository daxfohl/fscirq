open System
let inline (^%) f = f

module Map =
  let set k f m = Map.change k (function None -> None | Some v -> Some ^% f v) m
  let singleton k v = Map.empty |> Map.add k v

type Qubit = int ref
type CArg =
  | CVal of bool
  | CObj of Map<string, CArg>
  with  
    member this.get path =
      match this with
        | CObj m ->
            if String.IsNullOrEmpty path then this
            else
              let split = path.Split(".")
              m.[split.[0]].get (String.Join('.', Array.tail split))
        | _ -> failwith "Not an object"
    member this.b path =
      if String.IsNullOrEmpty path then
        match this with
          | CVal b -> b
          | _ -> failwith "Not a leaf"
      else
        match this with
          | CObj m ->
              let split = path.Split(".")
              m.[split.[0]].b (String.Join('.', Array.tail split))
          | _ -> failwith "Not an object"
        

  
type TArgs<'T, 'U> = Map<string, 'T> * Map<string, 'U>
type Args = TArgs<Qubit, CArg>
type NameMap = (string * string) list
type ArgsMap = NameMap * NameMap

type Circuit = Operation list
and Operation =
  | Subcircuit of args:ArgsMap * circuit:Circuit * name:string
  | Gate of qubit:string
  | GateIf of qubit:string * path:string
  | Measure of qubit:string * name:string



let rec run args circuit =
  circuit |> List.fold runOp args
and runOp ((qvars, cvars) as args:Args) operation =
  match operation with
  | Measure (q, name) ->
      let q = Map.find q qvars
      let cvars = Map.add name (CVal (!q % 2 = 0)) cvars
      qvars, cvars
  | Gate q ->
      incr ^% Map.find q qvars
      args
  | GateIf (q, cvar) ->
      if (CObj cvars).b cvar then runOp args (Gate q) else args
  | Subcircuit ((qmap, cmap), circuit, name) ->
      let qargs = qmap |> List.map (fun (k, v) -> k, qvars.[v]) |> Map.ofList
      let cargs = cmap |> List.map (fun (k, v) -> k, (CObj cvars).get v) |> Map.ofList
      let _, c = run (qargs, cargs) circuit
      qvars, Map.add name (CObj c) cvars

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
    Subcircuit ((["q", "q"],  []), subsubcircuit, "a")
    Subcircuit ((["q", "q"],  []), subsubcircuit, "b")
    Subcircuit ((["q", "q"],  []), subsubcircuit, "c")
    Subcircuit ((["q", "q"],  ["c", "b"]), doit, "x")
  ]

let circuit =
  [
    Subcircuit ((["q", "q"], []), subcircuit, "a")
    Subcircuit ((["q", "q"], []), subcircuit, "b")
    Subcircuit ((["q", "q"], []), subcircuit, "c")
    Subcircuit ((["q", "q"], ["c", "b.b"]), doit, "x")
  ]


[<EntryPoint>]
let main argv =
  let q = ref 0
  let x = run ((Map.singleton "q" q), Map.empty) circuit
  printfn "%A" circuit
  0 // return an integer exit code
