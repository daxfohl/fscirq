module DynamicInvoke

open FSharp.Reflection

let dynamicFunction (fn:obj) (args:obj seq) =
    let rec dynamicFunctionInternal (next:obj) (args:obj list) : obj =
        match args.IsEmpty with
        | false ->
            let fType = next.GetType()
            if FSharpType.IsFunction fType then
                let (head, tail) = (args.Head, args.Tail)
                let methodInfo = 
                    fType.GetMethods()
                    |> Seq.filter (fun x -> x.Name = "Invoke" && x.GetParameters().Length = 1)
                    |> Seq.head
                let partalResult = methodInfo.Invoke(next, [| head |])
                dynamicFunctionInternal partalResult tail
            else failwith "Not a function"
        | true -> next
    dynamicFunctionInternal fn (args |> List.ofSeq )