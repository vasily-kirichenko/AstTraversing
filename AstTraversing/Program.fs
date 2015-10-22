open Microsoft.FSharp.Compiler.SourceCodeServices
open Utils
open System.IO

[<EntryPoint>]
let main argv = 
    let checker = FSharpChecker.Create()
    let ast = 
        async {
            let! opts = checker.GetScriptCheckerOptions(Path.GetFullPath "Script.fsx")
            let file = "Script.fsx"
            let! results = checker.ParseFileInProject (file, File.ReadAllText file, opts)
            return results.ParseTree
        } |> Async.RunSynchronously

    let longIdents = 
        TraverseWithRecursiveFunctions.getLongIdents ast 
        |> Seq.map (fun (KeyValue (_, idents)) -> idents)
        |> Seq.toList

    printfn "Recursive functions result: %A" longIdents
    0 