module Utils

open Microsoft.FSharp.Compiler.SourceCodeServices
open System.IO
open System
open FSharpEnvironment

let fakeDateTimeRepresentingTimeLoaded x = DateTime(abs (int64 (match x with null -> 0 | _ -> x.GetHashCode())) % 103231L)

type FSharpChecker with
    member checker.GetScriptCheckerOptions fileName =
      async { 
        try 
            let projectFileName = Path.ChangeExtension(fileName, ".fsproj")
            let src = File.ReadAllText fileName
            let! opts = checker.GetProjectOptionsFromScript(fileName, src, fakeDateTimeRepresentingTimeLoaded projectFileName)
                
            let results =
                if opts.OtherOptions |> Seq.exists (fun s -> s.Contains("FSharp.Core.dll")) then
                    let dirs = FSharpEnvironment.getDefaultDirectories(FSharpCompilerVersion.FSharp_3_1, FSharpTargetFramework.NET_4_5)
                    FSharpEnvironment.resolveAssembly dirs "FSharp.Core"
                    |> Option.map (fun path -> 
                        let fsharpCoreRef = sprintf "-r:%s" path
                        { opts with OtherOptions = [| yield fsharpCoreRef
                                                      yield! opts.OtherOptions |> Seq.filter (fun s -> not (s.Contains "FSharp.Core.dll")) |] })
                    |> function Some x -> x | None -> opts
                else 
                    let dirs = FSharpEnvironment.getDefaultDirectories(FSharpCompilerVersion.FSharp_3_1, FSharpTargetFramework.NET_4_5)
                    { opts with OtherOptions =  [|  yield! opts.OtherOptions
                                                    match FSharpEnvironment.resolveAssembly dirs "FSharp.Core" with
                                                    | Some fn -> yield sprintf "-r:%s" fn
                                                    | None -> ()
                                                    match FSharpEnvironment.resolveAssembly dirs "FSharp.Compiler.Interactive.Settings" with
                                                    | Some fn -> yield sprintf "-r:%s" fn
                                                    | None -> () |] }
              
            return results
        with e -> 
            return failwithf "Exception when getting check options for '%s'\n.Details: %A" fileName e
      }

