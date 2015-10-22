module TraverseWithRecursiveFunctions

open Microsoft.FSharp.Compiler.Ast
open System.Collections.Generic
open Microsoft.FSharp.Compiler

type ShortIdent = string
type Idents = ShortIdent[]

let longIdentToArray (longIdent: LongIdent): Idents =
    longIdent |> Seq.map string |> Seq.toArray

/// An recursive pattern that collect all sequential expressions to avoid StackOverflowException
let rec (|Sequentials|_|) = function
    | SynExpr.Sequential(_, _, e, Sequentials es, _) ->
        Some(e::es)
    | SynExpr.Sequential(_, _, e1, e2, _) ->
        Some [e1; e2] 
    | _ -> None

let (|ConstructorPats|) = function
    | SynConstructorArgs.Pats ps -> ps
    | SynConstructorArgs.NamePatPairs(xs, _) -> List.map snd xs

/// Returns all Idents and LongIdents found in an untyped AST.
let getLongIdents (input: ParsedInput option) : IDictionary<Range.pos, Idents> =
    let identsByEndPos = Dictionary<Range.pos, Idents>()

    let addLongIdent (longIdent: LongIdent) =
        let idents = longIdentToArray longIdent
        for ident in longIdent do
            identsByEndPos.[ident.idRange.End] <- idents

    let addLongIdentWithDots (LongIdentWithDots (longIdent, lids) as value) = 
        match longIdentToArray longIdent with
        | [||] -> ()
        | [|_|] as idents -> identsByEndPos.[value.Range.End] <- idents
        | idents ->
            for dotRange in lids do 
                identsByEndPos.[Range.mkPos dotRange.EndLine (dotRange.EndColumn - 1)] <- idents
            identsByEndPos.[value.Range.End] <- idents
    
    let addIdent (ident: Ident) = 
        identsByEndPos.[ident.idRange.End] <- [|ident.idText|]

    let rec walkImplFileInput (ParsedImplFileInput(_, _, _, _, _, moduleOrNamespaceList, _)) = 
        List.iter walkSynModuleOrNamespace moduleOrNamespaceList

    and walkSynModuleOrNamespace (SynModuleOrNamespace(_, _, decls, _, attrs, _, _)) =
        List.iter walkAttribute attrs
        List.iter walkSynModuleDecl decls

    and walkAttribute (attr: SynAttribute) = 
        addLongIdentWithDots attr.TypeName 
        walkExpr attr.ArgExpr

    and walkTyparDecl (SynTyparDecl.TyparDecl (attrs, typar)) = 
        List.iter walkAttribute attrs
        walkTypar typar
            
    and walkTypeConstraint = function
        | SynTypeConstraint.WhereTyparDefaultsToType (t1, t2, _) -> 
            walkTypar t1
            walkType t2
        | SynTypeConstraint.WhereTyparIsValueType(t, _) -> walkTypar t
        | SynTypeConstraint.WhereTyparIsReferenceType(t, _) -> walkTypar t
        | SynTypeConstraint.WhereTyparIsUnmanaged(t, _) -> walkTypar t
        | SynTypeConstraint.WhereTyparSupportsNull (t, _) -> walkTypar t
        | SynTypeConstraint.WhereTyparIsComparable(t, _) -> walkTypar t
        | SynTypeConstraint.WhereTyparIsEquatable(t, _) -> walkTypar t
        | SynTypeConstraint.WhereTyparSubtypeOfType(t, ty, _) -> 
            walkTypar t
            walkType ty
        | SynTypeConstraint.WhereTyparSupportsMember(ts, sign, _) -> 
            List.iter walkTypar ts 
            walkMemberSig sign
        | SynTypeConstraint.WhereTyparIsEnum(t, ts, _) -> 
            walkTypar t
            List.iter walkType ts
        | SynTypeConstraint.WhereTyparIsDelegate(t, ts, _) -> 
            walkTypar t
            List.iter walkType ts

    and walkPat = function
        | SynPat.Ands (pats, _) -> List.iter walkPat pats
        | SynPat.Named (pat, ident, _, _, _) -> 
            walkPat pat
            addIdent ident
        | SynPat.Typed(pat, t, _) -> 
            walkPat pat
            walkType t
        | SynPat.Attrib(pat, attrs, _) -> 
            walkPat pat
            List.iter walkAttribute attrs
        | SynPat.Or(pat1, pat2, _) -> List.iter walkPat [pat1; pat2]
        | SynPat.LongIdent(ident, _, typars, ConstructorPats pats, _, _) -> 
            addLongIdentWithDots ident
            typars
            |> Option.iter (fun (SynValTyparDecls (typars, _, constraints)) ->
                 List.iter walkTyparDecl typars
                 List.iter walkTypeConstraint constraints)
            List.iter walkPat pats
        | SynPat.Tuple(pats, _) -> List.iter walkPat pats
        | SynPat.Paren(pat, _) -> walkPat pat
        | SynPat.ArrayOrList(_, pats, _) -> List.iter walkPat pats
        | SynPat.IsInst(t, _) -> walkType t
        | SynPat.QuoteExpr(e, _) -> walkExpr e
        | _ -> ()

    and walkTypar (Typar (_, _, _)) = ()

    and walkBinding (SynBinding.Binding(_, _, _, _, attrs, _, _, pat, returnInfo, e, _, _)) =
        List.iter walkAttribute attrs
        walkPat pat
        walkExpr e
        returnInfo |> Option.iter (fun (SynBindingReturnInfo (t, _, _)) -> walkType t)

    and walkInterfaceImpl (InterfaceImpl(_, bindings, _)) = List.iter walkBinding bindings

    and walkIndexerArg = function
        | SynIndexerArg.One e -> walkExpr e
        | SynIndexerArg.Two (e1, e2) -> List.iter walkExpr [e1; e2]

    and walkType = function
        | SynType.LongIdent ident -> addLongIdentWithDots ident
        | SynType.App(ty, _, types, _, _, _, _) -> 
            walkType ty
            List.iter walkType types
        | SynType.LongIdentApp(_, _, _, types, _, _, _) -> List.iter walkType types
        | SynType.Tuple(ts, _) -> ts |> List.iter (fun (_, t) -> walkType t)
        | SynType.Array(_, t, _) -> walkType t
        | SynType.Fun(t1, t2, _) -> 
            walkType t1
            walkType t2
        | SynType.WithGlobalConstraints(t, typeConstraints, _) -> 
            walkType t
            List.iter walkTypeConstraint typeConstraints
        | SynType.HashConstraint(t, _) -> walkType t
        | SynType.MeasureDivide(t1, t2, _) -> 
            walkType t1
            walkType t2
        | SynType.MeasurePower(t, _, _) -> walkType t
        | _ -> ()

    and walkClause (Clause(pat, e1, e2, _, _)) =
        walkPat pat 
        walkExpr e2
        e1 |> Option.iter walkExpr

    and walkExpr = function
        | SynExpr.LongIdent (_, ident, _, _) -> addLongIdentWithDots ident
        | SynExpr.Ident ident -> addIdent ident
        | SynExpr.Paren (e, _, _, _) -> walkExpr e
        | SynExpr.Quote(_, _, e, _, _) -> walkExpr e
        | SynExpr.Typed(e, _, _) -> walkExpr e
        | SynExpr.Tuple(es, _, _) -> List.iter walkExpr es
        | SynExpr.ArrayOrList(_, es, _) -> List.iter walkExpr es
        | SynExpr.Record(_, _, fields, _) -> 
            fields |> List.iter (fun ((ident, _), e, _) -> 
                        addLongIdentWithDots ident
                        e |> Option.iter walkExpr)
        | SynExpr.New(_, t, e, _) -> 
            walkExpr e
            walkType t
        | SynExpr.ObjExpr(ty, argOpt, bindings, ifaces, _, _) -> 
            argOpt |> Option.iter (fun (e, ident) -> 
                walkExpr e
                ident |> Option.iter addIdent)
            walkType ty
            List.iter walkBinding bindings
            List.iter walkInterfaceImpl ifaces
        | SynExpr.While(_, e1, e2, _) -> List.iter walkExpr [e1; e2]
        | SynExpr.For(_, ident, e1, _, e2, e3, _) -> 
            addIdent ident
            List.iter walkExpr [e1; e2; e3]
        | SynExpr.ForEach(_, _, _, pat, e1, e2, _) -> 
            walkPat pat
            List.iter walkExpr [e1; e2]
        | SynExpr.ArrayOrListOfSeqExpr(_, e, _) -> walkExpr e
        | SynExpr.CompExpr(_, _, e, _) -> walkExpr e
        | SynExpr.Lambda(_, _, _, e, _) -> walkExpr e
        | SynExpr.MatchLambda(_, _, synMatchClauseList, _, _) -> 
            List.iter walkClause synMatchClauseList
        | SynExpr.Match(_, e, synMatchClauseList, _, _) -> 
            walkExpr e 
            List.iter walkClause synMatchClauseList
        | SynExpr.Do(e, _) -> walkExpr e
        | SynExpr.Assert(e, _) -> walkExpr e
        | SynExpr.App(_, _, e1, e2, _) -> List.iter walkExpr [e1; e2]
        | SynExpr.TypeApp(e, _, tys, _, _, _, _) -> 
            walkExpr e 
            List.iter walkType tys
        | SynExpr.LetOrUse(_, _, bindings, e, _) -> 
            List.iter walkBinding bindings 
            walkExpr e
        | SynExpr.TryWith(e, _, clauses, _, _, _, _) -> 
            List.iter walkClause clauses
            walkExpr e
        | SynExpr.TryFinally(e1, e2, _, _, _) -> List.iter walkExpr [e1; e2]
        | SynExpr.Lazy(e, _) -> walkExpr e
        | Sequentials es -> List.iter walkExpr es
        | SynExpr.IfThenElse(e1, e2, e3, _, _, _, _) -> 
            List.iter walkExpr [e1; e2]
            e3 |> Option.iter walkExpr
        | SynExpr.LongIdentSet(ident, e, _) -> 
            addLongIdentWithDots ident
            walkExpr e
        | SynExpr.DotGet(e, _, idents, _) -> 
            addLongIdentWithDots idents
            walkExpr e
        | SynExpr.DotSet(e1, idents, e2, _) -> 
            walkExpr e1
            addLongIdentWithDots idents
            walkExpr e2
        | SynExpr.DotIndexedGet(e, args, _, _) -> 
            walkExpr e
            List.iter walkIndexerArg args
        | SynExpr.DotIndexedSet(e1, args, e2, _, _, _) -> 
            walkExpr e1
            List.iter walkIndexerArg args
            walkExpr e2
        | SynExpr.NamedIndexedPropertySet(ident, e1, e2, _) -> 
            addLongIdentWithDots ident
            List.iter walkExpr [e1; e2]
        | SynExpr.DotNamedIndexedPropertySet(e1, ident, e2, e3, _) -> 
            addLongIdentWithDots ident
            List.iter walkExpr [e1; e2; e3]
        | SynExpr.TypeTest(e, t, _) -> 
            walkExpr e
            walkType t
        | SynExpr.Upcast(e, t, _) -> 
            walkExpr e
            walkType t
        | SynExpr.Downcast(e, t, _) -> 
            walkExpr e
            walkType t
        | SynExpr.InferredUpcast(e, _) -> walkExpr e
        | SynExpr.InferredDowncast(e, _) -> walkExpr e
        | SynExpr.AddressOf(_, e, _, _) -> walkExpr e
        | SynExpr.JoinIn(e1, _, e2, _) -> List.iter walkExpr [e1; e2]
        | SynExpr.YieldOrReturn(_, e, _) -> walkExpr e
        | SynExpr.YieldOrReturnFrom(_, e, _) -> walkExpr e
        | SynExpr.LetOrUseBang(_, _, _, pat, e1, e2, _) -> 
            walkPat pat
            List.iter walkExpr [e1; e2]
        | SynExpr.DoBang(e, _) -> walkExpr e
        | SynExpr.TraitCall (ts, sign, e, _) ->
            List.iter walkTypar ts 
            walkMemberSig sign
            walkExpr e
        | SynExpr.Const (SynConst.Measure(_, m), _) -> walkMeasure m
        | _ -> ()

    and walkMeasure = function
        | SynMeasure.Product(m1, m2, _)
        | SynMeasure.Divide (m1, m2, _) -> walkMeasure m1; walkMeasure m2
        | SynMeasure.Named(longIdent, _) -> addLongIdent longIdent
        | SynMeasure.Seq(ms, _) -> List.iter walkMeasure ms
        | SynMeasure.Power(m, _, _) -> walkMeasure m
        | SynMeasure.Var(ty, _) -> walkTypar ty
        | SynMeasure.One
        | SynMeasure.Anon _ -> ()

    and walkSimplePat = function
        | SynSimplePat.Attrib (pat, attrs, _) ->
            walkSimplePat pat 
            List.iter walkAttribute attrs
        | SynSimplePat.Typed(pat, t, _) ->
            walkSimplePat pat
            walkType t
        | _ -> ()

    and walkField (SynField.Field(attrs, _, _, t, _, _, _, _)) =
        List.iter walkAttribute attrs 
        walkType t

    and walkValSig (SynValSig.ValSpfn(attrs, _, _, t, SynValInfo(argInfos, argInfo), _, _, _, _, _, _)) =
        List.iter walkAttribute attrs 
        walkType t
        argInfo :: (argInfos |> List.concat) 
        |> List.map (fun (SynArgInfo(attrs, _, _)) -> attrs) 
        |> List.concat 
        |> List.iter walkAttribute

    and walkMemberSig = function
        | SynMemberSig.Inherit (t, _) -> walkType t
        | SynMemberSig.Member(vs, _, _) -> walkValSig vs
        | SynMemberSig.Interface(t, _) -> walkType t
        | SynMemberSig.ValField(f, _) -> walkField f
        | SynMemberSig.NestedType(SynTypeDefnSig.TypeDefnSig (info, repr, memberSigs, _), _) -> 
            let isTypeExtensionOrAlias = 
                match repr with
                | SynTypeDefnSigRepr.ObjectModel(SynTypeDefnKind.TyconAugmentation, _, _)
                | SynTypeDefnSigRepr.ObjectModel(SynTypeDefnKind.TyconAbbrev, _, _)
                | SynTypeDefnSigRepr.Simple(SynTypeDefnSimpleRepr.TypeAbbrev _, _) -> true
                | _ -> false
            walkComponentInfo isTypeExtensionOrAlias info
            walkTypeDefnSigRepr repr
            List.iter walkMemberSig memberSigs

    and walkMember = function
        | SynMemberDefn.AbstractSlot (valSig, _, _) -> walkValSig valSig
        | SynMemberDefn.Member(binding, _) -> walkBinding binding
        | SynMemberDefn.ImplicitCtor(_, attrs, pats, _, _) -> 
            List.iter walkAttribute attrs 
            List.iter walkSimplePat pats
        | SynMemberDefn.ImplicitInherit(t, e, _, _) -> walkType t; walkExpr e
        | SynMemberDefn.LetBindings(bindings, _, _, _) -> List.iter walkBinding bindings
        | SynMemberDefn.Interface(t, members, _) -> 
            walkType t 
            members |> Option.iter (List.iter walkMember)
        | SynMemberDefn.Inherit(t, _, _) -> walkType t
        | SynMemberDefn.ValField(field, _) -> walkField field
        | SynMemberDefn.NestedType(tdef, _, _) -> walkTypeDefn tdef
        | SynMemberDefn.AutoProperty(attrs, _, _, t, _, _, _, _, e, _, _) -> 
            List.iter walkAttribute attrs
            Option.iter walkType t
            walkExpr e
        | _ -> ()

    and walkEnumCase (EnumCase(attrs, _, _, _, _)) = List.iter walkAttribute attrs

    and walkUnionCaseType = function
        | SynUnionCaseType.UnionCaseFields fields -> List.iter walkField fields
        | SynUnionCaseType.UnionCaseFullType(t, _) -> walkType t

    and walkUnionCase (SynUnionCase.UnionCase(attrs, _, t, _, _, _)) = 
        List.iter walkAttribute attrs 
        walkUnionCaseType t

    and walkTypeDefnSimple = function
        | SynTypeDefnSimpleRepr.Enum (cases, _) -> List.iter walkEnumCase cases
        | SynTypeDefnSimpleRepr.Union(_, cases, _) -> List.iter walkUnionCase cases
        | SynTypeDefnSimpleRepr.Record(_, fields, _) -> List.iter walkField fields
        | SynTypeDefnSimpleRepr.TypeAbbrev(_, t, _) -> walkType t
        | _ -> ()

    and walkComponentInfo isTypeExtensionOrAlias (ComponentInfo(attrs, typars, constraints, longIdent, _, _, _, _)) =
        List.iter walkAttribute attrs
        List.iter walkTyparDecl typars
        List.iter walkTypeConstraint constraints
        if isTypeExtensionOrAlias then
            addLongIdent longIdent

    and walkTypeDefnRepr = function
        | SynTypeDefnRepr.ObjectModel (_, defns, _) -> List.iter walkMember defns
        | SynTypeDefnRepr.Simple(defn, _) -> walkTypeDefnSimple defn

    and walkTypeDefnSigRepr = function
        | SynTypeDefnSigRepr.ObjectModel (_, defns, _) -> List.iter walkMemberSig defns
        | SynTypeDefnSigRepr.Simple(defn, _) -> walkTypeDefnSimple defn

    and walkTypeDefn (TypeDefn (info, repr, members, _)) =
        let isTypeExtensionOrAlias = 
            match repr with
            | SynTypeDefnRepr.ObjectModel (SynTypeDefnKind.TyconAugmentation, _, _)
            | SynTypeDefnRepr.ObjectModel (SynTypeDefnKind.TyconAbbrev, _, _)
            | SynTypeDefnRepr.Simple (SynTypeDefnSimpleRepr.TypeAbbrev _, _) -> true
            | _ -> false
        walkComponentInfo isTypeExtensionOrAlias info
        walkTypeDefnRepr repr
        List.iter walkMember members

    and walkSynModuleDecl (decl: SynModuleDecl) =
        match decl with
        | SynModuleDecl.NamespaceFragment fragment -> walkSynModuleOrNamespace fragment
        | SynModuleDecl.NestedModule(info, modules, _, _) ->
            walkComponentInfo false info
            List.iter walkSynModuleDecl modules
        | SynModuleDecl.Let (_, bindings, _) -> List.iter walkBinding bindings
        | SynModuleDecl.DoExpr (_, expr, _) -> walkExpr expr
        | SynModuleDecl.Types (types, _) -> List.iter walkTypeDefn types
        | SynModuleDecl.Attributes (attrs, _) -> List.iter walkAttribute attrs
        | _ -> ()

    match input with 
    | Some (ParsedInput.ImplFile input) -> 
         walkImplFileInput input
    | _ -> ()
    identsByEndPos :> _