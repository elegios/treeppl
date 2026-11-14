/-
TreePPL Compiler and Unit Tests

Unit tests available via:

  mi compile models/treeppl-to-coreppl/compile.mc --test

-/

include "../treeppl-ast.mc"
include "../src-location.mc"
include "mexpr/ast.mc"
include "mexpr/ast-builder.mc"
include "mexpr/boot-parser.mc"
include "mexpr/type-check.mc"
include "mexpr/generate-json-serializers.mc"
include "mexpr/utils.mc"
include "mexpr/constant-fold.mc"
include "mexpr/duplicate-code-elimination.mc"
include "mexpr/deadcode.mc"
include "mexpr/generate-utest.mc"
include "mexpr/uncurried.mc"
include "mexpr/ssa-block.mc"
include "ocaml/mcore.mc"
include "ocaml/compile.mc"
include "ocaml/external-includes.mc"
include "mi-stats::stats.ext-ocaml.mc"

include "sys.mc"

include "coreppl::coreppl-to-mexpr/compile.mc"
include "coreppl::coreppl.mc"
include "coreppl::inference/mcmc.mc"
include "coreppl::parser.mc"

include "coreppl::coreppl-to-mexpr/is-lw/compile.mc"
include "coreppl::coreppl-to-mexpr/smc-bpf/compile.mc"
include "coreppl::coreppl-to-mexpr/smc-apf/compile.mc"
include "coreppl::coreppl-to-mexpr/mcmc-naive/compile.mc"
include "coreppl::coreppl-to-mexpr/mcmc-trace/compile.mc"
include "coreppl::coreppl-to-mexpr/mcmc-lightweight/compile.mc"
include "coreppl::coreppl-to-mexpr/pval-graph/compile.mc"
include "coreppl::coreppl-to-mexpr/pmcmc-pimh/compile.mc"

include "matrix.mc"

include "ast-additions.mc"


lang TreePPLCompile
  = TreePPLAst + MExprPPL + MExprFindSym + RecLetsDeclAst + Externals + MExprSym
  + FloatAst + Resample + GenerateJsonSerializers + MExprEliminateDuplicateCode
  + SSABlockLang
  + MCoreLoader + JsonSerializationLoader + IncludeLoader
  + ProjMatchAst + TreePPLOperators
  + TyVarOrConAst
  + UncurriedAst

  type MkInferMethod = Type -> Loader -> (Loader, {mkMethod : Name -> InferMethod, optParser : Expr})

  -- a type with useful information passed down from compile
  type TpplCompileContext = {
    serializeResult: Name,
    runInference: Name,
    logName: Name, expName: Name,
    printJsonLn: Name,
    some: Name,
    none: Name,
    matrixMul: Name,
    matrixAdd: Name,
    matrixMulFloat: Name,
    pow: Name,
    functionDepth: Int
  }

  type TpplNameScope = Map Name {name : Name, depth : Int, info : Info, ty : Either (Name, Info) Type}

  sem isemi_: Expr -> Expr -> Expr
  sem isemi_ l =
  | r ->
    let infoL = infoTm l in
    let infoR = infoTm r in
    let mergedInfo = mergeInfo infoL infoR in
    withInfo mergedInfo (semi_ l r)

  sem compileTpplTypeDecl : DeclTppl -> [Decl]
  sem compileTpplTypeDecl =
  | TypeDeclTppl (x & {constructor = Some c, alias = None _}) ->
    [ DeclType
      { ident = c.name.v
      , params = map (lam x. x.v) c.params
      , tyIdent = tyvariant_ []
      , info = x.info
      }
    ]
  | TypeDeclTppl (x & {alias = Some a, constructor = None _}) ->
    [ DeclType
      { ident = a.name.v
      , params = map (lam x. x.v) a.params
      , tyIdent = compileTypeTppl a.ty
      , info = x.info
      }
    ]
  | _ -> []

  sem compileTpplConDecl : DeclTppl -> [Decl]
  sem compileTpplConDecl =
  | TypeDeclTppl (x & {constructor = Some c}) ->
    let params = map (lam x. x.v) c.params in
    let f = lam constr.
      match constr with TypeCon constr in DeclConDef
      { ident = constr.name.v
      , tyIdent =
        let f = lam field. (field.name.v, compileTypeTppl field.ty) in
        let lhs = tyrecord_ (map f constr.fields) in
        let rhs = tyapps_ (ntycon_ c.name.v) (map ntyvar_ params) in
        foldr ntyall_ (tyarrow_ lhs rhs) params
      , info = constr.name.i
      } in
    map f c.cons
  | _ -> []

  sem tpplBindingHelper : TpplCompileContext -> TpplNameScope -> {i : Info, v : Name} -> Either Info Type -> (TpplNameScope, Name, Expr -> Expr)
  sem tpplBindingHelper context scope binder = | ty ->
    let n = binder.v in
    let entryTy = lam ty. switch ty
      case Left (tn, info) then tyWithInfo info (ntycon_ tn)
      case Right ty then ty
      end in
    let prev = mapLookup n scope in
    let sameFunction = optionMapOr false (lam e. eqi e.depth context.functionDepth) prev in
    match (sameFunction, prev) with (true, Some entry) then
      let prevTy = entryTy entry.ty in
      let wrap = switch ty
        case Left info then lam tm. _tyAnnot info tm prevTy
        case Right newTy then
          let info = infoTy newTy in
          lam tm. _tyAnnot info (_tyAnnot info tm newTy) prevTy
        end in
      (scope, entry.name, wrap)
    else
      let entry =
        { name = optionMapOr n (lam x. x.name) prev
        , depth = context.functionDepth
        , info = binder.i
        , ty = eitherEither (lam info. Left (nameSym (concat "TypeOf_" (nameGetStr n)), info)) (lam ty. Right ty) ty
        } in
      let ty = entryTy entry.ty in
      let wrap = lam tm. _tyAnnot (infoTy ty) tm ty in
      (mapInsert n entry scope, entry.name, wrap)

  sem tpplFunctionHelper
    : TpplCompileContext
    -> TpplNameScope
    -> Info
    -> [{name : {i : Info, v : Name}, ty : TypeTppl}]
    -> Option TypeTppl
    -> [StmtTppl]
    -> (Expr, Type)
  sem tpplFunctionHelper context scope info params retTy = | body ->
    let outerScope = scope in
    let context = {context with functionDepth = addi context.functionDepth 1} in
    match
      let g = lam scope. lam x.
        let n = nameSetNewSym x.name.v in
        let ty = compileTypeTppl x.ty in
        let binding =
          { name = n
          , depth = context.functionDepth
          , info = x.name.i
          , ty = Right ty
          } in
        let param =
          { ident = n
          , tyAnnot = ty
          , tyParam = tyunknown_
          , info = x.name.i
          } in
        (mapInsert x.name.v binding scope, param) in
      mapAccumL g scope params
    with (scope, positional) in
    let ret = optionMapOr tyunit_ compileTypeTppl retTy in
    match mapAccumL (compileStmtTppl context) scope body with (scope, body) in
    let body = ssaFinalize
      { ssaFinalizeOptsUntyped () with
        joinParam = lam args.
          let n = args.name in
          if any (lam x. match x with SSAOuter _ then true else false) args.sources then
            let v = join ["`", nameGetStr n, "`"] in
            let outer = mapChoose (mapFilter (lam x. nameEq x.name n) outerScope) in
            let extra = match outer with Some (_, x)
              then [(x.info, join [v, " is bound outside this function.\nIf you want to conditionally shadow it, add `val ", nameGetStr n, " = ", nameGetStr n, "` to the beginning of this function."])]
              else [] in
            let extra = cons (args.info, join ["This section might leave ", v, " unbound:"]) extra in
            errorExtra args.readInfo
              (join ["This use of ", v, " might not be bound:"])
              extra
          else ()
      }
      (ssaSeq (cons
        (ssaSetPar (mapFromSeq nameCmp (map (lam p. (p.ident, nvar_ p.ident)) positional)))
        body))
      unit_ in
    let body = mapFoldWithKey
      (lam body. lam. lam x.
        if eqi x.depth context.functionDepth then
          match x.ty with Left (n, info)
          then bind_ (ntype_ n [] (TyShared {info = info})) body
          else body
        else body)
      body
      scope in
    let function = TmUncurriedLam
      { positional = positional
      , body = body
      , info = info
      , ty = tyunknown_
      } in
    let fullTy = TyUncurriedArrow
      { positional = map (lam x. x.tyAnnot) positional
      , ret = ret
      , info = info
      } in
    (function, fullTy)

  sem compileTpplFunction: TpplCompileContext -> DeclTppl -> [DeclLetRecord]
  sem compileTpplFunction (context: TpplCompileContext) =
  | FunDeclTppl f ->
    match tpplFunctionHelper context (mapEmpty nameCmp) f.info f.args f.returnTy f.body
      with (function, fullTy) in
    let fullTy = foldr (lam p. lam ty. ntyall_ p.v ty) fullTy f.tyParams in
    [ { ident = f.name.v
      , tyBody = tyunknown_
      , tyAnnot = fullTy
      , body = function
      , info = f.info
      }
    ]
  | TypeDeclTppl _ -> []

  sem compileTypeTppl: TypeTppl -> Type

  sem compileTypeTppl =
  | NamedTypeTppl x -> TyVarOrCon {
      ident = x.name.v,
      info = x.name.i
    }

  | FunTypeTppl x -> TyUncurriedArrow
    { positional = map compileTypeTppl x.params
    , ret = compileTypeTppl x.ret
    , info = x.info
    }

  | AtomicRealTypeTppl x -> TyFloat {
      info = x.info
    }

  | AtomicBoolTypeTppl x -> TyBool {
      info = x.info
    }

  | AtomicIntTypeTppl x -> TyInt {
      info = x.info
    }

  | AtomicDistTypeTppl x ->
    errorSingle [x.info] "The Dist type needs exactly one type argument."
  | TypeAppOrSequenceTypeTppl (x & {ty = AtomicDistTypeTppl _, args = [arg]}) -> TyDist {
      info = x.info,
      ty = compileTypeTppl arg
    }

  | TypeAppOrSequenceTypeTppl (x & {args = []}) -> TySeq {
    info = x.info,
    ty = compileTypeTppl x.ty
  }
  | TypeAppOrSequenceTypeTppl x ->
    let tyapp_ = lam lhs. lam rhs.
      tyWithInfo x.info (tyapp_ lhs (compileTypeTppl rhs)) in
    foldl tyapp_ (compileTypeTppl x.ty) x.args

  | TpplStrTypeTppl x -> TySeq {
    info = x.info,
    ty = TyChar {
      info = x.info
    }
  }

  | NothingTypeTppl x -> tyunit_

  sem compileModelInvocation : TpplCompileContext -> TpplFrontendOptions -> MkInferMethod -> Loader -> SymEnv -> DeclTppl -> Option (Loader, SymEnv, Expr)
  sem compileModelInvocation context frontend mkInferenceMethod loader fileEnv =
  | FunDeclTppl (x & {model = Some modelInfo}) ->
    -- TODO(vipa, 2024-12-13): We could technically shadow a model
    -- function, in which case the generated code will refer to the
    -- wrong function, which is bad.
    let params : [(Name, Type)] =
      map (lam param. (param.name.v, compileTypeTppl param.ty)) x.args in

    let tcEnv = _getTCEnv loader in
    let inputType = tyrecord_ (map (lam x. (nameGetStr x.0, x.1)) params) in
    let inputType = resolveType modelInfo tcEnv false (symbolizeType fileEnv inputType) in
    let outputType = match x. returnTy with Some ty
      then compileTypeTppl ty
      else errorSingle [modelInfo] "A model function must have an explicit return type, even if it returns nothing, i.e., ()" in
    let outputType = resolveType modelInfo tcEnv false (symbolizeType fileEnv outputType) in
    match serializationPairsFor [inputType, outputType] loader with (loader, [inputSer, outputSer]) in

    let app_ = lam f. lam a. withInfo modelInfo (app_ f a) in

    let jsonInputName = nameSym "input" in
    let inferOptsName = nameSym "inferOpts" in

    let parsedName = nameSym "input" in
    let parsedDecl = DeclLet
      { ident = parsedName
      , body =
        let m = nameSym "m" in
        match_
          (app_ inputSer.deserializer (nvar_ jsonInputName))
          (npcon_ context.some (npvar_ m))
          (nvar_ m)
          (error_ (str_ "Could not deserialize data input, malformed json"))
      , tyAnnot = tyunknown_
      , tyBody = tyunknown_
      , info = modelInfo
      } in

    match mkInferenceMethod outputType loader with (loader, inferenceMethod) in

    let invocation =
      let f = withInfo modelInfo (nvar_ x.name.v) in
      let positional = map (lam p. recordproj_ (nameGetStr p.0) (nvar_ parsedName)) params in
      TmUncurriedApp
        { f = f
        , positional = positional
        , info = NoInfo ()
        , ty = tyunknown_
        } in
    let runOnce = nulam_ jsonInputName
      (bind_ parsedDecl
        (nulam_ inferOptsName
          (infer_ (inferenceMethod.mkMethod inferOptsName) (ulam_ "" invocation)))) in

    let inferConfig = urecord_
      [ ("sweeps", int_ frontend.sweeps)
      , ("seed", optionMapOr (nconapp_ context.none unit_) (lam i. nconapp_ context.some (int_ i)) frontend.seed)
      , ("inferTimeMs", bool_ frontend.inferTimeMs)
      , ("inferOpts", inferenceMethod.optParser)
      , ("sampleSerializer", outputSer.serializer)
      , ("runOnce", runOnce)
      ] in
    let inferCode = app_ (nvar_ context.runInference) inferConfig in

    Some (loader, fileEnv, inferCode)
  | _ -> None ()

  sem _tyAnnot : Info -> Expr -> Type -> Expr
  sem _tyAnnot info tm = | ty ->
    let n = nameSym "x" in
    TmDecl
    { decl = DeclLet {ident = n, tyAnnot = ty, tyBody = ty, body = tm, info = info}
    , inexpr = TmVar {ident = n, ty = ty, info = info, frozen = false}
    , ty = ty
    , info = info
    }

  sem compileStmtTppl: TpplCompileContext -> TpplNameScope -> StmtTppl -> (TpplNameScope, SSABlock)
  sem compileStmtTppl (context: TpplCompileContext) scope =

  | ExprStmtTppl x ->
    (scope, ssaRun (compileExprTppl context scope x.e))

  | AssumeStmtTppl a ->
    let dist = compileExprTppl context scope a.dist in
    let tyAnnot = optionMapOr tyunknown_ compileTypeTppl a.ty in
    let bindTy = match a.ty with Some _ then Right tyAnnot else Left a.randomVar.i in
    match tpplBindingHelper context scope a.randomVar bindTy with (scope, name, wrap) in
    let driftKernel =
      match a.driftKernel with Some dk then
        let dk = compileExprTppl context scope dk in
        Some (withInfo (infoTm dk) (nulam_ name dk))
      else None () in
    let body = TmAssume
      { dist = dist
      , ty = tyAnnot
      , info = a.randomVar.i
      , driftKernel = driftKernel
      } in
    (scope, ssaSetI a.info name (wrap body))

  | ObserveStmtTppl x ->
    let obs = TmObserve {
      info = x.info,
      value = compileExprTppl context scope x.value,
      dist = compileExprTppl context scope x.dist,
      ty = tyunknown_
    } in
    (scope, ssaRun obs)

  | ResampleStmtTppl x ->
    (scope, ssaRun (TmResample { info = x.info, ty = tyunknown_ }))

  | AssignStmtTppl a ->
    let body = compileExprTppl context scope a.val in
    let bindTy = match a.ty with Some ty
      then Right (compileTypeTppl ty)
      else Left (get_ExprTppl_info a.val) in
    match tpplBindingHelper context scope a.var bindTy with (scope, name, wrap) in
    (scope, ssaSetI a.info name (wrap body))

  | WeightStmtTppl a ->
    let cExpr: Expr = compileExprTppl context scope a.value in
    let logExpr: Expr = withInfo a.info (app_ (withInfo a.info (nvar_ context.logName)) cExpr) in
    let body = TmWeight
      { weight = logExpr
      , ty = tyunknown_
      , info = a.info
      } in
    (scope, ssaRun body)

  | LogWeightStmtTppl a ->
    let body = TmWeight
      { weight = compileExprTppl context scope a.value
      , ty = tyunknown_
      , info = a.info
      } in
    (scope, ssaRun body)

  | IfStmtTppl x ->
    let condition = compileExprTppl context scope x.condition in
    match mapAccumL (compileStmtTppl context) scope x.ifTrueStmts with (scope, ifTrue) in
    match mapAccumL (compileStmtTppl context) scope x.ifFalseStmts with (scope, ifFalse) in
    (scope, ssaMatchI x.info condition (withInfoPat (infoTm condition) ptrue_) (ssaSeq ifTrue) (ssaSeq ifFalse))

  | ForLoopStmtTppl x ->
    let range = compileExprTppl context scope x.range in
    let rangeN = nameSym "seq" in
    let elemN = nameSym "elem" in
    match tpplBindingHelper context scope x.iterator (Left x.iterator.i) with (scope, name, wrap) in
    match mapAccumL (compileStmtTppl context) scope x.forStmts with (scope, forStmts) in
    let body = ssaChain
      (ssaSetI x.iterator.i name (wrap (withInfo x.iterator.i (nvar_ elemN))))
      (ssaSeq forStmts) in
    ( scope
    , ssaChain
      (ssaSet rangeN range)
      (ssaBlock (lam break. ssaLoopI x.info
        (ssaMatch (nvar_ rangeN) (pseqedgen_ [npvar_ elemN] rangeN [])
          body
          break)))
    )

  | ReturnStmtTppl r ->
    (scope, ssaReturn (optionMapOr (withInfo r.info unit_) (compileExprTppl context scope) r.return))

  | PrintStmtTppl x ->
    let processTerm : Bool -> ExprTppl -> (Bool, Expr) = lam maybeInsertSpace. lam expr.
      match expr with TpplStringExprTppl x then (false, printError_ (str_ x.val.v)) else
      let p = dprint_ (compileExprTppl context scope expr) in
      (true, if maybeInsertSpace then isemi_ (printError_ (str_ " ")) p else p) in
    let final = isemi_ (printError_ (str_ "\n")) (flushStderr_ unit_) in
    let print = foldr isemi_ final (mapAccumL processTerm false x.printable).1 in
    (scope, ssaRun print)

  sem compileExprTppl: TpplCompileContext -> TpplNameScope -> ExprTppl -> Expr
  sem compileExprTppl (context: TpplCompileContext) scope =

  | AnonFunExprTppl x ->
    match tpplFunctionHelper context scope x.info x.args x.retTy x.stmts
      with (function, fullTy) in
    _tyAnnot x.info function fullTy

  | ProjectionExprTppl x ->
    TmProjMatch {
      info = x.info,
      target = compileExprTppl context scope x.target,
      field = stringToSid x.field.v,
      ty = tyunknown_
    }

  | PartialApplicationExprTppl x ->
    errorSingle [x.info] "'_' is only allowed in a (partial) function application."
  | FunCallExprTppl x ->
    let compileArg = lam e.
      match e with PartialApplicationExprTppl a
      then Left (nameSym "x", a.info)
      else Right (compileExprTppl context scope e) in
    let args = map compileArg x.args in
    match eitherLefts args with params & ![]
    then TmUncurriedLam
      { positional = map
        (lam p. {ident = p.0, tyAnnot = tyunknown_, tyParam = tyunknown_, info = p.1})
        params
      , body = TmUncurriedApp
        { f = compileExprTppl context scope x.f
        , positional = map (eitherEither (lam p. withInfo p.1 (nvar_ p.0)) (lam x. x)) args
        , info = x.info
        , ty = tyunknown_
        }
      , info = x.info
      , ty = tyunknown_
      }
    else TmUncurriedApp
      { f = compileExprTppl context scope x.f
      , positional = eitherRights args
      , info = x.info
      , ty = tyunknown_
      }

  | BernoulliExprTppl d ->
    TmDist {
      dist = DBernoulli {
        p = compileExprTppl context scope d.prob
      },
      ty = tyunknown_,
      info = d.info
    }

  | BetaExprTppl d ->
    TmDist {
      dist = DBeta {
        a = compileExprTppl context scope d.a,
        b = compileExprTppl context scope d.b
      },
      ty = tyunknown_,
      info = d.info
    }

  | BinomialExprTppl d ->
    TmDist {
      dist = DBinomial {
        n = compileExprTppl context scope d.n,
        p = compileExprTppl context scope d.prob
      },
      ty = tyunknown_,
      info = d.info
  }

  | CategoricalExprTppl d ->
    TmDist {
      dist = DCategorical {
        p = compileExprTppl context scope d.probs
      },
      ty = tyunknown_,
      info = d.info
  }

  | Chi2ExprTppl d ->
    TmDist {
      dist = DChi2 {
        df = compileExprTppl context scope d.df
      },
      ty = tyunknown_,
      info = d.info
  }

  | DirichletExprTppl d ->
    TmDist {
      dist = DDirichlet {
        a = compileExprTppl context scope d.alphas
      },
      ty = tyunknown_,
      info = d.info
  }

  | EmpiricalExprTppl d ->
    TmDist {
      dist = DEmpirical {
        samples = compileExprTppl context scope d.samples
      },
      ty = tyunknown_,
      info = d.info
  }

  | ExponentialExprTppl d ->
    TmDist {
      dist = DExponential {
        rate = compileExprTppl context scope d.rate
      },
      ty = tyunknown_,
      info = d.info
    }

  | GammaExprTppl d ->
    TmDist {
      dist = DGamma {
        k = compileExprTppl context scope d.shape,
        theta = compileExprTppl context scope d.scale
      },
      ty = tyunknown_,
      info = d.info
    }

  | NormalExprTppl d ->
    TmDist {
      dist = DNormal {
        mu = compileExprTppl context scope d.mean,
        sigma = compileExprTppl context scope d.dev
      },
      ty = tyunknown_,
      info = d.info
    }

  | GeometricExprTppl d ->
    TmDist {
      dist = DGeometric {
        p = compileExprTppl context scope d.prob
      },
      ty = tyunknown_,
      info = d.info
  }

  | MultinomialExprTppl d ->
    TmDist {
      dist = DMultinomial {
        n = compileExprTppl context scope d.n,
        p = compileExprTppl context scope d.probs
      },
      ty = tyunknown_,
      info = d.info
  }

  | PoissonExprTppl d ->
    TmDist {
      dist = DPoisson {
        lambda = compileExprTppl context scope d.rate
      },
      ty = tyunknown_,
      info = d.info
    }

  | UniformExprTppl d ->
    TmDist {
      dist = DUniform {
        a = compileExprTppl context scope d.a,
        b = compileExprTppl context scope d.b
      },
      ty = tyunknown_,
      info = d.info
  }

  | UniformDiscreteExprTppl d ->
    TmDist {
      dist = DUniformDiscrete {
        a = compileExprTppl context scope d.a,
        b = compileExprTppl context scope d.b
      },
      ty = tyunknown_,
      info = d.info
  }

| ReciprocalExprTppl d ->
    TmDist {
      dist = DReciprocal {
        a = compileExprTppl context scope d.a,
        b = compileExprTppl context scope d.b
      },
      ty = tyunknown_,
      info = d.info
  }

  | VariableExprTppl v ->
    TmVar {
      ident = optionMapOr v.ident.v (lam x. x.name) (mapLookup v.ident.v scope),
      ty = tyunknown_,
      info = v.info,
      frozen = false
    }

  | IsExprTppl x ->
    TmMatch {
      info = x.info,
      target = compileExprTppl context scope x.thing, -- and constructor
      pat = PatCon {
        info = x.constructor.i,
        ty = tyunknown_,
        ident = x.constructor.v,
        subpat = withInfoPat x.info pvarw_
      },
      thn = withInfo x.info true_,
      els = withInfo x.info false_,
      ty = tyunknown_
    }

  | ToExprTppl x ->
    let let_ = lam n. lam body. lam inexpr. TmDecl
      { decl = DeclLet
        { ident = n
        , tyAnnot = tyunknown_
        , tyBody = tyunknown_
        , body = body
        , info = x.info
        }
      , info = x.info
      , inexpr = inexpr
      , ty = tyunknown_
      } in
    let var_ = lam n. TmVar {ident = n, ty = tyunknown_, info = x.info, frozen = false} in
    let app_ = lam l. lam r. TmApp { lhs = l, rhs = r, info = x.info, ty = tyunknown_ } in
    let const_ = lam c. TmConst { info = x.info, val = c, ty = tyunknown_ } in
    let int_ = lam i. const_ (CInt { val = i }) in
    let lam_ = lam n. lam body. TmLam {ident = n, tyAnnot = tyunknown_, tyParam = tyunknown_, body = body, ty = tyunknown_, info = x.info} in
    let addi_ = lam l. lam r. app_ (app_ (const_ (CAddi ())) l) r in
    let subi_ = lam l. lam r. app_ (app_ (const_ (CSubi ())) l) r in
    let s = nameSym "start" in
    let e = nameSym "end" in
    let idx = nameSym "idx" in
    let_ s (compileExprTppl context scope x.beginVal)
      (let_ e (compileExprTppl context scope x.endVal)
        (app_ (app_ (const_ (CCreate {})) (addi_ (subi_ (var_ e) (var_ s)) (int_ 1)))
          (lam_ idx (addi_ (var_ idx) (var_ s)))))

  | ConstructorExprTppl x ->
    let mkField : {key : {v:String, i:Info}, value : Option ExprTppl} -> (SID, Expr) = lam field.
      let sid = stringToSid field.key.v in
      let ce = lam x.
        compileExprTppl context scope x
      in
      let n = nameNoSym field.key.v in
      let n = optionMapOr n (lam x. x.name) (mapLookup n scope) in
      let val = optionMapOr (withInfo field.key.i (nvar_ n)) ce field.value in
      (sid, val) in
    let fields = mapFromSeq cmpSID (map mkField x.fields) in
    let record = TmRecord { bindings = fields, ty = tyunknown_, info = x.info } in
    TmConApp { ident = x.name.v, body = record, ty = tyunknown_, info = x.info }

  | AddExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpAdd ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | SubExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpSub ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | NegExprTppl x ->
    TmApp {
      info = x.info,
      lhs = mkOp x.info (OpNeg ()),
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | MulExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpMul ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | MatrixMulExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = nvar_ context.matrixMul,
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | MatrixAddExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = nvar_ context.matrixAdd,
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | PowerExprTppl x ->
   TmApp {
        info = x.info,
        lhs = TmApp {
          info = x.info,
          lhs = mkOp x.info (OpPow ()),
          rhs = compileExprTppl context scope x.left,
          ty = tyunknown_
        },
        rhs = compileExprTppl context scope x.right,
        ty = tyunknown_
      }

  | MatrixLeftScalarMulExprTppl x ->
    TmApp {
        info = x.info,
        lhs = TmApp {
          info = x.info,
          lhs = nvar_ context.matrixMulFloat,
          rhs = compileExprTppl context scope x.left,
          ty = tyunknown_
        },
        rhs = compileExprTppl context scope x.right,
        ty = tyunknown_
      }

  | MatrixRightScalarMulExprTppl x ->
    TmApp {
        info = x.info,
        lhs = TmApp {
          info = x.info,
          lhs = nvar_ context.matrixMulFloat,
          rhs = compileExprTppl context scope x.right, -- the scalar is on the right
          ty = tyunknown_
        },
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      }

  | DivExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpDiv ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | ConvIntToRealExprTppl x ->
    withInfo x.info (int2float_ (compileExprTppl context scope x.val))

  | LessEqExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpLeq ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | LessExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpLt ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | GreaterExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpGt ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }


  | GreaterEqExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpGeq ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | EqualExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpEq ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | UnequalExprTppl x ->
    TmApp {
      info = x.info,
      lhs = TmApp {
        info = x.info,
        lhs = mkOp x.info (OpNeq ()),
        rhs = compileExprTppl context scope x.left,
        ty = tyunknown_
      },
      rhs = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | AndExprTppl x ->
    TmMatch {
      info = x.info,
      target = compileExprTppl context scope x.left,
      pat = PatBool { val = true, info = get_ExprTppl_info x.left, ty = tyunknown_ },
      thn = compileExprTppl context scope x.right,
      els = TmConst { info = x.info, ty = tyunknown_, val = CBool { val = false } },
      ty = tyunknown_
    }

  | OrExprTppl x ->
    TmMatch {
      info = x.info,
      target = compileExprTppl context scope x.left,
      pat = PatBool { val = true, info = get_ExprTppl_info x.left, ty = tyunknown_ },
      thn = TmConst { info = x.info, ty = tyunknown_, val = CBool { val = true } },
      els = compileExprTppl context scope x.right,
      ty = tyunknown_
    }

  | NotExprTppl x ->
    TmMatch {
      info = x.info,
      target = compileExprTppl context scope x.right,
      pat = PatBool { val = true, info = get_ExprTppl_info x.right, ty = tyunknown_ },
      thn = TmConst { info = x.info, ty = tyunknown_, val = CBool { val = false } },
      els = TmConst { info = x.info, ty = tyunknown_, val = CBool { val = true } },
      ty = tyunknown_
    }

  -- NOTE(vipa, 2023-05-05): Currently using 1-based indexing
  | SubscriptExprTppl x ->
    let app_ = lam l. lam r. TmApp { lhs = l, rhs = r, info = x.info, ty = tyunknown_ } in
    let const_ = lam c. TmConst { info = x.info, val = c, ty = tyunknown_ } in
    let int_ = lam i. const_ (CInt { val = i }) in
    let addi_ = lam l. lam r. app_ (app_ (const_ (CAddi ())) l) r in
    let var_ = lam n. TmVar {ident = n, ty = tyunknown_, info = x.info, frozen = false} in
    let subseq_ = lam seq. lam idx. lam len. app_ (app_ (app_ (const_ (CSubsequence ())) seq) idx) len in
    let let_ = lam n. lam body. lam inexpr. TmDecl
      { decl = DeclLet
        { ident = n
        , tyAnnot = tyunknown_
        , tyBody = tyunknown_
        , body = body
        , info = x.info
        }
      , inexpr = inexpr
      , ty = tyunknown_
      , info = x.info
      } in
    let idx = compileExprTppl context scope x.idx in
    match x.lastIdx with Some lastIdx then
      let n = nameSym "start" in
      let start = subi_ (var_ n) (int_ 1) in
      let len = addi_ (subi_ (compileExprTppl context scope lastIdx) (var_ n)) (int_ 1) in
      let_ n idx (subseq_ (compileExprTppl context scope x.left) start len)
    else
      app_ (app_ (const_ (CGet ())) (compileExprTppl context scope x.left)) (subi_ idx (int_ 1))

  | SequenceExprTppl x ->
    let ce = lam x.
      compileExprTppl context scope x
    in
    TmSeq {
      tms = map ce x.values,
      ty = tyunknown_,
      info = x.info
    }

  | RealExprTppl r ->
    TmConst {
      val = CFloat { val = r.val.v },
      ty = tyunknown_,
      info = r.info
    }

  | IntegerExprTppl r ->
    TmConst {
      val = CInt { val = r.val.v },
      ty = tyunknown_,
      info = r.info
    }

  | TrueExprTppl r ->
    TmConst {
      val = CBool { val = true },
      ty = tyunknown_,
      info = r.info
    }

  | FalseExprTppl r ->
    TmConst {
      val = CBool { val = false },
      ty = tyunknown_,
      info = r.info
    }

  | TpplStringExprTppl r ->
    TmSeq {
      tms = map char_ r.val.v,
      ty = tyunknown_,
      info = r.info
    }
end

type TpplFrontendOptions =
  { input : String
  , output : String
  , outputMl : Option String
  , inferTimeMs : Bool
  , seed : Option Int
  , sweeps : Int
  }

lang TreePPLThings = TreePPLAst + TreePPLCompile
  + ProjMatchTypeCheck + ProjMatchPprint + MExprAst
  + TyVarOrConSym
  + MExprGenerateEq
  + OverloadedOpTypeCheck
  + OverloadedOpPrettyPrint
  + TransformDist + CPPLLoader + CorePPLFileTypeLoader
  + ProjMatchToJson + TyVarOrConToJson
  + JsonSerializationLoader
  + DPrintViaPprintLoader + MExprGeneratePprint + GeneratePprintMissingCase
  + TreePPLOperators
  + StripUtestLoader + PprintUnifyErrorNumArguments + UncurriedTypeCheck + SymUncurried + UncurriedPrettyPrint + LowerUncurryLoader
  + UnifyUncurriedMixed + UncurriedToJson
  + MExprLowerNestedPatterns + MExprDeadcodeElimination + MExprConstantFold + MCoreCompileLang
  + MLangTypeAlias + MLangSyn + MLangSem + TyUseSym + DeclUseSym
  + MExprPatAnalysis + MCoreKeywordMaker
  + PhaseStats
  + BPFCompilerPicker + APFCompilerPicker + ImportanceCompilerPicker
  + NaiveMCMCCompilerPicker + TraceMCMCCompilerPicker + PIMHCompilerPicker
  + LightweightMCMCCompilerPicker + SimplePValGraphCompiler
  + UnboundErrorAttr + DefinedAttr + WithoutInfoAttr

  syn FileType =
  | FTreePPL ()

  syn Hook =
  | TreePPLHook
    { frontend : TpplFrontendOptions
    , mkInferenceMethod : MkInferMethod
    }

  sem _fileType = | _ ++ ".tppl" -> FTreePPL ()
  sem _loadFile path = | (FTreePPL _, loader) ->
    match getHookOpt (lam x. match x with TreePPLHook x then Some x else None ()) loader with Some hook in
    -- For things referencing the entirety of the file, and no
    -- particular part of it
    let fileInfo = infoVal path 0 0 0 0 in

    let content = readFile path in
    match parseTreePPLExn path content with DeclSequenceFileTppl top in

    -- Standard library (these should be in scope in the program)
    let autoImportDir = stdlibResolveFileOr (lam. never) "." "treeppl::auto-import" in
    let autoImportPaths =
      -- NOTE(vipa, 2026-05-20): Do not autoimport anything if we're
      -- currently compiling a file in the auto-import dir
      if strStartsWith autoImportDir path then [] else
      let x = sysRunCommand ["find", autoImportDir, "-type", "f", "-a", "-name", "'*.tppl'"] "" "." in
      let x = strSplit "\n" x.stdout in
      filter (lam s. not (null s)) x in
    -- Compiler libraries (these should *not* be in scope in the program)
    match includeFileExn "." "stdlib::ext/dist-ext.mc" loader with (distEnv, loader) in
    match includeFileExn "." "stdlib::ext/math-ext.mc" loader with (mathEnv, loader) in
    match includeFileExn "." "stdlib::ext/mat-ext.mc" loader with (matrixEnv, loader) in
    match includeFileExn "." "stdlib::json.mc" loader with (jsonEnv, loader) in
    match includeFileExn "." "stdlib::basic-types.mc" loader with (optionEnv, loader) in
    match includeFileExn "." "stdlib::common.mc" loader with (commonEnv, loader) in
    match includeFileExn "." "treeppl::internal/lib-compile.dppl" loader with (compileLibEnv, loader) in
    -- Explicit imports (these should be in scope in the program)
    let import = lam acc. lam imp.
      match includeFileExn (dirname path) imp acc.1 with (newEnv, loader) in
      (mergeSymEnv acc.0 newEnv.env, loader) in
    match foldl import (_symEnvEmpty, loader) (concat autoImportPaths (map (lam x. x.v) top.imports)) with (fileEnv, loader) in

    let context =
      { serializeResult = _getVarExn "serializeResult" compileLibEnv
      , runInference = _getVarExn "runInference" compileLibEnv
      , logName = _getVarExn "externalLog" mathEnv
      , expName = _getVarExn "externalExp" mathEnv
      , pow = _getVarExn "pow" mathEnv
      , printJsonLn = _getVarExn "printJsonLn" jsonEnv
      , some = _getConExn "Some" optionEnv
      , none = _getConExn "None" optionEnv
      , matrixMul = _getVarExn "matMulExn" matrixEnv
      , matrixAdd = _getVarExn "matAddExn" matrixEnv
      , matrixMulFloat = _getVarExn "matScale" matrixEnv
      , functionDepth = 0
      } in

    -- 1. Type and constructor definitions. *All* types are inserted
    -- before *all* constructors, which lets constructors refer to
    -- other types in mutually recursive ways.
    let work = lam f. lam acc. lam decl.
      foldl (lam acc. _addDeclExn acc.0 acc.1) acc (f decl) in
    match foldl (work compileTpplTypeDecl) (fileEnv, loader) top.decls with (fileEnv, loader) in
    match foldl (work compileTpplConDecl) (fileEnv, loader) top.decls with (fileEnv, loader) in

    -- 2. Functions. These are inserted into a single recursive let,
    -- which enables mutual recursion.
    let functions = DeclRecLets {bindings = joinMap (compileTpplFunction context) top.decls, info = fileInfo} in
    match _addDeclExn fileEnv loader functions with (fileEnv, loader) in

    -- 3. Model invocations.
    let work = lam loader. lam decl.
      match compileModelInvocation context hook.frontend hook.mkInferenceMethod loader fileEnv decl with Some (loader, fileEnv, invocation) then
        let decl = DeclLet
          { body = invocation
          , ident = nameSym ""
          , tyAnnot = tyunknown_
          , tyBody = tyunknown_
          , info = infoTm invocation
          } in
        (_addDeclExn fileEnv loader decl).1
      else loader in
    let loader = foldl work loader top.decls in

    loader

  sem registerMatrixFunctions : Loader -> Loader
  sem registerMatrixFunctions = | loader ->
    match includeFileExn "." "stdlib::ext/arr-ext.mc" loader with (arrEnv, loader) in
    match includeFileExn "." "stdlib::json.mc" loader with (jsonEnv, loader) in
    match includeFileExn "." "stdlib::basic-types.mc" loader with (basicEnv, loader) in
    match includeFileExn "." "stdlib::option.mc" loader with (optionEnv, loader) in
    let extArrName = _getTyConExn "ExtArr" arrEnv in
    let jsonArrName = _getConExn "JsonArray" jsonEnv in
    let optionMapM_ = appf2_ (nvar_ (_getVarExn "optionMapM" optionEnv)) in
    let optionMap_ = appf2_ (nvar_ (_getVarExn "optionMap" optionEnv)) in
    let extArrToSeq_ = app_ (nvar_ (_getVarExn "extArrToSeq" arrEnv)) in
    let extArrOfSeq = app_
      (nvar_ (_getVarExn "extArrOfSeq" arrEnv))
      (nvar_ (_getVarExn "extArrKindFloat64" arrEnv)) in

    -- NOTE(vipa, 2025-04-30): Json serialization
    let ser = ulam_ "serElem" (ulam_ "seq"
      (nconapp_ jsonArrName
        (map_ (var_ "serElem") (extArrToSeq_ (var_ "seq"))))) in
    let deser = ulam_ "deserElem" (ulam_ "json"
      (match_ (var_ "json") (npcon_ jsonArrName (pvar_ "arr"))
        (optionMap_ extArrOfSeq (optionMapM_ (var_ "deserElem") (var_ "arr")))
        (nconapp_ (_getConExn "None" basicEnv) unit_))) in
    let loader = registerCustomJsonSerializer extArrName {serializer = ser, deserializer = deser} loader in

    loader
end

let compileTpplToExecutable = lam frontend. lam transformations. lam mkInferenceMethod.
  use TreePPLThings in
  let log = mkPhaseLogState transformations.debugDumpPhases transformations.debugPhases transformations.invariantsToCheck in
  let loader = mkLoader typcheckEnvDefault [StripUtestHook ()] in
  let loader = enableCPPLCompilation transformations loader in
  let loader = addHook loader (CorePPLFileHook
    { options =
      { dpplTypeCheck = false
      , printSamples = false
      , printAcceptanceRate = false
      , defaultParticles = 0
      }
    , method = Default {runs = int_ 0}
    }) in
  let loader = enableEqGeneration loader in
  let loader = enableDesugar loader in
  let loader = enableJsonSerialization loader in
  let loader = enableDPrintViaPprint loader in
  let loader = registerMatrixFunctions loader in
  let loader = addHook loader (TreePPLHook {frontend = frontend, mkInferenceMethod = mkInferenceMethod}) in
  let loader = addHook loader (LowerUncurryHook ()) in
  endPhaseStatsExpr log "mk-cppl-loader" unit_;
  let loader = (includeFileExn "." frontend.input loader).1 in
  endPhaseStatsExpr log "include-file" unit_;
  let ast = buildFullAst loader in
  endPhaseStatsExpr log "build-full-ast" ast;

  let ocamlCompile : [String] -> [String] -> String -> String = lam libs. lam clibs. lam prog.
    let opts =
      { defaultCompileOptions
      with libraries = libs
      , cLibraries = clibs
      } in
    (match frontend.outputMl with Some path
     then writeFile path prog
     else ());
    let res = ocamlCompileWithConfig opts prog in
    sysMoveFile res.binaryPath frontend.output;
    sysChmodWriteAccessFile frontend.output;
    res.cleanup ();
    frontend.output in
  let hooks =
    { mkEmptyHooks ocamlCompile with
      externalImpls = mapUnion globalExternalImplsMap miStatsExtMap } in
  let ast = deadcodeElimination ast in
  endPhaseStatsExpr log "deadcode-elimination" ast;
  let ast = lowerAll ast in
  endPhaseStatsExpr log "lower-all" ast;
  let ast = constantFold ast in
  endPhaseStatsExpr log "constant-folding" ast;
  let res = compileMCore ast hooks in
  endPhaseStatsExpr log "compile-mcore" ast;
  res
