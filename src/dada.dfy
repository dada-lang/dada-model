
// The mode lattice:
//
// My ----------> Our
// |               |
// v               v
// Borrow(o) ---> Shared(o) 
//
// where the `-->` arrow indicates "coercible to".
datatype Mode = My | Our | Borrow(set<Origin>) | Shared(set<Origin>)

datatype LoanKind = LkBorrow | LkShare

datatype Origin = OriginVar(Ident) | Loan(Path, LoanKind)

// Merging two modes produces their common "supermode".
//
// This is the "Greatest Lower Bound" on the mode lattice.
function ModeMerge(m1: Mode, m2: Mode): Mode {
    match (m1, m2)
    case (My, m) => m
    case (m, My) => m
    case (Our, Our) => Our
    case (Our, Shared(o)) => Shared(o)
    case (Shared(o), Our) => Shared(o)
    case (Our, Borrow(o)) => Shared(o)
    case (Borrow(o), Our) => Shared(o)
    case (Borrow(o1), Shared(o2)) => Shared(o1 + o2)
    case (Shared(o1), Borrow(o2)) => Shared(o1 + o2)
    case (Borrow(o1), Borrow(o2)) => Borrow(o1 + o2)
    case (Shared(o1), Shared(o2)) => Shared(o1 + o2)
}

// m1 is "coercible to" m2 if:
//
// * any program using m2 would also be legal with m1
//
// This implies:
//
// * anything you can do with a value in mode m1, you can do with a value in mode m2
//
// and
//
// * using a value in mode m1 imposes fewer restrictions on what you can do with other values
//
// This final bullet implies: the set of origins in m1 is a subset of the set in m2
// (i.e., you can coerce and add imprecision by assuming m2 came from more places).
function ModeCoercibleTo(m1: Mode, m2: Mode): bool {
    match (m1, m2)
    case (My, _) => true
    case (_, My) => false
    case (Our, _) => true
    case (_, Our) => false
    case (Borrow(o1), Borrow(o2)) => o1 <= o2
    case (_, Borrow(_)) => false
    case (Borrow(o1), Shared(o2)) => o1 <= o2
    case (Shared(o1), Shared(o2)) => o1 <= o2
}

lemma ModeCoercibleToReflexible() 
ensures forall m1 :: ModeCoercibleTo(m1, m1)
{
}

lemma ModeMergeYieldsCoercibleTo() 
ensures forall m1, m2 :: ModeCoercibleTo(m1, ModeMerge(m1, m2)) && ModeCoercibleTo(m2, ModeMerge(m1, m2))
{
}

datatype Ident = Id(string)

datatype Type = Struct(Ident, seq<Param>) | Class(Mode, Ident, seq<Param>) | Variable(Mode, Ident)

function MergeModeInType(m: Mode, t: Type): Type
decreases t
{
    match t
    case Struct(name, params) => Struct(name, MergeModeInParams(m, params))
    case Class(mode, name, params) =>
        var mode1 := ModeMerge(m, mode);
        var params1 := MergeModeInParams(mode1, params);
        Class(mode1, name, params1)
    case Variable(mode, name) =>
        Variable(ModeMerge(m, mode), name)
}

function MergeModeInParams(m: Mode, params: seq<Param>): seq<Param> 
decreases params
{
    seq(|params|, i requires 0 <= i < |params| => MergeModeInParam(m, params[i]))
}

function MergeModeInParam(m: Mode, param: Param): Param
decreases param
{
    match param
    case Type(t) => Type(MergeModeInType(m, t))
    case Origin(o) => Origin(o)
}

function TypeCoercibleTo(t_source: Type, t_target: Type): bool 
{
    match (t_source, t_target)
    case (Struct(name_source, params_source), Struct(name_target, params_target)) => 
    name_source == name_target && ParamsCoercibleTo(params_source, params_target)
    case (Struct(_, _), _) => false
    case (Class(mode_source, name_source, params_source), Class(mode_target, name_target, params_target)) => 
    name_source == name_target && ModeCoercibleTo(mode_source, mode_target) && ParamsCoercibleTo(params_source, params_target)
    case (Class(_, _, _), _) => false
    case (Variable(mode_source, name_source), Variable(mode_target, name_target)) => 
    name_source == name_target && ModeCoercibleTo(mode_source, mode_target)
    case (Variable(_, _), _) => false
}

function ParamsCoercibleTo(params_source: seq<Param>, params_target: seq<Param>): bool {
    // length should be equal, else ill-kinded
    |params_source| == |params_target| && forall i :: 0 <= i < |params_source| ==> ParamCoercibleTo(params_source[i], params_target[i])
}

function ParamCoercibleTo(param_source: Param, param_target: Param): bool {
    match (param_source, param_target)
    case (Type(t_source), Type(t_target)) => TypeCoercibleTo(t_source, t_target)
    case (Type(_), _) => false // indicates ill-kinded
    case (Origin(o_source), Origin(o_target)) => o_source <= o_target
    case (Origin(_), _) => false // indicates ill-kinded
}

datatype Param = Type(Type) | Origin(set<Origin>)

datatype ProgramDef = Program(
    structs: map<Ident, StructDef>,
    classes: map<Ident, ClassDef>,
    functions: map<Ident, FunctionDef>
)

datatype StructDef = StructDef(
    generics: seq<GenericDef>,
    fields: seq<VarDef>
)

datatype ClassDef = ClassDef(
    generics: seq<GenericDef>,
    fields: seq<VarDef>
)

datatype FunctionDef = Fn(
    generics: seq<GenericDef>,
    parameters: seq<VarDef>,
    returnType: Type,
    body: Expr
)

datatype Expr = 
    Call(Expr, seq<Type>, seq<Expr>) |
    StructLiteral(Ident, seq<Type>, seq<VarValue>) |
    ClassLiteral(Ident, seq<Type>, seq<VarValue>) |
    Access(AccessKind, Path) |
    Let(Ident, Type, Expr) |
    Semi(Expr, Expr) |
    Store(Path, Expr) |
    IfThenElse(Expr, Expr, Expr)

datatype Path =
    Var(Ident) |
    Field(Path, Ident)

datatype GenericDef = Generic(Ident)

datatype VarDef = Var(name: Ident, ty: Type)

datatype VarValue = Var(name: Ident, value: Expr)

datatype AccessKind = AccMy | AccOwn | AccBorrow | AccShare

datatype LivePath = LivePath(acc_kind: AccessKind, path: Path)

datatype Env = Env(
    program: ProgramDef,
    vars: map<Ident, Type>
)

function LivenessExpr(env: Env, expr: Expr, live_after: set<LivePath>): set<LivePath> {
    match expr
    case Call(e_func, _, e_args) => LivenessExpr(env, e_func, LivenessExprs(env, e_args, live_after))
    case StructLiteral(_, _, var_exprs) => LivenessVarValues(env, var_exprs, live_after)
    case ClassLiteral(_, _, var_exprs) => LivenessVarValues(env, var_exprs, live_after)
    case Access(access_kind, path) => live_after + {LivePath(access_kind, path)}
    case Let(name, _, initializer) => LivenessExpr(env, initializer, FilterAssigned(Path.Var(name), live_after))
    case Semi(e1, e2) => LivenessExpr(env, e1, LivenessExpr(env, e2, live_after))
    case Store(path, value) => LivenessExpr(env, value, FilterAssigned(path, live_after))
    case IfThenElse(cond_expr, then_expr, else_expr) => LivenessExpr(env, cond_expr, LivenessExpr(env, else_expr, live_after) + LivenessExpr(env, then_expr, live_after))
}

function LivenessExprs(env: Env, exprs: seq<Expr>, live_after: set<LivePath>): set<LivePath> {
    var l := |exprs|;
    if l == 0 then
        live_after
    else
        LivenessExprs(env, exprs[.. l-1], LivenessExpr(env, exprs[l-1], live_after))
}

function LivenessVarValues(env: Env, var_exprs: seq<VarValue>, live_after: set<LivePath>): set<LivePath> {
    var l := |var_exprs|;
    if l == 0 then
        live_after
    else
        LivenessVarValues(env, var_exprs[..l-1], LivenessExpr(env, var_exprs[l-1].value, live_after))
}

function FilterAssigned(prefix: Path, live_after: set<LivePath>): set<LivePath> {
    set p | p in live_after && !StartsWith(prefix, p.path) :: p
}

function StartsWith(prefix: Path, path: Path): bool {
    path == prefix || match path
    case Var(_) => false
    case Field(parent, _) => StartsWith(prefix, parent)
}