
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
    // Structs
    map<Ident, StructDef>,

    // Classes
    map<Ident, ClassDef>,

    // Functions
    map<Ident, FunctionDef>
)

datatype StructDef = StructDef(
    // Generic parameters
    seq<GenericDef>,

    // Fields
    seq<VarDef>
)

datatype ClassDef = ClassDef(
    // Generic parameters
    seq<GenericDef>,

    // Fields
    seq<VarDef>
)

datatype FunctionDef = Fn(
    // Generic parameters
    seq<GenericDef>,

    // Function parameters
    seq<VarDef>,

    // Return type
    Type,

    // Function body
    Expr
)

datatype Expr = 
    Call(Expr, seq<Type>, seq<Expr>) |
    StructLiteral(Ident, seq<Type>, seq<VarDef>) |
    ClassLiteral(Ident, seq<Type>, seq<VarDef>) |
    Access(Mode, Path) |
    Let(Ident, Type, Expr, Expr)

datatype Path =
    Var(Ident) |
    Field(Path, Ident)

datatype GenericDef = Generic(Ident)

datatype VarDef = Var(Ident, Type)
