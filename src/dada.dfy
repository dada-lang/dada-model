
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

datatype Type = Struct(Ident, seq<Param>) | Class(Mode, Ident, seq<Param>) | Variable(Mode, Ident) | TMode(Mode, Type)

datatype Param = PType(Type)

datatype ProgramDef = Program(
    // Structs
    seq<StructDef>,

    // Structs
    seq<ClassDef>,

    // Functions
    seq<FunctionDef>
)

datatype StructDef = StructDef(
    Ident,

    // Generic parameters
    seq<GenericDef>,

    // Fields
    seq<VarDef>
)

datatype ClassDef = ClassDef(
    Ident,

    // Generic parameters
    seq<GenericDef>,

    // Fields
    seq<VarDef>
)

datatype FunctionDef = Fn(
    // Function name
    Ident, 

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
    Access(Mode, Path)

datatype Path =
    Var(Ident) |
    Field(Path, Ident)

datatype GenericDef = Generic(Ident)

datatype VarDef = Var(Ident, Type)

