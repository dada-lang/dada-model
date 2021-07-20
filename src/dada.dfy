datatype Mode = My | Our | Borrow(set<Origin>) | Shared(set<Origin>)

datatype LoanKind = LkBorrow | LkShare

datatype Origin = OriginVar(Ident) | Loan(Path, LoanKind)

function ModeGlb(m1: Mode, m2: Mode): Mode {
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

function ModeLessThanEq(m1: Mode, m2: Mode): bool {
    match (m1, m2)
    case (m, My) => true
    case (m, Our) => true
    case (Borrow(o1), Borrow(o2)) => o1 <= o2
    case (Shared(o1), Borrow(o2)) => o1 <= o2
    case (Shared(o1), Shared(o2)) => o1 <= o2
    case _ => false
}

lemma ModeGlbTest1() 
ensures forall m1, m2 :: ModeLessThanEq(ModeGlb(m1, m2), m1)
{}

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

