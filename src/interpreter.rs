use formality_core::Map;

use crate::grammar::{FieldId, TypeName, Var};

pub struct StackFrame {
    variables: Map<Var, Value>,
}

pub struct Heap {
    objects: Vec<Value>,
}

enum Value {
    Int(i64),
    Pointer(usize),
    Object(ObjectData),
    Uninitialized,
}

struct ObjectData {
    flag: ObjectFlag,
    class: TypeName,
    fields: Map<FieldId, Value>,
}

enum ObjectFlag {
    Owned,
    Shared,
}
