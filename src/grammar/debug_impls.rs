use std::fmt::Debug;

use super::{perm_tree_impls::PermTreeRoot, ClassName, ClassTy, Perm, PermTree};

impl Debug for ClassTy {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if f.alternate() {
            f.debug_struct("ClassTy")
                .field("name", &self.name)
                .field("parameters", &self.parameters)
                .finish()
        } else {
            match self.name {
                ClassName::Tuple(_) => {
                    write!(f, "(")?;
                    for (p, i) in self.parameters.iter().zip(0..) {
                        if i > 0 {
                            write!(f, ", ")?;
                        }
                        write!(f, "{:?}", p)?;
                    }
                    write!(f, ")")?;
                }

                _ => {
                    write!(f, "{:?}", self.name)?;

                    if self.parameters.len() > 0 {
                        write!(f, "[")?;
                        for (p, i) in self.parameters.iter().zip(0..) {
                            if i > 0 {
                                write!(f, ", ")?;
                            }
                            write!(f, "{:?}", p)?;
                        }
                        write!(f, "]")?;
                    }
                }
            }
            Ok(())
        }
    }
}

impl<R> Debug for PermTree<R>
where
    R: PermTreeRoot,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Root(arg0) => f.debug_tuple("Root").field(arg0).finish(),
            Self::Shared(arg0, arg1) => f.debug_tuple("Shared").field(arg0).field(arg1).finish(),
            Self::Leased(arg0, arg1) => f.debug_tuple("Leased").field(arg0).field(arg1).finish(),
            Self::Var(arg0, arg1) => f.debug_tuple("Var").field(arg0).field(arg1).finish(),
        }
    }
}
