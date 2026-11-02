import Mathlib

set_option linter.style.header false

namespace PolyContracts

/-- Visibility of a method in a component. -/
inductive Visibility where
  | pbl -- public
  | prv -- private
  deriving Repr, DecidableEq

/-- Kind of computational method provided by a component. -/
inductive MethodKind where
  | service
  | command
  | source
  | well
  deriving Repr, DecidableEq

/-- Location of a component reference. -/
inductive ReferenceLocation where
  | local
  | remote
  deriving Repr, DecidableEq

end PolyContracts
