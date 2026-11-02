import PolyContracts.Component.Instance
import PolyContracts.Component.Reference
import PolyContracts.Component.Context

namespace PolyContracts

-- open scoped ResolutionNotation
open scoped InstanceNotation
open scoped ReferenceNotation

namespace Component

/-! **## Requiring relation** -/

section RequiringRelation

variable (𝕄 : Context)

local notation:max "𝕄̄(" M ")" =>
  Component.ContextualEnvironment 𝕄 M

/--
`Requires 𝕄 M r b` states that component `M`, in context `𝕄`,
requires method `b` through reference `r`.

The reference belongs to `M`, refers to a component definition `N`
in the contextual environment of `M`, and `b` is a public service
or public command provided by `N`.
-/
def Requires
    [ReferenceSemantics]
    (M : Component)
    (r : Reference)
    (b : Method) : Prop :=
  r ∈ M.E ∧
  ∃ N : Component,
    r ▶ N ∧
    N ∈ 𝕄̄(M) ∧
    b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺)

/--
The requiring relation of component `M` in context `𝕄`
is the set of reference-method pairs satisfying `Requires`.
-/
def RequiringRelation
    [ReferenceSemantics]
    (M : Component) : Set (Reference × Method) :=
  {rb | Requires 𝕄 M rb.1 rb.2}

/--
The requiring relation stored by component `M` is well formed
when it is contained in the admissible requiring relation
induced by `M` and context `𝕄`.
-/
def RequiringWellFormed
    [ReferenceSemantics]
    (M : Component) : Prop :=
  M.R ⊆ RequiringRelation 𝕄 M

end RequiringRelation


/-! **## Sanity checks** -/

#check fun [ReferenceSemantics]
           (𝕄 : Context)
           (M : Component)
           (r : Reference)
           (b : Method) =>
  Requires 𝕄 M r b

#check fun [ReferenceSemantics]
           (𝕄 : Context)
           (M : Component) =>
  RequiringRelation 𝕄 M

end Component

end PolyContracts
