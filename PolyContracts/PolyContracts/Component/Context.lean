import PolyContracts.Component.Component

set_option linter.unusedVariables false

namespace PolyContracts

/-! ## Context -/

/--
A context 𝕄 is a set of component definitions.
-/
abbrev Context := Set Component

namespace Component

/-! ## Contextual environment -/

/--
The contextual environment 𝕄̄(M) of component M in context 𝕄
contains the component definitions exposing at least one
public service or public command.

Mathematically: 𝕄̄(M) = {N ∈ 𝕄 | (N.P^s+ ∪ N.P^c+) ≠ ∅}.
-/
def ContextualEnvironment
    (𝕄 : Context)
    (M : Component) : Set Component :=
  {N | N ∈ 𝕄 ∧
       (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅}

end Component


/-! **## Sanity checks** -/

#check Component.ContextualEnvironment

end PolyContracts
