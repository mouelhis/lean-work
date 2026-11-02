import PolyContracts.Component.Instance

namespace PolyContracts
namespace Component


/-! **## Contextual-environment properties** -/

section ContextualEnvironmentProperties

variable (𝕄 : Context)

local notation:max "𝕄̄(" M ")" =>
  Component.ContextualEnvironment 𝕄 M


/--
Membership in the contextual environment is characterised by
membership in 𝕄 and exposure of a public service or command.

Proof:
1) By definition, `𝕄̄(M)` contains exactly those components `N`
   such that
     `N ∈ 𝕄`
   and
     `(N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`.
2) Therefore, the proposition
     `N ∈ 𝕄̄(M)`
   unfolds to exactly
     `N ∈ 𝕄 ∧ (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`.
3) `rfl` (reflexivity, which proves an equality or equivalence when
   both sides reduce to the same expression) proves the equivalence
   because, after unfolding the definition of `𝕄̄(M)`, both sides
   are definitionally equal.
-/
theorem mem_contextual_environment
    (M N : Component) :
    N ∈ 𝕄̄(M) ↔
      N ∈ 𝕄 ∧
      (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅ := by
  rfl


/--
The contextual environment of `M` is a subset of the context `𝕄`.

Proof:
1) To prove the subset relation
     `𝕄̄(M) ⊆ 𝕄`,
   `intro N hN` introduces an arbitrary component `N` together with
     `hN : N ∈ 𝕄̄(M)`.
2) `mem_contextual_environment 𝕄 M N` gives the equivalence
     `N ∈ 𝕄̄(M) ↔
        N ∈ 𝕄 ∧ (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`.
3) `.mp hN` applies the forward direction of this equivalence to
   `hN`, producing
     `h : N ∈ 𝕄 ∧ (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`.
4) `h.1` selects the first component of this conjunction,
     `N ∈ 𝕄`,
   which is exactly the required conclusion.
-/
theorem contextual_environment_subset_context
    (M : Component) :
    𝕄̄(M) ⊆ 𝕄 := by
  intro N hN
  have h :=
    (mem_contextual_environment 𝕄 M N).mp hN
  exact h.1


/--
Every component in the contextual environment exposes at least
one public service or public command.

Proof:
1) The hypothesis
     `hN : N ∈ 𝕄̄(M)`
   states that `N` belongs to the contextual environment of `M`.
2) `mem_contextual_environment 𝕄 M N` gives the equivalence
     `N ∈ 𝕄̄(M) ↔
        N ∈ 𝕄 ∧ (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`.
3) `.mp` (modus ponens, which applies the forward direction of an
   equivalence) applied to `hN` produces
     `h : N ∈ 𝕄 ∧ (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`.
4) `h.2` selects the second component of this conjunction,
     `(N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`,
   which is exactly the required conclusion.
-/
theorem contextual_environment_exposes_public
    (M N : Component)
    (hN : N ∈ 𝕄̄(M)) :
    (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅ := by
  have h :=
    (mem_contextual_environment 𝕄 M N).mp hN
  exact h.2

end ContextualEnvironmentProperties


/-! **## Contextual-reference properties** -/

section ContextualReferenceProperties

variable [ReferenceSemantics]

variable (𝕄 : Context)

local notation:max "𝕄̄(" M ")" =>
  Component.ContextualEnvironment 𝕄 M

open scoped ReferenceNotation


/--
A well-formed reference belonging to component `M` and referring to
component definition `N` identifies a component in the contextual
environment of `M`.

Proof:
1) The hypothesis
     `hM : M.ReferencesWellFormed 𝕄`
   states that every well-formed reference of `M` that refers to a
   component definition satisfies the conditions required for that
   target component to belong to the context and expose public
   functionality.
2) Applying
     `hM r hr N hN`
   to the reference `r`, its membership
     `hr : r ∈ M.E`,
   and the fact
     `hN : r ▶ N`,
   produces
     `h : N ∈ 𝕄 ∧ (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`.
3) `mem_contextual_environment 𝕄 M N` gives the equivalence
     `N ∈ 𝕄̄(M) ↔
        N ∈ 𝕄 ∧ (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅`.
4) `.mpr` (which applies the right-to-left direction of an
   equivalence) uses `h` to derive
     `N ∈ 𝕄̄(M)`,
   which is exactly the required conclusion.
-/
theorem reference_target_in_contextual_environment
    (M N : Component)
    (hM : M.ReferencesWellFormed 𝕄)
    (r : Reference)
    (hr : r ∈ M.E)
    (hN : r ▶ N) :
    N ∈ 𝕄̄(M) := by
  have h :=
    hM r hr N hN
  exact
    (mem_contextual_environment 𝕄 M N).mpr h


/--
A self-referencing component belongs to its own contextual
environment when its references are well formed.

Proof:
1) The hypothesis
     `hself : M.SelfReferencing`
   states that `M` contains a reference that refers back to
   component definition `M` itself.
2) `rcases hself with ⟨r, hr, href⟩` (`rcases`, which decomposes
   an existential statement together with its associated
   properties) extracts
     `r    : Reference`,
     `hr   : r ∈ M.E`,
   and
     `href : r ▶ M`.
3) Applying
     `hWF r hr M href`
   uses reference well-formedness together with the self-reference
   to obtain
     `h : M ∈ 𝕄 ∧ (M.Pˢ⁺ ∪ M.Pᵈ⁺) ≠ ∅`.
4) `mem_contextual_environment 𝕄 M M` gives the equivalence
     `M ∈ 𝕄̄(M) ↔
        M ∈ 𝕄 ∧ (M.Pˢ⁺ ∪ M.Pᵈ⁺) ≠ ∅`.
5) `.mpr` (which applies the right-to-left direction of an
   equivalence) uses `h` to conclude
     `M ∈ 𝕄̄(M)`,
   which is exactly the required result.
-/
theorem self_reference_in_contextual_environment
    (M : Component)
    (hWF : M.ReferencesWellFormed 𝕄)
    (hself : M.SelfReferencing) :
    M ∈ 𝕄̄(M) := by
  rcases hself with ⟨r, hr, href⟩
  have h :=
    hWF r hr M href
  exact
    (mem_contextual_environment 𝕄 M M).mpr h

end ContextualReferenceProperties

end Component
end PolyContracts
