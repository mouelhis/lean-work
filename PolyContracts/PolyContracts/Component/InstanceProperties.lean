import PolyContracts.Component.Instance

namespace PolyContracts

open scoped InstanceNotation
open scoped ResolutionNotation
open scoped ReferenceNotation


/-! **## Component-instance properties** -/

/--
Every component instance is an instance of its own
associated component definition.

Proof:
1) By definition, the notation
     `c :: c.component`
   means that the component associated with `c` is equal to
   `c.component`, giving the equality
     `c.component = c.component`.
2) `rfl` (reflexivity, which proves an equality when both sides
   reduce to the same expression) closes the proof because both
   sides are definitionally identical.
-/
theorem instance_of_component
    (c : ComponentInstance) :
    c :: c.component := by
  rfl


/--
A component instance has a unique component definition.
If `c` is an instance of both `M` and `N`, then `M = N`.

Proof:
1) By definition of the instance notation `::`, the hypothesis
     `hM : c :: M`
   means
     `c.component = M`.
2) Likewise, the hypothesis
     `hN : c :: N`
   means
     `c.component = N`.
3) `hM.symm` (`symm`, symmetry, which reverses an equality)
   transforms
     `c.component = M`
   into
     `M = c.component`.
4) `.trans hN` (`trans`, transitivity, which chains two equalities)
   combines
     `M = c.component`
   and
     `c.component = N`
   to derive
     `M = N`,
   which is exactly the required conclusion.
-/
theorem instance_component_unique
    (c : ComponentInstance)
    (M N : Component)
    (hM : c :: M)
    (hN : c :: N) :
    M = N := by
  exact hM.symm.trans hN


/-! **## Reference-resolution properties** -/

/--
A resolved component reference denotes at most one
run-time component instance.

Proof:
1) The hypotheses
     `h₁ : r ▷ c₁`
   and
     `h₂ : r ▷ c₂`
   state that the same reference `r` resolves to `c₁`
   and `c₂`, respectively.
2) `unfold ResolvesTo at h₁ h₂` (unfolding, which replaces a
   defined predicate by its definition) exposes these hypotheses as
     `resolve r = some c₁`
   and
     `resolve r = some c₂`.
3) `h₁.symm` (`symm`, symmetry, which reverses an equality)
   transforms
     `resolve r = some c₁`
   into
     `some c₁ = resolve r`.
4) `.trans h₂` (`trans`, transitivity, which chains two equalities)
   combines
     `some c₁ = resolve r`
   and
     `resolve r = some c₂`
   to derive
     `h : some c₁ = some c₂`.
5) `Option.some.inj h` uses the injectivity of the `some`
   constructor (equal `some` values must contain equal values) to
   conclude
     `c₁ = c₂`,
   which is exactly the required result.
-/
theorem reference_resolution_unique
    [ReferenceSemantics]
    (r : Reference)
    (c₁ c₂ : ComponentInstance)
    (h₁ : r ▷ c₁)
    (h₂ : r ▷ c₂) :
    c₁ = c₂ := by
  unfold ResolvesTo at h₁ h₂
  have h : some c₁ = some c₂ :=
    h₁.symm.trans h₂
  exact Option.some.inj h


/--
A reference that resolves to a run-time component instance
cannot simultaneously be unresolved.

Proof:
1) The hypothesis
     `h : r ▷ c`
   states that the reference `r` resolves to the run-time
   component instance `c`.
2) `intro hunresolved` assumes the negated case for contradiction,
   introducing
     `hunresolved : r ▷⊥`,
   which states that the same reference `r` is unresolved.
3) `unfold ResolvesTo at h` and
   `unfold Unresolved at hunresolved`
   (unfolding, which replaces defined predicates by their
   definitions) expose the hypotheses as
     `h           : resolve r = some c`
   and
     `hunresolved : resolve r = none`.
4) `h.symm` (`symm`, symmetry, which reverses an equality)
   transforms
     `resolve r = some c`
   into
     `some c = resolve r`.
5) `.trans hunresolved` (`trans`, transitivity, which chains two
   equalities) combines
     `some c = resolve r`
   and
     `resolve r = none`
   to derive
     `hcontra : some c = none`.
6) `cases hcontra` eliminates this impossible equality because
   `some c` and `none` are distinct constructors of `Option`,
   thereby closing the contradiction and proving
     `¬ r ▷⊥`.
-/
theorem resolved_not_unresolved
    [ReferenceSemantics]
    (r : Reference)
    (c : ComponentInstance)
    (h : r ▷ c) :
    ¬ r ▷⊥ := by
  intro hunresolved
  unfold ResolvesTo at h
  unfold Unresolved at hunresolved
  have hcontra : some c = none :=
    h.symm.trans hunresolved
  cases hcontra


/--
An unresolved reference cannot resolve to any
run-time component instance.

Proof:
1) The hypothesis
     `hunresolved : r ▷⊥`
   states that the reference `r` is unresolved.
2) To prove
     `¬ ∃ c : ComponentInstance, r ▷ c`,
   `intro hresolved` assumes for contradiction that there exists
   some component instance to which `r` resolves.
3) `rcases hresolved with ⟨c, hc⟩` (`rcases`, which decomposes an
   existential witness together with its proof) extracts
     `c  : ComponentInstance`
   and
     `hc : r ▷ c`.
4) `resolved_not_unresolved r c hc` applies the previously proved
   theorem to `hc`, yielding
     `¬ r ▷⊥`.
5) Applying this negation to
     `hunresolved : r ▷⊥`
   produces a contradiction, thereby proving that no such
   component instance `c` can exist.
-/
theorem unresolved_not_resolved
    [ReferenceSemantics]
    (r : Reference)
    (hunresolved : r ▷⊥) :
    ¬ ∃ c : ComponentInstance, r ▷ c := by
  intro hresolved
  rcases hresolved with ⟨c, hc⟩
  exact (resolved_not_unresolved r c hc) hunresolved


/--
Every component reference is either unresolved or resolves
to some run-time component instance.

Proof:
1) `cases h : ReferenceSemantics.resolve r with` performs a case
   analysis on the result of resolving `r`, while recording the
   corresponding equality as `h`.
2) Since `ReferenceSemantics.resolve r` has type
     `Option ComponentInstance`,
   there are exactly two possible cases: `none` or `some c`.
3) In the `none` case, `h` states
     `ReferenceSemantics.resolve r = none`.
   `left` selects the first branch of the disjunction,
     `r ▷⊥`,
   and `exact h` proves it because `Unresolved` is defined by this
   equality.
4) In the `some c` case, `h` states
     `ReferenceSemantics.resolve r = some c`.
   `right` selects the second branch of the disjunction,
     `∃ c : ComponentInstance, r ▷ c`.
5) `⟨c, h⟩` constructs the existential statement by providing
   `c` as the witness and `h` as the proof that
     `r ▷ c`.
6) Because the two constructors `none` and `some c` exhaust all
   possible values of `Option ComponentInstance`, the two cases
   establish that every reference is either unresolved or resolves
   to some run-time component instance.
-/
theorem reference_resolution_exhaustive
    [ReferenceSemantics]
    (r : Reference) :
    r ▷⊥ ∨
    ∃ c : ComponentInstance, r ▷ c := by
  cases h : ReferenceSemantics.resolve r with
  | none =>
      left
      exact h
  | some c =>
      right
      exact ⟨c, h⟩


/--
A component reference refers to at most one
component definition.

Proof:
1) The hypothesis
     `hM : r ▶ M`
   states that `r` refers to component definition `M`.
   By definition, this means that there exists some run-time
   component instance `c₁` such that
     `r ▷ c₁`
   and
     `c₁ :: M`.
2) `rcases hM with ⟨c₁, hr₁, hc₁⟩` (`rcases`, which decomposes
   an existential statement and its conjunction of properties)
   extracts
     `c₁  : ComponentInstance`,
     `hr₁ : r ▷ c₁`,
   and
     `hc₁ : c₁ :: M`.
3) Likewise,
     `rcases hN with ⟨c₂, hr₂, hc₂⟩`
   extracts
     `c₂  : ComponentInstance`,
     `hr₂ : r ▷ c₂`,
   and
     `hc₂ : c₂ :: N`.
4) `reference_resolution_unique r c₁ c₂ hr₁ hr₂` applies the
   previously proved uniqueness of reference resolution to derive
     `hinst : c₁ = c₂`.
5) `rw [← hinst] at hc₂` (`rw`, rewriting by equality, and `←`,
   which uses the equality in the reverse direction) replaces
   `c₂` by `c₁` in
     `hc₂ : c₂ :: N`,
   yielding
     `hc₂ : c₁ :: N`.
6) The same instance `c₁` is therefore an instance of both `M`
   and `N`. `instance_component_unique c₁ M N hc₁ hc₂` applies
   the previously proved uniqueness of a component definition to
   conclude
     `M = N`,
   which is exactly the required conclusion.
-/
theorem reference_component_unique
    [ReferenceSemantics]
    (r : Reference)
    (M N : Component)
    (hM : r ▶ M)
    (hN : r ▶ N) :
    M = N := by
  rcases hM with ⟨c₁, hr₁, hc₁⟩
  rcases hN with ⟨c₂, hr₂, hc₂⟩
  have hinst : c₁ = c₂ :=
    reference_resolution_unique r c₁ c₂ hr₁ hr₂
  rw [← hinst] at hc₂
  exact instance_component_unique c₁ M N hc₁ hc₂


/--
A reference that refers to a component definition
cannot be unresolved.

Proof:
1) The hypothesis
     `hM : r ▶ M`
   states that the reference `r` refers to the component
   definition `M`.
2) By definition of `RefersToComponent`, this means that there
   exists a run-time component instance `c` such that
     `r ▷ c`
   and
     `c :: M`.
3) `rcases hM with ⟨c, hr, hc⟩` (`rcases`, which decomposes an
   existential statement together with its associated properties)
   extracts
     `c  : ComponentInstance`,
     `hr : r ▷ c`,
   and
     `hc : c :: M`.
4) `resolved_not_unresolved r c hr` applies the previously proved
   result that a reference resolving to an instance cannot
   simultaneously be unresolved.
5) This yields
     `¬ r ▷⊥`,
   which is exactly the required conclusion.
-/
theorem refers_to_component_not_unresolved
    [ReferenceSemantics]
    (r : Reference)
    (M : Component)
    (hM : r ▶ M) :
    ¬ r ▷⊥ := by
  rcases hM with ⟨c, hr, hc⟩
  exact resolved_not_unresolved r c hr

end PolyContracts
