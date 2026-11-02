import PolyContracts.Component.Instance
import PolyContracts.Component.Requiring
import PolyContracts.Component.ContextProperties
import PolyContracts.Component.InstanceProperties
import PolyContracts.Component.ReferenceProperties

namespace PolyContracts

open scoped ReferenceNotation

namespace Component

/-! **## Requiring-relation properties** -/

section RequiringProperties

variable [ReferenceSemantics]
variable (𝕄 : Context)

local notation:max "𝕄̄(" M ")" =>
  Component.ContextualEnvironment 𝕄 M


/--
Membership in the admissible requiring relation is characterised
exactly by the `Requires` predicate.

Proof:
1) By definition, the requiring relation
     `RequiringRelation 𝕄 M`
   contains exactly those pairs `(r, b)` for which
     `Requires 𝕄 M r b`
   holds.
2) Therefore, the membership proposition
     `(r, b) ∈ RequiringRelation 𝕄 M`
   unfolds to exactly
     `Requires 𝕄 M r b`.
3) `rfl` (reflexivity, which proves an equality or equivalence when
   both sides reduce to the same expression) closes the proof
   because the two sides are definitionally identical.
-/
theorem mem_requiring_relation
    (M : Component)
    (r : Reference)
    (b : Method) :
    (r, b) ∈ RequiringRelation 𝕄 M ↔
      Requires 𝕄 M r b := by
  rfl


/--
If the requiring relation of `M` is well formed, every pair stored
in `M.R` belongs to the admissible requiring relation.

Proof:
1) The hypothesis
     `hWF : RequiringWellFormed 𝕄 M`
   states that the requiring relation stored in `M.R` is a subset
   of the admissible requiring relation
     `RequiringRelation 𝕄 M`.
2) The hypothesis
     `hR : (r, b) ∈ M.R`
   states that the pair `(r, b)` belongs to the requiring relation
   of `M`.
3) Applying `hWF` to `hR` uses the subset property to derive
     `(r, b) ∈ RequiringRelation 𝕄 M`.
4) `exact hWF hR` therefore supplies exactly the proof required by
   the goal.
-/
theorem requiring_member_admissible
    (M : Component)
    (r : Reference)
    (b : Method)
    (hWF : RequiringWellFormed 𝕄 M)
    (hR : (r, b) ∈ M.R) :
    (r, b) ∈ RequiringRelation 𝕄 M := by
  exact hWF hR

/--
Every reference occurring in a well-formed requiring relation
belongs to the reference set of the component.

Proof:
1) The hypotheses
     `hWF : RequiringWellFormed 𝕄 M`
   and
     `hR : (r, b) ∈ M.R`
   state respectively that the stored requiring relation is
   well formed and that `(r, b)` is one of its members.
2) `requiring_member_admissible 𝕄 M r b hWF hR` applies the
   previously proved admissibility result to obtain
     `h : (r, b) ∈ RequiringRelation 𝕄 M`.
3) `change Requires 𝕄 M r b at h` (`change`, which replaces a
   proposition by a definitionally equal form) exposes membership
   in the admissible requiring relation as the predicate
     `Requires 𝕄 M r b`.
4) By definition, `Requires 𝕄 M r b` is a conjunction whose first
   condition is
     `r ∈ M.E`.
5) `h.1` selects the first component of this conjunction, yielding
     `r ∈ M.E`,
   which is exactly the required conclusion.
-/
theorem requiring_reference_member
    (M : Component)
    (r : Reference)
    (b : Method)
    (hWF : RequiringWellFormed 𝕄 M)
    (hR : (r, b) ∈ M.R) :
    r ∈ M.E := by
  have h :=
    requiring_member_admissible 𝕄 M r b hWF hR
  change Requires 𝕄 M r b at h
  exact h.1


/--
Every pair occurring in a well-formed requiring relation identifies
a component definition targeted by its reference.

Proof:
1) The hypotheses
     `hWF : RequiringWellFormed 𝕄 M`
   and
     `hR : (r, b) ∈ M.R`
   state that the requiring relation is well formed and that
   `(r, b)` is one of its stored pairs.
2) `requiring_member_admissible 𝕄 M r b hWF hR` applies the
   previously proved admissibility theorem to obtain
     `h : (r, b) ∈ RequiringRelation 𝕄 M`.
3) `change Requires 𝕄 M r b at h` (`change`, which replaces a
   proposition by a definitionally equal form) exposes this
   membership as the predicate
     `Requires 𝕄 M r b`.
4) `h.2` selects the second part of the `Requires` conjunction,
   which contains an existentially quantified target component.
5) `rcases h.2 with ⟨N, hrN, _hNenv, _hb⟩` (`rcases`, which
   decomposes the existential witness and its associated
   properties) extracts
     `N      : Component`,
     `hrN    : r ▶ N`,
   together with the remaining conditions `_hNenv` and `_hb`,
   which are not needed for this theorem.
6) `⟨N, hrN⟩` constructs the required existential statement by
   providing `N` as the witness and `hrN` as the proof that
     `r ▶ N`.
-/
theorem requiring_target_exists
    (M : Component)
    (r : Reference)
    (b : Method)
    (hWF : RequiringWellFormed 𝕄 M)
    (hR : (r, b) ∈ M.R) :
    ∃ N : Component,
      r ▶ N := by
  have h :=
    requiring_member_admissible 𝕄 M r b hWF hR
  change Requires 𝕄 M r b at h
  rcases h.2 with ⟨N, hrN, _hNenv, _hb⟩
  exact ⟨N, hrN⟩


/--
Every pair occurring in a well-formed requiring relation has
a target component in the contextual environment of `M`.

Proof:
1) The hypotheses
     `hWF : RequiringWellFormed 𝕄 M`
   and
     `hR : (r, b) ∈ M.R`
   state that the requiring relation is well formed and that
   `(r, b)` is one of its stored pairs.
2) `requiring_member_admissible 𝕄 M r b hWF hR` applies the
   previously proved admissibility theorem to obtain
     `h : (r, b) ∈ RequiringRelation 𝕄 M`.
3) `change Requires 𝕄 M r b at h` (`change`, which replaces a
   proposition by a definitionally equal form) exposes this
   membership as the predicate
     `Requires 𝕄 M r b`.
4) `h.2` selects the part of `Requires` that contains the target
   component and its associated properties.
5) `rcases h.2 with ⟨N, hrN, hNenv, _hb⟩` (`rcases`, which
   decomposes the existential witness and its associated
   properties) extracts
     `N     : Component`,
     `hrN   : r ▶ N`,
   and
     `hNenv : N ∈ 𝕄̄(M)`.
   The remaining condition `_hb` is not needed for this theorem.
6) `⟨N, hrN, hNenv⟩` constructs the required existential statement
   by providing `N` as the witness together with the proofs that
     `r ▶ N`
   and
     `N ∈ 𝕄̄(M)`.
-/
theorem requiring_target_in_contextual_environment
    (M : Component)
    (r : Reference)
    (b : Method)
    (hWF : RequiringWellFormed 𝕄 M)
    (hR : (r, b) ∈ M.R) :
    ∃ N : Component,
      r ▶ N ∧
      N ∈ 𝕄̄(M) := by
  have h :=
    requiring_member_admissible 𝕄 M r b hWF hR
  change Requires 𝕄 M r b at h
  rcases h.2 with ⟨N, hrN, hNenv, _hb⟩
  exact ⟨N, hrN, hNenv⟩


/--
Every pair occurring in a well-formed requiring relation targets
a component whose selected method is a public service or command.

Proof:
1) The hypotheses
     `hWF : RequiringWellFormed 𝕄 M`
   and
     `hR : (r, b) ∈ M.R`
   state that the requiring relation is well formed and that
   `(r, b)` is one of its stored pairs.
2) `requiring_member_admissible 𝕄 M r b hWF hR` applies the
   previously proved admissibility theorem to obtain
     `h : (r, b) ∈ RequiringRelation 𝕄 M`.
3) `change Requires 𝕄 M r b at h` (`change`, which replaces a
   proposition by a definitionally equal form) exposes this
   membership as the predicate
     `Requires 𝕄 M r b`.
4) By definition, the second conjunct of `Requires 𝕄 M r b`
   states that there exists a component `N` such that
     `r ▶ N`,
     `N ∈ 𝕄̄(M)`,
   and
     `b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺)`.
5) `h.2` selects exactly this second conjunct, which already has
   the same form as the required existential conclusion.
6) `exact h.2` therefore closes the proof directly.
-/
theorem requiring_target_method
    (M : Component)
    (r : Reference)
    (b : Method)
    (hWF : RequiringWellFormed 𝕄 M)
    (hR : (r, b) ∈ M.R) :
    ∃ N : Component,
      r ▶ N ∧
      N ∈ 𝕄̄(M) ∧
      b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺) := by
  have h :=
    requiring_member_admissible 𝕄 M r b hWF hR
  change Requires 𝕄 M r b at h
  exact h.2

/--
If a reference `r` occurring in a well-formed requiring relation
is known to refer to component `N`, then `N` belongs to the
contextual environment of `M` and `b` is one of its public
services or commands.

Proof:
1) The hypotheses
     `hWF : RequiringWellFormed 𝕄 M`
   and
     `hR : (r, b) ∈ M.R`
   state that the requiring relation is well formed and that
   `(r, b)` is one of its stored pairs.
2) `requiring_member_admissible 𝕄 M r b hWF hR` applies the
   previously proved admissibility theorem to obtain
     `h : (r, b) ∈ RequiringRelation 𝕄 M`.
3) `change Requires 𝕄 M r b at h` (`change`, which replaces a
   proposition by a definitionally equal form) exposes this
   membership as the predicate
     `Requires 𝕄 M r b`.
4) `rcases h.2 with ⟨N', hrN', hN'env, hb⟩` (`rcases`, which
   decomposes the existential witness and its associated
   properties) extracts a target component `N'` together with
     `hrN'   : r ▶ N'`,
     `hN'env : N' ∈ 𝕄̄(M)`,
   and
     `hb      : b ∈ (N'.Pˢ⁺ ∪ N'.Pᵈ⁺)`.
5) The additional hypothesis
     `hrN : r ▶ N`
   states that the same reference `r` is also known to refer to
   component `N`.
6) `reference_component_unique r N N' hrN hrN'` applies the
   previously proved uniqueness of the component targeted by a
   reference to derive
     `hNN' : N = N'`.
7) `rw [hNN']` (`rw`, rewriting by equality) replaces `N` by
   `N'` in the goal. The remaining goal is therefore
     `N' ∈ 𝕄̄(M) ∧
      b ∈ (N'.Pˢ⁺ ∪ N'.Pᵈ⁺)`.
8) `⟨hN'env, hb⟩` constructs this conjunction from the two
   properties already obtained for `N'`, completing the proof.
-/
theorem requiring_target_unique
    (M N : Component)
    (r : Reference)
    (b : Method)
    (hWF : RequiringWellFormed 𝕄 M)
    (hR : (r, b) ∈ M.R)
    (hrN : r ▶ N) :
    N ∈ 𝕄̄(M) ∧
    b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺) := by
  have h :=
    requiring_member_admissible 𝕄 M r b hWF hR
  change Requires 𝕄 M r b at h
  rcases h.2 with ⟨N', hrN', hN'env, hb⟩
  have hNN' : N = N' :=
    reference_component_unique r N N' hrN hrN'
  rw [hNN']
  exact ⟨hN'env, hb⟩

/--
Every pair in a well-formed requiring relation is characterised by
a unique target component in the contextual environment whose public
service or command is selected by the relation.

Proof:
1) `requiring_reference_member 𝕄 M r b hWF hR` applies the
   previously proved reference-membership result to obtain
     `hrE : r ∈ M.E`.
2) `requiring_target_method 𝕄 M r b hWF hR` applies the previously
   proved target-method result to obtain
     `htarget :
        ∃ N : Component,
          r ▶ N ∧
          N ∈ 𝕄̄(M) ∧
          b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺)`.
3) `rcases htarget with ⟨N, hrN, hNenv, hb⟩` (`rcases`, which
   decomposes an existential witness together with its associated
   properties) extracts
     `N     : Component`,
     `hrN   : r ▶ N`,
     `hNenv : N ∈ 𝕄̄(M)`,
   and
     `hb    : b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺)`.
4) `refine ⟨hrE, ?_⟩` (`refine`, which partially constructs the
   required result and leaves the remaining part as a new goal)
   proves the first conjunct
     `r ∈ M.E`
   using `hrE`, leaving the unique-existence statement to prove.
5) `refine ⟨N, ⟨hrN, hNenv, hb⟩, ?_⟩` constructs the
   `∃!` statement by choosing `N` as the witness, proving that it
   satisfies
     `r ▶ N ∧
      N ∈ 𝕄̄(M) ∧
      b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺)`,
   and leaving only uniqueness to establish.
6) `intro N' hN'` introduces an arbitrary component `N'` satisfying
   the same target property. In particular,
     `hN'.1 : r ▶ N'`.
7) `reference_component_unique r N' N hN'.1 hrN` applies the
   previously proved uniqueness of the component targeted by a
   reference. Since the same reference `r` refers to both `N'`
   and `N`, it derives
     `N' = N`.
8) This proves the uniqueness condition of `∃!`, and together with
   `hrE` and the existence of `N`, establishes the complete
   characterisation of every pair in the well-formed requiring
   relation.
-/
theorem requiring_pair_characterisation
    (M : Component)
    (r : Reference)
    (b : Method)
    (hWF : RequiringWellFormed 𝕄 M)
    (hR : (r, b) ∈ M.R) :
    r ∈ M.E ∧
    ∃! N : Component,
      r ▶ N ∧
      N ∈ 𝕄̄(M) ∧
      b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺) := by
  have hrE :
      r ∈ M.E :=
    requiring_reference_member 𝕄 M r b hWF hR
  have htarget :
      ∃ N : Component,
        r ▶ N ∧
        N ∈ 𝕄̄(M) ∧
        b ∈ (N.Pˢ⁺ ∪ N.Pᵈ⁺) :=
    requiring_target_method 𝕄 M r b hWF hR
  rcases htarget with ⟨N, hrN, hNenv, hb⟩
  refine ⟨hrE, ?_⟩
  refine ⟨N, ⟨hrN, hNenv, hb⟩, ?_⟩
  intro N' hN'
  exact
    reference_component_unique
      r N' N hN'.1 hrN


end RequiringProperties
end Component
end PolyContracts
