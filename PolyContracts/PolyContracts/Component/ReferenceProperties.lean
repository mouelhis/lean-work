import PolyContracts.Component.Reference
import PolyContracts.Component.Component

namespace PolyContracts

/-! **## Reference-location properties** -/

/--
Local and remote component references are disjoint.

Proof:
1) `rw [Set.disjoint_left]` rewrites set disjointness into the
   element-wise condition
     `∀ r, r ∈ M.Eˡ → r ∈ M.Eʳ → False`.
2) `intro r hlocal hremote` introduces a reference `r` together with
     `hlocal  : r ∈ M.Eˡ`
   and
     `hremote : r ∈ M.Eʳ`.
3) `change` exposes these memberships as location constraints:
     `r.location = ReferenceLocation.local`
   and
     `r.location = ReferenceLocation.remote`.
4) `hlocal.2.symm.trans hremote.2` uses `.symm`
   (symmetry, which reverses an equality) and `.trans`
   (transitivity, which chains two equalities) to derive
     `ReferenceLocation.local = ReferenceLocation.remote`.
5) `cases` eliminates this impossible equality between the distinct
   constructors `local` and `remote`, closing the proof.
-/
theorem reference_location_disjoint
    (M : Component) :
    Disjoint (M.Eˡ) (M.Eʳ) := by
  rw [Set.disjoint_left]
  intro r hlocal hremote
  change
    r ∈ M.E ∧
    r.location = ReferenceLocation.local
    at hlocal
  change
    r ∈ M.E ∧
    r.location = ReferenceLocation.remote
    at hremote
  have h :
      ReferenceLocation.local = ReferenceLocation.remote :=
    hlocal.2.symm.trans hremote.2
  cases h


/--
Local and remote references jointly cover the complete reference set.

Proof:
1) `ext r` reduces equality of sets to pointwise membership equivalence:
     `r ∈ M.Eˡ ∪ M.Eʳ ↔ r ∈ M.E`.
2) `cases h : r.location` performs case analysis on the two possible
   constructors of `ReferenceLocation`:
     `local` or `remote`.
3) `<;>` applies the following `simp` command to both generated cases.
4) `simp [Reference.E_supers_loc, h]` unfolds the location-specific
   reference subsets and uses the known value of `r.location`. In either
   case, membership in the corresponding local or remote subset reduces
   to membership in `M.E`.
-/
theorem reference_location_cover
    (M : Component) :
    M.Eˡ ∪ M.Eʳ = M.E := by
  ext r
  cases h : r.location <;>
    simp [Reference.E_supers_loc, h]

end PolyContracts
