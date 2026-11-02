import PolyContracts.Component.Component

namespace PolyContracts
namespace Component

/--
Public and private methods are disjoint.

Proof:
1) `rw [Set.disjoint_left]` rewrites set disjointness into the
   element-wise condition
     `∀ m, m ∈ M.P⁺ → m ∈ M.P⁻ → False`.
2) `intro` introduces a method `m` together with
     `hpub : m ∈ M.P⁺` and `hpriv : m ∈ M.P⁻`.
3) `change` exposes these memberships as visibility constraints:
     `m.visibility = Visibility.pbl`
     and
     `m.visibility = Visibility.prv`.
4) `hpub.2` gives `m.visibility = Visibility.pbl`, while
   `hpriv.2` gives `m.visibility = Visibility.prv`. Using `.symm`
   (symmetry, which reverses an equality) on the first equality and
   `.trans` (transitivity, which chains two equalities) yields
     `Visibility.pbl = Visibility.prv`.
5) `cases` eliminates this impossible equality between the distinct
   constructors `Visibility.pbl` and `Visibility.prv`, closing the proof.
-/
theorem visibility_disjoint (M : Component) :
    Disjoint (M.P⁺) (M.P⁻) := by
  rw [Set.disjoint_left]
  intro m hpub hpriv
  change m ∈ M.P ∧ m.visibility = Visibility.pbl at hpub
  change m ∈ M.P ∧ m.visibility = Visibility.prv at hpriv
  have h : Visibility.pbl = Visibility.prv :=
    hpub.2.symm.trans hpriv.2
  cases h

/--
Methods belonging to two distinct kinds are disjoint.

Proof:
1) `rw [Set.disjoint_left]` rewrites set disjointness into
     `∀ m, m ∈ P(k₁) → m ∈ P(k₂) → False`.
2) `intro` introduces a method `m` together with
     `hk₁ : m ∈ P(k₁)` and `hk₂ : m ∈ P(k₂)`.
3) `change` exposes these memberships as kind constraints:
     `m.kind = k₁`
     and
     `m.kind = k₂`.
4) `hk₁.2` gives `m.kind = k₁`, while `hk₂.2` gives
   `m.kind = k₂`. Using `.symm` (symmetry, which reverses an equality)
   on the first equality and `.trans` (transitivity, which chains two
   equalities) yields
     `k₁ = k₂`.
5) `exact hne h` applies `hne : k₁ ≠ k₂` to the derived equality
   `h : k₁ = k₂`, producing `False` and closing the proof.
-/
theorem kind_disjoint
    (M : Component)
    (k₁ k₂ : MethodKind)
    (hne : k₁ ≠ k₂) :
    Disjoint
      (Component.P_supers_kind M.P k₁)
      (Component.P_supers_kind M.P k₂) := by
  rw [Set.disjoint_left]
  intro m hk₁ hk₂
  change m ∈ M.P ∧ m.kind = k₁ at hk₁
  change m ∈ M.P ∧ m.kind = k₂ at hk₂
  have h : k₁ = k₂ :=
    hk₁.2.symm.trans hk₂.2
  exact hne h

/--
Services and commands are disjoint.

Proof:
1) `apply kind_disjoint` reduces the goal to proving that the
   corresponding method kinds are distinct.
2) `simp` proves `MethodKind.service ≠ MethodKind.command`
   because they are different constructors of `MethodKind`.
-/
theorem service_command_disjoint (M : Component) :
    Disjoint (M.Pˢ) (M.Pᵈ) := by
  apply kind_disjoint
  simp

/--
Services and data sources are disjoint.

Proof:
1) `apply kind_disjoint` reduces the goal to distinctness of the
   two method kinds.
2) `simp` proves `MethodKind.service ≠ MethodKind.source`.
-/
theorem service_source_disjoint (M : Component) :
    Disjoint (M.Pˢ) (M.Pᵒ) := by
  apply kind_disjoint
  simp

/--
Services and data wells are disjoint.

Proof:
1) `apply kind_disjoint` reduces the goal to distinctness of the
   two method kinds.
2) `simp` proves `MethodKind.service ≠ MethodKind.well`.
-/
theorem service_well_disjoint (M : Component) :
    Disjoint (M.Pˢ) (M.Pʷ) := by
  apply kind_disjoint
  simp

/--
Commands and data sources are disjoint.

Proof:
1) `apply kind_disjoint` reduces the goal to distinctness of the
   two method kinds.
2) `simp` proves `MethodKind.command ≠ MethodKind.source`.
-/
theorem command_source_disjoint (M : Component) :
    Disjoint (M.Pᵈ) (M.Pᵒ) := by
  apply kind_disjoint
  simp

/--
Commands and data wells are disjoint.

Proof:
1) `apply kind_disjoint` reduces the goal to distinctness of the
   two method kinds.
2) `simp` proves `MethodKind.command ≠ MethodKind.well`.
-/
theorem command_well_disjoint (M : Component) :
    Disjoint (M.Pᵈ) (M.Pʷ) := by
  apply kind_disjoint
  simp

/--
Data sources and data wells are disjoint.

Proof:
1) `apply kind_disjoint` reduces the goal to distinctness of the
   two method kinds.
2) `simp` proves `MethodKind.source ≠ MethodKind.well`.
-/
theorem source_well_disjoint (M : Component) :
    Disjoint (M.Pᵒ) (M.Pʷ) := by
  apply kind_disjoint
  simp

/--
Public and private methods jointly cover the complete method set.

Proof:
1) `ext m` reduces equality of sets to pointwise membership equivalence:
     `m ∈ M.P⁺ ∪ M.P⁻ ↔ m ∈ M.P`.
2) `cases h : m.visibility` performs case analysis on the two possible
   constructors of `Visibility`:
     `m.visibility = Visibility.pbl`
     or
     `m.visibility = Visibility.prv`.
3) `<;>` applies the following `simp` command to both cases.
4) `simp [P_supers_vis, h]` unfolds the visibility subsets and uses the
   known value `h` of `m.visibility`. In the public case, membership reduces
   to `m ∈ M.P⁺`; in the private case, it reduces to `m ∈ M.P⁻`.
   Both cases simplify to the required equivalence with `m ∈ M.P`.
-/
theorem visibility_cover (M : Component) :
    M.P⁺ ∪ M.P⁻ = M.P := by
  ext m
  cases h : m.visibility <;>
    simp [P_supers_vis, h]


/--
The four method-kind subsets jointly cover the complete method set.

Proof:
1) `ext m` reduces equality of sets to pointwise membership equivalence:
     `m ∈ M.Pˢ ∪ M.Pᵈ ∪ M.Pᵒ ∪ M.Pʷ ↔ m ∈ M.P`.
2) `cases h : m.kind` performs case analysis on the four constructors
   of `MethodKind`:
     `service`, `command`, `source`, or `well`.
3) `<;>` applies the following `simp` command to every generated case.
4) `simp [Component.P_supers_kind, h]` unfolds the kind-specific subsets
   and uses the known value `h` of `m.kind`. In each case, membership in
   exactly one of `M.Pˢ`, `M.Pᵈ`, `M.Pᵒ`, or `M.Pʷ` reduces to
   membership in `M.P`, establishing the required equivalence.
-/
theorem kind_cover (M : Component) :
    M.Pˢ ∪ M.Pᵈ ∪ M.Pᵒ ∪ M.Pʷ = M.P := by
  ext m
  cases h : m.kind <;>
    simp [Component.P_supers_kind, h]

/--
The visibility partition and the method-kind partition describe the
same complete method set.

Proof:
1) `rw [visibility_cover]` rewrites the left-hand side
     `M.P⁺ ∪ M.P⁻`
   as the complete method set `M.P`.
2) `rw [kind_cover]` rewrites the right-hand side
     `M.Pˢ ∪ M.Pᵈ ∪ M.Pᵒ ∪ M.Pʷ`
   as the same set `M.P`.
3) Both sides are therefore identical, which closes the equality.
-/
theorem partitions_equivalent (M : Component) :
    M.P⁺ ∪ M.P⁻ = M.Pˢ ∪ M.Pᵈ ∪ M.Pᵒ ∪ M.Pʷ := by
  rw [visibility_cover]
  rw [kind_cover]

/--
A method selected simultaneously by kind `k` and visibility `v`
is exactly a method belonging to both corresponding subsets.

Proof:
1) `ext m` reduces equality of sets to pointwise membership equivalence:
     `m ∈ P(k,v) ↔ m ∈ P(k) ∩ P(v)`.
2) `simp` unfolds `P_supers_kind_vis`, `P_supers_kind`, and
   `P_supers_vis`, reducing both sides to conjunctions expressing
     `m ∈ M.P`, `m.kind = k`, and `m.visibility = v`.
3) `and_assoc`, `and_left_comm`, and `and_comm` allow `simp` to
   rearrange these conjunctions so both sides have the same logical form,
   completing the proof.
-/
theorem kind_visibility_eq_intersection
    (M : Component)
    (k : MethodKind)
    (v : Visibility) :
    Component.P_supers_kind_vis M.P k v =
      Component.P_supers_kind M.P k ∩
      Component.P_supers_vis M.P v := by
  ext m
  simp [Component.P_supers_kind_vis,
        Component.P_supers_kind,
        Component.P_supers_vis,
        and_assoc, and_left_comm, and_comm]

/--
Public services are the intersection of services and public methods.

Proof:
1) `apply kind_visibility_eq_intersection` instantiates the generic
   kind/visibility intersection theorem with
     `k = MethodKind.service`
     `v = Visibility.pbl`.
2) The resulting goal is exactly
     `M.Pˢ⁺ = M.Pˢ ∩ M.P⁺`.
-/
theorem service_public_eq_intersection (M : Component) :
    M.Pˢ⁺ = M.Pˢ ∩ M.P⁺ := by
  apply kind_visibility_eq_intersection


/--
Private services are the intersection of services and private methods.

Proof:
1) `apply kind_visibility_eq_intersection` instantiates the generic theorem with
     `k = MethodKind.service`
     `v = Visibility.prv`.
2) This gives
     `M.Pˢ⁻ = M.Pˢ ∩ M.P⁻`.
-/
theorem service_private_eq_intersection (M : Component) :
    M.Pˢ⁻ = M.Pˢ ∩ M.P⁻ := by
  apply kind_visibility_eq_intersection


/--
Public commands are the intersection of commands and public methods.

Proof:
1) `apply kind_visibility_eq_intersection` instantiates the generic theorem with
     `k = MethodKind.command`
     `v = Visibility.pbl`.
2) This gives
     `M.Pᵈ⁺ = M.Pᵈ ∩ M.P⁺`.
-/
theorem command_public_eq_intersection (M : Component) :
    M.Pᵈ⁺ = M.Pᵈ ∩ M.P⁺ := by
  apply kind_visibility_eq_intersection


/--
Private commands are the intersection of commands and private methods.

Proof:
1) `apply kind_visibility_eq_intersection` instantiates the generic theorem with
     `k = MethodKind.command`
     `v = Visibility.prv`.
2) This gives
     `M.Pᵈ⁻ = M.Pᵈ ∩ M.P⁻`.
-/
theorem command_private_eq_intersection (M : Component) :
    M.Pᵈ⁻ = M.Pᵈ ∩ M.P⁻ := by
  apply kind_visibility_eq_intersection


/--
Public data sources are the intersection of sources and public methods.

Proof:
1) `apply kind_visibility_eq_intersection` instantiates the generic theorem with
     `k = MethodKind.source`
     `v = Visibility.pbl`.
2) This gives
     `M.Pᵒ⁺ = M.Pᵒ ∩ M.P⁺`.
-/
theorem source_public_eq_intersection (M : Component) :
    M.Pᵒ⁺ = M.Pᵒ ∩ M.P⁺ := by
  apply kind_visibility_eq_intersection


/--
Private data sources are the intersection of sources and private methods.

Proof:
1) `apply kind_visibility_eq_intersection` instantiates the generic theorem with
     `k = MethodKind.source`
     `v = Visibility.prv`.
2) This gives
     `M.Pᵒ⁻ = M.Pᵒ ∩ M.P⁻`.
-/
theorem source_private_eq_intersection (M : Component) :
    M.Pᵒ⁻ = M.Pᵒ ∩ M.P⁻ := by
  apply kind_visibility_eq_intersection


/--
Public data wells are the intersection of wells and public methods.

Proof:
1) `apply kind_visibility_eq_intersection` instantiates the generic theorem with
     `k = MethodKind.well`
     `v = Visibility.pbl`.
2) This gives
     `M.Pʷ⁺ = M.Pʷ ∩ M.P⁺`.
-/
theorem well_public_eq_intersection (M : Component) :
    M.Pʷ⁺ = M.Pʷ ∩ M.P⁺ := by
  apply kind_visibility_eq_intersection


/--
Private data wells are the intersection of wells and private methods.

Proof:
1) `apply kind_visibility_eq_intersection` instantiates the generic theorem with
     `k = MethodKind.well`
     `v = Visibility.prv`.
2) This gives
     `M.Pʷ⁻ = M.Pʷ ∩ M.P⁻`.
-/
theorem well_private_eq_intersection (M : Component) :
    M.Pʷ⁻ = M.Pʷ ∩ M.P⁻ := by
  apply kind_visibility_eq_intersection

/--
Any public subset corresponding to a data source or data well is empty
for a well-formed component.

Proof:
1) `ext m` reduces equality with the empty set to pointwise membership.
2) `simp only [Set.mem_empty_iff_false, iff_false]` turns the goal into
   proving that membership in the public subset is impossible.
3) `intro hm` assumes
     `hm : m ∈ P(k, pbl)`,
   and `change` exposes this as
     `m ∈ M.P`,
     `m.kind = k`,
     `m.visibility = Visibility.pbl`.
4) `rcases hk` considers the two possibilities
     `k = MethodKind.source`
     or
     `k = MethodKind.well`,
   and derives that `m` itself is a source or a well.
5) `hM` applies component well-formedness to obtain
     `hpriv : m.visibility = Visibility.prv`.
   From `hm`, we also have
     `hpub : m.visibility = Visibility.pbl`.
6) `hpub.symm.trans hpriv` uses symmetry and transitivity to derive
     `Visibility.pbl = Visibility.prv`.
7) `cases hcontra` eliminates this impossible equality between distinct
   visibility constructors, closing the proof.
-/
theorem public_source_or_well_empty
    (M : Component)
    (hM : M.WellFormed)
    (k : MethodKind)
    (hk : k = MethodKind.source ∨ k = MethodKind.well) :
    Component.P_supers_kind_vis M.P k Visibility.pbl = ∅ := by
  ext m
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hm
  change
    m ∈ M.P ∧
    m.kind = k ∧
    m.visibility = Visibility.pbl
    at hm
  have hkind :
      m.kind = MethodKind.source ∨
      m.kind = MethodKind.well := by
    rcases hk with hsource | hwell
    · exact Or.inl (hm.2.1.trans hsource)
    · exact Or.inr (hm.2.1.trans hwell)
  have hpriv : m.visibility = Visibility.prv :=
    hM m hm.1 hkind
  have hpub : m.visibility = Visibility.pbl :=
    hm.2.2
  have hcontra : Visibility.pbl = Visibility.prv :=
    hpub.symm.trans hpriv
  cases hcontra

/--
Public data sources are empty in a well-formed component.

Proof:
1) `apply public_source_or_well_empty M hM` reduces the goal to proving
   that the selected kind is either a data source or a data well.
2) `exact Or.inl rfl` chooses the left branch of the disjunction and proves
     `MethodKind.source = MethodKind.source`
   by reflexivity.
-/
theorem public_sources_empty
    (M : Component)
    (hM : M.WellFormed) :
    M.Pᵒ⁺ = ∅ := by
  apply public_source_or_well_empty M hM
  exact Or.inl rfl

/--
Public data wells are empty in a well-formed component.

Proof:
1) `apply public_source_or_well_empty M hM` reduces the goal to proving
   that the selected kind is either a data source or a data well.
2) `exact Or.inr rfl` chooses the right branch of the disjunction and proves
     `MethodKind.well = MethodKind.well`
   by reflexivity.
-/
theorem public_wells_empty
    (M : Component)
    (hM : M.WellFormed) :
    M.Pʷ⁺ = ∅ := by
  apply public_source_or_well_empty M hM
  exact Or.inr rfl


/--
A job belongs to the job set `M.J` exactly when it belongs to the
underlying set of jobs stored by component `M`.

Proof:
1) By definition, `M.J` is exactly `M.jobs`.
2) Therefore both membership propositions reduce to the same
   expression.
3) `rfl` (reflexivity, which proves an equivalence when both sides
   reduce to the same expression) closes the proof.
-/
theorem job_membership
    (M : Component)
    (j : Job) :
    j ∈ M.J ↔
    j ∈ M.jobs := by
  rfl


/-! **## Behaviour-domain properties** -/

/--
A method behaviour belongs to the behaviour domain of component `M`
exactly when its underlying method is a public method of `M`.

Proof:
1) `BehaviourDomain` contains two kinds of values: public methods
   wrapped with `Behaviour.method`, and jobs wrapped with
   `Behaviour.job`.
2) For a value of the form `Behaviour.method a`, the job alternative
   is impossible because the two constructors of `Behaviour` are
   distinct.
3) The method alternative therefore reduces precisely to
     `a ∈ M.P⁺`.
4) `simp [BehaviourDomain]` unfolds the behaviour domain, uses
   injectivity and disjointness of the `Behaviour` constructors,
   and simplifies the existential statement.
-/
theorem method_mem_behaviour_domain_iff
    (M : Component)
    (a : Method) :
    Behaviour.method a ∈ M.BehaviourDomain ↔
    a ∈ M.P⁺ := by
  simp [BehaviourDomain]


/--
A job behaviour belongs to the behaviour domain of component `M`
exactly when its underlying job belongs to `M.J`.

Proof:
1) `BehaviourDomain` contains public methods and jobs.
2) For a value of the form `Behaviour.job j`, the method alternative
   is impossible because `Behaviour.method` and `Behaviour.job` are
   distinct constructors.
3) The job alternative therefore reduces precisely to
     `j ∈ M.J`.
4) `simp [BehaviourDomain]` unfolds the definition and simplifies
   the constructor equalities and existential statement.
-/
theorem job_mem_behaviour_domain_iff
    (M : Component)
    (j : Job) :
    Behaviour.job j ∈ M.BehaviourDomain ↔
    j ∈ M.J := by
  simp [BehaviourDomain]

/--
A behaviour belongs to the behaviour domain of component `M`
exactly when it is either a public method of `M` or a job of `M`.

Proof:
1) By definition, membership in `M.BehaviourDomain` is the
   disjunction of two alternatives.
2) The first alternative provides a public method `a` together with
   the equality identifying the behaviour as `Behaviour.method a`.
3) The second alternative provides a job `j` together with the
   equality identifying the behaviour as `Behaviour.job j`.
4) Unfolding `BehaviourDomain` makes the two sides definitionally
   identical.
5) `rfl` closes the proof.
-/
theorem behaviour_domain_membership_characterisation
    (M : Component)
    (b : Behaviour) :
    b ∈ M.BehaviourDomain ↔
      (∃ a : Method,
        a ∈ M.P⁺ ∧
        b = Behaviour.method a) ∨
      (∃ j : Job,
        j ∈ M.J ∧
        b = Behaviour.job j) := by
  rfl
end Component
end PolyContracts
