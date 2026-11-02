import PolyContracts.Component.Method
import PolyContracts.Component.Component

namespace PolyContracts
namespace Method

/-! **## Method-parameter properties** -/

/--
The parameters of a method are exactly the union of its
input, output, and inout parameters.

Proof:
1) `ext p` (extensionality, which proves equality of sets by showing
   that they have exactly the same elements) reduces the goal to
   proving membership equivalence for an arbitrary parameter `p`.
2) `constructor` splits the equivalence into the two implications.
3) In the forward direction, `intro hp` assumes
     `hp : p ∈ a.p`.
4) `cases hmode : p.mode with` performs a case analysis on the mode
   of `p`, recording the corresponding equality in `hmode`.
   Since `ParameterMode` has exactly three constructors, there are
   three cases: `input`, `output`, and `inout`.
5) In the `input` case,
     `⟨hp, hmode⟩`
   proves `p ∈ a.i`; the nested `Or.inl` constructors place this
   proof in the left branch of
     `(a.i ∪ a.o) ∪ a.io`.
6) In the `output` case,
     `⟨hp, hmode⟩`
   proves `p ∈ a.o`; `Or.inr` selects the output branch inside
   `a.i ∪ a.o`, and the outer `Or.inl` selects this union.
7) In the `inout` case,
     `⟨hp, hmode⟩`
   proves `p ∈ a.io`; `Or.inr` selects the right-hand branch of
     `(a.i ∪ a.o) ∪ a.io`.
8) In the reverse direction, `intro hp` assumes that `p` belongs to
   the union of the three mode-specific parameter sets.
9) The two `rcases` expressions decompose the nested unions into the
   possible cases `p ∈ a.i`, `p ∈ a.o`, or `p ∈ a.io`.
10) In every case, `.1` selects the first component of the defining
    conjunction of the corresponding set, namely
      `p ∈ a.p`,
    which proves the reverse implication.
-/
theorem parameter_partition
    (a : Method) :
    a.p = (a.i ∪ a.o) ∪ a.io := by
  ext p
  constructor
  · intro hp
    cases hmode : p.mode with
    | input =>
        exact Or.inl (Or.inl ⟨hp, hmode⟩)
    | output =>
        exact Or.inl (Or.inr ⟨hp, hmode⟩)
    | inout =>
        exact Or.inr ⟨hp, hmode⟩
  · intro hp
    rcases hp with hio | hio
    · rcases hio with hi | ho
      · exact hi.1
      · exact ho.1
    · exact hio.1


/--
Input and output parameters of a method are disjoint.

Proof:
1) `rw [Set.disjoint_left]` rewrites set disjointness into the
   element-wise condition that no parameter can belong to both
   `a.i` and `a.o`.
2) `intro p hi ho` introduces an arbitrary parameter `p` together
   with
     `hi : p ∈ a.i`
   and
     `ho : p ∈ a.o`.
3) The first `change` (`change`, which replaces a proposition by a
   definitionally equal form) exposes `hi` as
     `p ∈ a.p ∧ p.mode = ParameterMode.input`.
4) The second `change` exposes `ho` as
     `p ∈ a.p ∧ p.mode = ParameterMode.output`.
5) `hi.2.symm` (`symm`, symmetry, which reverses an equality)
   transforms
     `p.mode = ParameterMode.input`
   into
     `ParameterMode.input = p.mode`.
6) `.trans ho.2` (`trans`, transitivity, which chains two
   equalities) derives
     `ParameterMode.input = ParameterMode.output`.
7) `cases h` eliminates this impossible equality because `input`
   and `output` are distinct constructors of `ParameterMode`,
   closing the proof.
-/
theorem input_output_disjoint
    (a : Method) :
    Disjoint a.i a.o := by
  rw [Set.disjoint_left]
  intro p hi ho
  change
    p ∈ a.p ∧
    p.mode = ParameterMode.input
    at hi
  change
    p ∈ a.p ∧
    p.mode = ParameterMode.output
    at ho
  have h :
      ParameterMode.input = ParameterMode.output :=
    hi.2.symm.trans ho.2
  cases h


/--
Input and inout parameters of a method are disjoint.

Proof:
1) `rw [Set.disjoint_left]` rewrites set disjointness into the
   element-wise condition that no parameter can belong to both
   `a.i` and `a.io`.
2) `intro p hi hio` introduces a parameter `p` together with
     `hi  : p ∈ a.i`
   and
     `hio : p ∈ a.io`.
3) `change` exposes these memberships as
     `p ∈ a.p ∧ p.mode = ParameterMode.input`
   and
     `p ∈ a.p ∧ p.mode = ParameterMode.inout`.
4) `hi.2.symm.trans hio.2` uses `.symm`
   (symmetry, which reverses an equality) and `.trans`
   (transitivity, which chains two equalities) to derive
     `ParameterMode.input = ParameterMode.inout`.
5) `cases h` eliminates this impossible equality because `input`
   and `inout` are distinct constructors of `ParameterMode`,
   closing the proof.
-/
theorem input_inout_disjoint
    (a : Method) :
    Disjoint a.i a.io := by
  rw [Set.disjoint_left]
  intro p hi hio
  change
    p ∈ a.p ∧
    p.mode = ParameterMode.input
    at hi
  change
    p ∈ a.p ∧
    p.mode = ParameterMode.inout
    at hio
  have h :
      ParameterMode.input = ParameterMode.inout :=
    hi.2.symm.trans hio.2
  cases h


/--
Output and inout parameters of a method are disjoint.

Proof:
1) `rw [Set.disjoint_left]` rewrites set disjointness into the
   element-wise condition that no parameter can belong to both
   `a.o` and `a.io`.
2) `intro p ho hio` introduces a parameter `p` together with
     `ho  : p ∈ a.o`
   and
     `hio : p ∈ a.io`.
3) `change` exposes these memberships as
     `p ∈ a.p ∧ p.mode = ParameterMode.output`
   and
     `p ∈ a.p ∧ p.mode = ParameterMode.inout`.
4) `ho.2.symm.trans hio.2` uses `.symm`
   (symmetry, which reverses an equality) and `.trans`
   (transitivity, which chains two equalities) to derive
     `ParameterMode.output = ParameterMode.inout`.
5) `cases h` eliminates this impossible equality because `output`
   and `inout` are distinct constructors of `ParameterMode`,
   closing the proof.
-/
theorem output_inout_disjoint
    (a : Method) :
    Disjoint a.o a.io := by
  rw [Set.disjoint_left]
  intro p ho hio
  change
    p ∈ a.p ∧
    p.mode = ParameterMode.output
    at ho
  change
    p ∈ a.p ∧
    p.mode = ParameterMode.inout
    at hio
  have h :
      ParameterMode.output = ParameterMode.inout :=
    ho.2.symm.trans hio.2
  cases h


/--
The input, output, and inout parameter sets of a method are
pairwise disjoint.

Proof:
1) `input_output_disjoint a` establishes that the input and output
   parameter sets are disjoint.
2) `input_inout_disjoint a` establishes that the input and inout
   parameter sets are disjoint.
3) `output_inout_disjoint a` establishes that the output and inout
   parameter sets are disjoint.
4) Combining these three previously proved results gives the
   complete pairwise-disjointness property.
-/
theorem parameter_sets_pairwise_disjoint
    (a : Method) :
    Disjoint a.i a.o ∧
    Disjoint a.i a.io ∧
    Disjoint a.o a.io := by
  exact
    ⟨input_output_disjoint a,
     input_inout_disjoint a,
     output_inout_disjoint a⟩

/--
A parameter belongs to the parameter set of a method exactly when
it is an input, output, or inout parameter.

Proof:
1) `constructor` splits the equivalence into the two implications.
2) In the forward direction, `intro hp` assumes
     `hp : p ∈ a.p`.
3) `cases hmode : p.mode with` performs a case analysis on the
   parameter mode, recording the corresponding equality in `hmode`.
4) In the `input` case, `⟨hp, hmode⟩` proves
     `p ∈ a.i`,
   and `Or.inl` selects the first branch of the disjunction.
5) In the `output` case, `⟨hp, hmode⟩` proves
     `p ∈ a.o`,
   and the nested `Or.inr` and `Or.inl` constructors select the
   second branch.
6) In the `inout` case, `⟨hp, hmode⟩` proves
     `p ∈ a.io`,
   and the two `Or.inr` constructors select the third branch.
7) In the reverse direction, the two `rcases` expressions separate
   the three possible memberships.
8) In each case, `.1` selects the underlying condition
     `p ∈ a.p`,
   which proves the reverse implication.
-/
theorem parameter_membership_characterisation
    (a : Method)
    (p : Parameter) :
    p ∈ a.p ↔
      p ∈ a.i ∨
      p ∈ a.o ∨
      p ∈ a.io := by
  constructor
  · intro hp
    cases hmode : p.mode with
    | input =>
        exact Or.inl ⟨hp, hmode⟩
    | output =>
        exact Or.inr (Or.inl ⟨hp, hmode⟩)
    | inout =>
        exact Or.inr (Or.inr ⟨hp, hmode⟩)
  · intro hp
    rcases hp with hi | hrest
    · exact hi.1
    · rcases hrest with ho | hio
      · exact ho.1
      · exact hio.1

/--
A method has at most one return parameter.

Proof:
1) The hypotheses
     `h₁ : a.r = some r₁`
   and
     `h₂ : a.r = some r₂`
   state that the same method has return parameters `r₁` and `r₂`.
2) `h₁.symm` (`symm`, symmetry, which reverses an equality)
   gives
     `some r₁ = a.r`.
3) `.trans h₂` (`trans`, transitivity, which chains two equalities)
   derives
     `some r₁ = some r₂`.
4) `Option.some.inj` uses the injectivity of the `some`
   constructor to conclude
     `r₁ = r₂`.
-/
theorem return_parameter_unique
    (a : Method)
    (r₁ r₂ : Variable)
    (h₁ : a.r = some r₁)
    (h₂ : a.r = some r₂) :
    r₁ = r₂ := by
  have h : some r₁ = some r₂ :=
    h₁.symm.trans h₂
  exact Option.some.inj h

/--
If method `a` returns variable `r`, then its return type
is the type `T[r]` of that variable.

Proof:
1) The hypothesis
     `h : a.r = some r`
   states that `r` is the return variable of `a`.
2) `change a.result = some r at h` (`change`, which replaces a
   proposition by a definitionally equal form) exposes the
   underlying `result` field used by `returnType`.
3) `simp [returnType, h]` unfolds `returnType`, uses `h` to select
   the `some r` branch of the match, and reduces the result to
     `r.type`.
-/
theorem return_type_of_result
    (a : Method)
    (r : Variable)
    (h : a.r = some r) :
    a.returnType = r.type := by
  change a.result = some r at h
  simp [returnType, h]

/--
If method `a` has no return parameter, then its return type
is `⊥`.

Proof:
1) The hypothesis
     `h : a.r = none`
   states that `a` has no return parameter.
2) `change a.result = none at h` exposes the underlying `result`
   field used by `returnType`.
3) `simp [returnType, h]` unfolds `returnType`, selects the `none`
   branch, and reduces the return type to
     `ValueType.noType`,
   which represents `⊥`.
-/
theorem void_return_type
    (a : Method)
    (h : a.r = none) :
    a.returnType = ValueType.noType := by
  change a.result = none at h
  simp [returnType, h]


/--
Every method either has no return parameter or has a return
parameter.

Proof:
1) `cases h : a.r with` performs a case analysis on the optional
   return parameter of `a`, while recording the original equality
   in `h`.
2) Since `a.r` has type `Option Variable`, there are exactly two
   possible cases: `none` and `some r`.
3) In the `none` case, Lean rewrites `a.r` in the goal to `none`.
   `left` selects the first branch, which therefore becomes
     `none = none`.
4) `rfl` (reflexivity, which proves an equality when both sides
   reduce to the same expression) closes this branch.
5) In the `some r` case, Lean rewrites `a.r` in the goal to
     `some r`.
6) `right` selects the existential branch
     `∃ r : Variable, some r = some r`.
7) `⟨r, rfl⟩` provides `r` as the return-variable witness and
   uses reflexivity to prove the corresponding equality.
8) Since `none` and `some r` exhaust `Option Variable`, the two
   cases establish that every method is either void or has a
   return parameter.
-/
theorem return_exhaustive
    (a : Method) :
    a.r = none ∨
    ∃ r : Variable,
      a.r = some r := by
  cases h : a.r with
  | none =>
      left
      rfl
  | some r =>
      right
      exact ⟨r, rfl⟩

/--
The return type of a method is completely characterised by its
optional return parameter: either the method has no return parameter
and its return type is `⊥`, or it has a return parameter `r` and its
return type is `T[r]`.

Proof:
1) `return_exhaustive a` states that exactly the relevant structural
   alternatives are available:
     `a.r = none`
   or
     `∃ r : Variable, a.r = some r`.
2) `rcases` (`rcases`, which decomposes disjunctions, existential
   witnesses, and conjunctions) separates these two alternatives.
3) In the first case,
     `hnone : a.r = none`.
   `left` selects the void branch of the conclusion.
4) `void_return_type a hnone` gives
     `a.returnType = ValueType.noType`.
5) `⟨hnone, void_return_type a hnone⟩` constructs the conjunction
   stating both that no return parameter exists and that the return
   type is `⊥`.
6) In the second case,
     `⟨r, hr⟩`
   provides a return variable `r` together with
     `hr : a.r = some r`.
7) `right` selects the non-void branch of the conclusion.
8) `return_type_of_result a r hr` gives
     `a.returnType = r.type`.
9) `⟨r, hr, return_type_of_result a r hr⟩` constructs the
   existential witness and its two required properties.
-/
theorem return_type_characterisation
    (a : Method) :
    (a.r = none ∧
     a.returnType = ValueType.noType) ∨
    ∃ r : Variable,
      a.r = some r ∧
      a.returnType = r.type := by
  rcases return_exhaustive a with hnone | ⟨r, hr⟩
  · left
    exact ⟨hnone, void_return_type a hnone⟩
  · right
    exact ⟨r, hr, return_type_of_result a r hr⟩

/--
An exception belongs to the exception set `a.e` exactly when it
occurs in the exception list of method `a`.

Proof:
1) By definition,
     `a.e`
   is the set containing exactly those exceptions that occur in
     `a.exceptions`.
2) `rfl` (reflexivity, which proves an equivalence when both sides
   reduce to the same expression) closes the proof because unfolding
   `Method.e` makes both sides definitionally identical.
-/
theorem exception_membership
    (a : Method)
    (ex : Exception) :
    ex ∈ a.e ↔
    ex ∈ a.exceptions := by
  rfl

/--
If a method declares no exceptions, then its exception set is empty.

Proof:
1) The hypothesis
     `h : a.exceptions = []`
   states that the exception list of method `a` contains no
   exceptions.
2) `ext ex` (extensionality, which proves equality of sets by
   showing that they have exactly the same elements) reduces the
   set equality
     `a.e = ∅`
   to membership equivalence for an arbitrary exception `ex`.
3) `simp [e, h]` unfolds the definition of `a.e`, replaces
   `a.exceptions` by the empty list using `h`, and simplifies
   membership in both the empty list and the empty set to `False`.
4) Both sides therefore reduce to the same proposition, proving
   that the exception set is empty.
-/
theorem exception_set_empty_of_no_exceptions
    (a : Method)
    (h : a.exceptions = []) :
    a.e = ∅ := by
  ext ex
  simp [e, h]


/--
A method has an empty exception set exactly when its exception
list contains no exceptions.

Proof:
1) `constructor` splits the equivalence into its two directions.
2) In the forward direction, `intro h` assumes
     `h : a.e = ∅`.
3) `cases hex : a.exceptions with` performs case analysis on the
   exception list.
4) If the list is empty, `rfl` proves
     `a.exceptions = []`.
5) If the list has the form `ex :: rest`, then `ex` necessarily
   belongs to `a.e`.
6) Rewriting by `h` would therefore make `ex` a member of the
   empty set, which is impossible; `simp [e, hex] at h` derives
   the contradiction.
7) In the reverse direction,
   `exception_set_empty_of_no_exceptions a h`
   directly applies the previously proved theorem.
-/
theorem exception_set_empty_iff
    (a : Method) :
    a.e = ∅ ↔
    a.exceptions = [] := by
  constructor
  · intro h
    cases hex : a.exceptions with
    | nil =>
        rfl
    | cons ex rest =>
        exfalso
        have hexmem : ex ∈ a.e := by
          simp [e, hex]
        rw [h] at hexmem
        exact hexmem
  · intro h
    exact exception_set_empty_of_no_exceptions a h


/--
The exception set of a method is non-empty exactly when it contains
at least one exception.

Proof:
1) `constructor` splits the equivalence into the two implications.
2) In the forward direction, `intro hne` assumes
     `hne : a.e ≠ ∅`.
3) `cases hlist : a.exceptions with` performs case analysis on the
   exception list while recording its form in `hlist`.
4) In the `nil` case,
     `hlist : a.exceptions = []`.
   `exception_set_empty_of_no_exceptions a hlist` therefore gives
     `a.e = ∅`.
5) Applying `hne` to this equality produces `False`; `.elim`
   (false elimination, which allows any proposition to be concluded
   from a contradiction) closes the impossible branch.
6) In the `cons ex rest` case, the exception `ex` is the head of
   the exception list.
7) `⟨ex, ...⟩` provides `ex` as a witness for the existential
   statement.
8) `simp [e, hlist]` unfolds the definition of `a.e` and establishes
   that the head exception `ex` belongs to the corresponding
   exception set.
9) In the reverse direction,
     `rintro ⟨ex, hex⟩ hempty`
   (`rintro`, which introduces hypotheses while immediately
   destructuring them) assumes an exception
     `hex : ex ∈ a.e`
   and, for contradiction,
     `hempty : a.e = ∅`.
10) `rw [hempty] at hex` rewrites the membership statement as
      `ex ∈ ∅`.
11) `simpa using hex` simplifies membership in the empty set to
    `False`, thereby proving
      `a.e ≠ ∅`.
-/
theorem exception_set_nonempty_iff
    (a : Method) :
    a.e ≠ ∅ ↔
    ∃ ex : Exception,
      ex ∈ a.e := by
  constructor
  · intro hne
    cases hlist : a.exceptions with
    | nil =>
        exact
          (hne
            (exception_set_empty_of_no_exceptions
              a hlist)).elim
    | cons ex rest =>
        exact ⟨ex, by simp [e, hlist]⟩
  · rintro ⟨ex, hex⟩ hempty
    rw [hempty] at hex
    simp at hex

/--
The exception set of a method is non-empty exactly when its
exception list is non-empty.

Proof:
1) `exception_set_empty_iff a` gives
     `a.e = ∅ ↔ a.exceptions = []`.
2) `not_congr` (congruence of negation, which transforms an
   equivalence `P ↔ Q` into `¬ P ↔ ¬ Q`) negates both sides of
   this equivalence.
3) The resulting statement is
     `a.e ≠ ∅ ↔ a.exceptions ≠ []`,
   which is exactly the required conclusion.
-/
theorem exception_set_nonempty_iff_list_nonempty
    (a : Method) :
    a.e ≠ ∅ ↔
    a.exceptions ≠ [] := by
  exact not_congr (exception_set_empty_iff a)

/--
A reference-method pair belongs to the requiring relation of
component `M` exactly when it belongs to the underlying relation
stored by `M`.

Proof:
1) By definition,
     `M.R`
   is the requiring relation stored in component `M`.
2) `rfl` (reflexivity, which proves an equivalence when both sides
   reduce to the same expression) closes the proof because
   membership in `M.R` unfolds directly to membership in
   `M.requiring`.
-/
theorem mem_requiring_relation
    (M : Component)
    (r : Reference)
    (a : Method) :
    (r, a) ∈ M.R ↔
    (r, a) ∈ M.requiring := by
  rfl


/--
Two methods have equal signatures exactly when their constituent
signature fields are equal.

Proof:
1) `constructor` splits the equivalence into its two implications.
2) In the forward direction, `intro h` assumes
     `h : a.signature = b.signature`.
3) `congrArg MethodSignature.name h` (`congrArg`, congruence of
   functions, which applies the same function to both sides of an
   equality) projects equality of the `name` fields.
4) `change` replaces the projected equality by the definitionally
   equal statement
     `a.name = b.name`.
5) The same argument is applied to the `parameters`, `result`, and
   `exceptions` fields.
6) The four resulting equalities are combined into the required
   conjunction.
7) In the reverse direction, `rintro` introduces and decomposes the
   four field equalities.
8) `simp [signature, hname, hparameters, hresult, hexceptions]`
   unfolds both method signatures and rewrites their corresponding
   fields using the supplied equalities.
9) After these rewrites, the two `MethodSignature` values are
   definitionally identical, which closes the equality.
-/
theorem signature_eq_iff
    (a b : Method) :
    a.signature = b.signature ↔
      a.name = b.name ∧
      a.parameters = b.parameters ∧
      a.result = b.result ∧
      a.exceptions = b.exceptions := by
  constructor
  · intro h
    have hname :=
      congrArg MethodSignature.name h
    change a.name = b.name at hname
    have hparameters :=
      congrArg MethodSignature.parameters h
    change a.parameters = b.parameters at hparameters
    have hresult :=
      congrArg MethodSignature.result h
    change a.result = b.result at hresult
    have hexceptions :=
      congrArg MethodSignature.exceptions h
    change a.exceptions = b.exceptions at hexceptions
    exact
      ⟨hname, hparameters, hresult, hexceptions⟩
  · rintro ⟨hname, hparameters, hresult, hexceptions⟩
    simp [signature, hname, hparameters, hresult, hexceptions]


/--
An attribute belongs to the attribute update set of method `a`
exactly when it occurs in the attribute list of `a`.

Proof:
1) By definition, `a.f` contains exactly the variables occurring
   in `a.attributes`.
2) Therefore, the propositions
     `x ∈ a.f`
   and
     `x ∈ a.attributes`
   are definitionally equivalent.
3) `rfl` (reflexivity, which proves an equivalence when both sides
   reduce to the same expression) closes the proof.
-/
theorem attribute_membership
    (a : Method)
    (x : Variable) :
    x ∈ a.f ↔
    x ∈ a.attributes := by
  rfl

/--
A local variable belongs to the local-variable update set of
method `a` exactly when it occurs in the local-variable list.

Proof:
1) By definition, `a.v` contains exactly the variables occurring
   in `a.locals`.
2) Therefore, the propositions
     `x ∈ a.v`
   and
     `x ∈ a.locals`
   are definitionally equivalent.
3) `rfl` (reflexivity, which proves an equivalence when both sides
   reduce to the same expression) closes the proof.
-/
theorem local_membership
    (a : Method)
    (x : Variable) :
    x ∈ a.v ↔
    x ∈ a.locals := by
  rfl

/--
The attribute update set of a method is empty exactly when its
attribute list is empty.

Proof:
1) `constructor` splits the equivalence into the two implications.
2) In the forward direction, `intro h` assumes
     `h : a.f = ∅`.
3) `cases hlist : a.attributes with` performs case analysis on the
   attribute list while recording its form in `hlist`.
4) In the `nil` case, the list is empty and `rfl` proves the
   required equality.
5) In the `cons x xs` case, the head attribute `x` belongs to
   `a.f`, contradicting the assumption that the set is empty.
6) `exfalso` changes the goal to `False`.
7) `simp [f, hlist]` establishes
     `hx : x ∈ a.f`
   using the fact that the head of a list belongs to that list.
8) `rw [h] at hx` replaces `a.f` by the empty set, and
   `simp at hx` derives the contradiction.
9) In the reverse direction, `intro h` assumes that the attribute
   list is empty.
10) `ext x` reduces equality of sets to membership equivalence.
11) `simp [f, h]` unfolds the attribute update set and simplifies
    membership in the empty list and empty set to `False`.
-/
theorem attribute_set_empty_iff
    (a : Method) :
    a.f = ∅ ↔
    a.attributes = [] := by
  constructor
  · intro h
    cases hlist : a.attributes with
    | nil =>
        rfl
    | cons x xs =>
        exfalso
        have hx : x ∈ a.f := by
          simp [f, hlist]
        rw [h] at hx
        simp at hx
  · intro h
    ext x
    simp [f, h]


/--
The local-variable update set of a method is empty exactly when
its local-variable list is empty.

Proof:
1) `constructor` splits the equivalence into the two implications.
2) In the forward direction, assume
     `h : a.v = ∅`.
3) Perform case analysis on `a.locals`.
4) If the list is empty, reflexivity proves the required equality.
5) If the list has the form `x :: xs`, its head `x` belongs to
   `a.v`, contradicting the assumption that `a.v` is empty.
6) `exfalso` changes the goal to `False`; the membership of `x`
   is established by unfolding `v` and simplifying the list.
7) Rewriting the update set using `h` and simplifying membership
   in the empty set closes the contradiction.
8) In the reverse direction, `ext x` reduces set equality to
   membership equivalence.
9) `simp [v, h]` unfolds the local-variable update set, rewrites
   the list to `[]`, and proves that both sets are empty.
-/
theorem local_set_empty_iff
    (a : Method) :
    a.v = ∅ ↔
    a.locals = [] := by
  constructor
  · intro h
    cases hlist : a.locals with
    | nil =>
        rfl
    | cons x xs =>
        exfalso
        have hx : x ∈ a.v := by
          simp [v, hlist]
        rw [h] at hx
        simp at hx
  · intro h
    ext x
    simp [v, h]

end Method
end PolyContracts
