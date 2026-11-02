import PolyContracts.Component.Job

namespace PolyContracts
namespace Job

/-! **## Job-input properties** -/

/--
A variable belongs to the input set of a job exactly when it
occurs in the ordered input list of that job.

Proof:
1) By definition,
     `j.i`
   is the set containing exactly those variables that occur in
     `j.inputs`.
2) Therefore, the propositions
     `x ∈ j.i`
   and
     `x ∈ j.inputs`
   reduce to the same expression.
3) `rfl` (reflexivity, which proves an equivalence when both sides
   reduce to the same expression) closes the proof.
-/
theorem input_membership
    (j : Job)
    (x : Variable) :
    x ∈ j.i ↔
    x ∈ j.inputs := by
  rfl


/--
If a job declares no input parameters, then its input set is empty.

Proof:
1) The hypothesis
     `h : j.inputs = []`
   states that the job declares no input variables.
2) `ext x` (extensionality, which proves equality of sets by
   showing that they contain exactly the same elements) reduces
   the set equality
     `j.i = ∅`
   to membership equivalence for an arbitrary variable `x`.
3) `simp [i, h]` unfolds the definition of `j.i`, rewrites
   `j.inputs` to the empty list using `h`, and simplifies
   membership in both the empty list and the empty set to `False`.
4) The two sides therefore contain exactly the same elements,
   proving that
     `j.i = ∅`.
-/
theorem input_set_empty_of_no_inputs
    (j : Job)
    (h : j.inputs = []) :
    j.i = ∅ := by
  ext x
  simp [i, h]


/--
The input set of a job is empty exactly when its ordered input
list contains no parameters.

Proof:
1) `constructor` splits the equivalence into the two implications.
2) In the forward direction, `intro h` assumes
     `h : j.i = ∅`.
3) `cases hinputs : j.inputs with` performs case analysis on the
   ordered input list while recording its form in `hinputs`.
4) In the `nil` case, the input list is empty, so `rfl`
   (reflexivity, which proves an equality when both sides reduce
   to the same expression) closes the branch.
5) In the `cons x xs` case, the input list has head `x` and is
   therefore non-empty.
6) `exfalso` changes the goal to `False`, because this case must
   contradict the assumption that
     `j.i = ∅`.
7) `have hx : x ∈ j.i := by simp [i, hinputs]` unfolds `j.i`
   and establishes that the head variable `x` belongs to the
   job's input set.
8) `rw [h] at hx` (`rw`, rewriting by equality) replaces
   `j.i` by `∅`, giving
     `hx : x ∈ ∅`.
9) `simp at hx` simplifies membership in the empty set to
   `False`, closing the contradiction.
10) In the reverse direction, `intro h` assumes
      `j.inputs = []`.
11) `input_set_empty_of_no_inputs j h` applies the previously
    proved theorem to conclude
      `j.i = ∅`.
-/
theorem input_set_empty_iff
    (j : Job) :
    j.i = ∅ ↔
    j.inputs = [] := by
  constructor
  · intro h
    cases hinputs : j.inputs with
    | nil =>
        rfl
    | cons x xs =>
        exfalso
        have hx : x ∈ j.i := by
          simp [i, hinputs]
        rw [h] at hx
        simp at hx
  · intro h
    exact input_set_empty_of_no_inputs j h


/--
An attribute belongs to the attribute update set of job `j`
exactly when it occurs in the attribute list of `j`.

Proof:
1) By definition, `j.f` contains exactly the variables occurring
   in `j.attributes`.
2) Therefore, the propositions
     `x ∈ j.f`
   and
     `x ∈ j.attributes`
   are definitionally equivalent.
3) `rfl` (reflexivity, which proves an equivalence when both sides
   reduce to the same expression) closes the proof.
-/
theorem attribute_membership
    (j : Job)
    (x : Variable) :
    x ∈ j.f ↔
    x ∈ j.attributes := by
  rfl

/--
A local variable belongs to the local-variable update set of
job `j` exactly when it occurs in the local-variable list.

Proof:
1) By definition, `j.v` contains exactly the variables occurring
   in `j.locals`.
2) Therefore, the propositions
     `x ∈ j.v`
   and
     `x ∈ j.locals`
   are definitionally equivalent.
3) `rfl` (reflexivity, which proves an equivalence when both sides
   reduce to the same expression) closes the proof.
-/
theorem local_membership
    (j : Job)
    (x : Variable) :
    x ∈ j.v ↔
    x ∈ j.locals := by
  rfl

/--
The attribute update set of a job is empty exactly when its
attribute list is empty.

Proof:
1) `constructor` splits the equivalence into the two implications.
2) In the forward direction, `intro h` assumes
     `h : j.f = ∅`.
3) `cases hlist : j.attributes with` performs case analysis on the
   attribute list.
4) In the empty-list case, `rfl` proves the required equality.
5) In the non-empty case, the head attribute `x` belongs to
   `j.f`, contradicting the assumption that the set is empty.
6) `exfalso` changes the goal to `False`.
7) `simp [f, hlist]` proves that the head belongs to the update set.
8) Rewriting the update set using `h` and simplifying membership
   in the empty set closes the contradiction.
9) In the reverse direction, `ext x` reduces the set equality to
   membership equivalence.
10) `simp [f, h]` unfolds the update set and simplifies both sides
    to the empty-set membership condition.
-/
theorem attribute_set_empty_iff
    (j : Job) :
    j.f = ∅ ↔
    j.attributes = [] := by
  constructor
  · intro h
    cases hlist : j.attributes with
    | nil =>
        rfl
    | cons x xs =>
        exfalso
        have hx : x ∈ j.f := by
          simp [f, hlist]
        rw [h] at hx
        simp at hx
  · intro h
    ext x
    simp [f, h]

/--
The local-variable update set of a job is empty exactly when its
local-variable list is empty.

Proof:
1) `constructor` splits the equivalence into the two implications.
2) In the forward direction, assume
     `h : j.v = ∅`.
3) Perform case analysis on the list `j.locals`.
4) If the list is empty, reflexivity proves the required equality.
5) If the list is non-empty, its head `x` belongs to `j.v`.
6) Unfolding `v` establishes this membership, which contradicts
   the assumption that `j.v` is empty.
7) `rw [h] at hx` rewrites the membership into the empty set, and
   `simp at hx` closes the contradiction.
8) In the reverse direction, use set extensionality and simplify
   the definition of `j.v` with the empty-list hypothesis.
-/
theorem local_set_empty_iff
    (j : Job) :
    j.v = ∅ ↔
    j.locals = [] := by
  constructor
  · intro h
    cases hlist : j.locals with
    | nil =>
        rfl
    | cons x xs =>
        exfalso
        have hx : x ∈ j.v := by
          simp [v, hlist]
        rw [h] at hx
        simp at hx
  · intro h
    ext x
    simp [v, h]

end Job
end PolyContracts
