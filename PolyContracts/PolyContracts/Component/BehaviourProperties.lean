import PolyContracts.Component.Behaviour

namespace PolyContracts
namespace Behaviour

/-! **## Behaviour update-set properties** -/

/--
A method behaviour has exactly the same attribute update set
as its underlying method.

Proof:
1) By definition, `Behaviour.f` performs case analysis on the
   behaviour.
2) For `Behaviour.method a`, the method branch reduces directly to
     `a.f`.
3) `rfl` (reflexivity, which proves an equality when both sides
   reduce to the same expression) closes the proof.
-/
theorem method_attribute_updates
    (a : Method) :
    (Behaviour.method a).f = a.f := by
  rfl


/--
A method behaviour has exactly the same local-variable update set
as its underlying method.

Proof:
1) By definition, `Behaviour.v` performs case analysis on the
   behaviour.
2) For `Behaviour.method a`, the method branch reduces directly to
     `a.v`.
3) `rfl` closes the proof because both sides are definitionally
   identical.
-/
theorem method_local_updates
    (a : Method) :
    (Behaviour.method a).v = a.v := by
  rfl


/--
A job behaviour has exactly the same attribute update set
as its underlying job.

Proof:
1) By definition, `Behaviour.f` performs case analysis on the
   behaviour.
2) For `Behaviour.job j`, the job branch reduces directly to
     `j.f`.
3) `rfl` closes the proof because both sides are definitionally
   identical.
-/
theorem job_attribute_updates
    (j : Job) :
    (Behaviour.job j).f = j.f := by
  rfl


/--
A job behaviour has exactly the same local-variable update set
as its underlying job.

Proof:
1) By definition, `Behaviour.v` performs case analysis on the
   behaviour.
2) For `Behaviour.job j`, the job branch reduces directly to
     `j.v`.
3) `rfl` closes the proof because both sides are definitionally
   identical.
-/
theorem job_local_updates
    (j : Job) :
    (Behaviour.job j).v = j.v := by
  rfl

/--
Membership in the attribute update set of a behaviour is determined
by whether the behaviour wraps a method or a job.

Proof:
1) `cases b with` performs case analysis on the two constructors
   of `Behaviour`.
2) In the method case, the goal reduces to membership in the
   underlying method's attribute update set.
3) In the job case, the goal reduces to membership in the
   underlying job's attribute update set.
4) `simp [f]` unfolds `Behaviour.f` in each case and establishes
   the corresponding existential branch.
-/
theorem attribute_membership_characterisation
    (b : Behaviour)
    (x : Variable) :
    x ∈ b.f ↔
      (∃ a : Method,
        b = Behaviour.method a ∧
        x ∈ a.f) ∨
      (∃ j : Job,
        b = Behaviour.job j ∧
        x ∈ j.f) := by
  cases b with
  | method a =>
      simp [f]
  | job j =>
      simp [f]

/--
Membership in the local-variable update set of a behaviour is
determined by whether the behaviour wraps a method or a job.

Proof:
1) `cases b with` performs case analysis on the two constructors
   of `Behaviour`.
2) In the method case, the goal reduces to membership in the
   underlying method's local-variable update set.
3) In the job case, the goal reduces to membership in the
   underlying job's local-variable update set.
4) `simp [v]` unfolds `Behaviour.v` in each case and establishes
   the corresponding existential branch.
-/
theorem local_membership_characterisation
    (b : Behaviour)
    (x : Variable) :
    x ∈ b.v ↔
      (∃ a : Method,
        b = Behaviour.method a ∧
        x ∈ a.v) ∨
      (∃ j : Job,
        b = Behaviour.job j ∧
        x ∈ j.v) := by
  cases b with
  | method a =>
      simp [v]
  | job j =>
      simp [v]

end Behaviour
end PolyContracts
