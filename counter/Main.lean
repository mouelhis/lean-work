import Mathlib

def init : Nat := 0

def next (cpt : Nat) : Nat :=
  if cpt < 100 then
    cpt + 10
  else
    cpt

inductive SynchronousCounter : Nat → Prop
  | initial : SynchronousCounter init
  | next {cpt : Nat} :
      SynchronousCounter cpt →
      SynchronousCounter (next cpt)



-- theorem cpt_in_range_attempt {cpt : Nat}
--   (h : SynchronousCounter cpt) : cpt ≤ 100 := by
--   induction h with
--   | initial =>
--       simp [init]

--   | @next cpt h ih =>
--       unfold next
--       split
--       · trace_state
--         omega
--       · exact ih

-- def firstBadTransition : Option Nat :=
--   (List.range 100).find? fun cpt =>
--     decide (cpt < 100 ∧ 100 < next cpt)

-- #eval do
--   match firstBadTransition with
--   | some cpt =>
--       IO.println s!"Counterexample: {cpt} -> {next cpt}"
--   | none =>
--       IO.println "No counterexample found"

lemma cpt_mod_ten_eq_zero {cpt : Nat}
    (h : SynchronousCounter cpt) :
    cpt % 10 = 0 := by
  induction h with
  | initial =>
      simp [init]

  | @next cpt h ih =>
      unfold next
      split
      · simp [ih]
      · exact ih

theorem cpt_in_range {cpt : Nat}
    (h : SynchronousCounter cpt) :
    cpt ≤ 100 := by
  induction h with
  | initial =>
      simp [init]

  | @next cpt h ih =>
      unfold next
      split
      · have hmod : cpt % 10 = 0 :=
          cpt_mod_ten_eq_zero h
        omega

      · exact ih
