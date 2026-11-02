import Mathlib

set_option autoImplicit false

namespace KInduction

/--
Run `next` exactly `steps` times, starting from `state`.
-/
def runFrom
    {State : Type}
    (next : State → State)
    (state : State) :
    Nat → State
  | 0 => state
  | steps + 1 => next (runFrom next state steps)

@[simp]
theorem runFrom_zero
    {State : Type}
    (next : State → State)
    (state : State) :
    runFrom next state 0 = state := by
  rfl

@[simp]
theorem runFrom_succ
    {State : Type}
    (next : State → State)
    (state : State)
    (steps : Nat) :
    runFrom next state (steps + 1) =
      next (runFrom next state steps) := by
  rfl

/--
Split an execution of `m + n` steps into `m` steps followed by
`n` steps.
-/
theorem runFrom_add
    {State : Type}
    (next : State → State)
    (state : State)
    (m n : Nat) :
    runFrom next state (m + n) =
      runFrom next (runFrom next state m) n := by
  induction n with
  | zero =>
      rw [Nat.add_zero]
      rfl

  | succ n ih =>
      rw [Nat.add_succ]

      change
        next (runFrom next state (m + n)) =
          next (runFrom next (runFrom next state m) n)

      exact congrArg next ih

/--
The first `k` states starting from `initial` satisfy `property`.
-/
def Base
    {State : Type}
    (next : State → State)
    (initial : State)
    (property : State → Prop)
    (k : Nat) : Prop :=
  ∀ i, i < k →
    property (runFrom next initial i)

/--
If `property` holds for `k` consecutive states beginning from an
arbitrary state, it holds after those `k` transitions.
-/
def Step
    {State : Type}
    (next : State → State)
    (property : State → Prop)
    (k : Nat) : Prop :=
  ∀ state,
    (∀ i, i < k →
      property (runFrom next state i)) →
    property (runFrom next state k)

/--
Soundness of deterministic k-induction.
-/
theorem sound
    {State : Type}
    (next : State → State)
    (initial : State)
    (property : State → Prop)
    {k : Nat}
    (hbase : Base next initial property k)
    (hstep : Step next property k) :
    ∀ n, property (runFrom next initial n) := by
  intro n

  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < k

      · exact hbase n hn

      · have hk_le_n : k ≤ n :=
          Nat.le_of_not_gt hn

        let m := n - k

        have hmk : m + k = n := by
          dsimp [m]
          omega

        have hwindow :
            ∀ i, i < k →
              property
                (runFrom next (runFrom next initial m) i) := by
          intro i hi

          have hlt : m + i < n := by
            omega

          have hprevious :
              property (runFrom next initial (m + i)) :=
            ih (m + i) hlt

          -- Rewrite exactly once, using the intended values m and i.
          rw [runFrom_add next initial m i] at hprevious

          exact hprevious

        have hfollowing :
            property
              (runFrom next (runFrom next initial m) k) :=
          hstep (runFrom next initial m) hwindow

        -- Merge the two execution segments.
        rw [← runFrom_add next initial m k] at hfollowing
        rw [hmk] at hfollowing

        exact hfollowing

end KInduction
