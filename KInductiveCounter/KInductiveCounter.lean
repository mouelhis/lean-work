import KInduction

set_option autoImplicit false

namespace KInductiveCounter

open KInduction

/-! ## Counter model -/

def initial : Nat :=
  0

def next (cpt : Nat) : Nat :=
  if cpt < 100 then
    cpt + 10
  else
    cpt

def Safe (cpt : Nat) : Prop :=
  cpt ≤ 100

/-! ## Executable k-induction checker -/

def safeB (cpt : Nat) : Bool :=
  decide (cpt ≤ 100)

def windowSafeB (k cpt : Nat) : Bool :=
  (List.range k).all fun i =>
    safeB (runFrom next cpt i)

def baseCheckB (k : Nat) : Bool :=
  windowSafeB k initial

def stepCheckB (k : Nat) : Bool :=
  (List.range 101).all fun cpt =>
    !(windowSafeB k cpt) ||
      safeB (runFrom next cpt k)

def kInductionCheckB (k : Nat) : Bool :=
  baseCheckB k && stepCheckB k

def firstSuccessfulK (maxK : Nat) : Option Nat :=
  ((List.range maxK).map fun i => i + 1).find?
    kInductionCheckB

def discoveredK : Nat :=
  (firstSuccessfulK 100).getD 1

structure KInductionCertificate where
  k : Nat
  basePassed : Bool
  stepPassed : Bool
deriving Repr

def certificate : KInductionCertificate where
  k := discoveredK
  basePassed := baseCheckB discoveredK
  stepPassed := stepCheckB discoveredK

theorem certificate_valid :
    0 < certificate.k ∧
    certificate.basePassed = true ∧
    certificate.stepPassed = true := by
  native_decide

def printCertificate : IO Unit := do
  IO.println "k-induction certificate"
  IO.println s!"  discovered k: {certificate.k}"
  IO.println s!"  base passed: {certificate.basePassed}"
  IO.println s!"  step passed: {certificate.stepPassed}"

#eval printCertificate

/-! ## Soundness of the executable checker -/

lemma safeB_correct (cpt : Nat) :
    safeB cpt = true ↔ Safe cpt := by
  simp [safeB, Safe]

lemma windowSafeB_sound
    {k cpt : Nat}
    (h :
      ∀ i, i < k →
        Safe (runFrom next cpt i)) :
    windowSafeB k cpt = true := by
  unfold windowSafeB
  apply List.all_eq_true.mpr

  intro i hi
  apply (safeB_correct _).mpr
  apply h i

  simpa using hi

lemma baseCheckB_sound
    {k : Nat}
    (hcheck : baseCheckB k = true) :
    Base next initial Safe k := by
  unfold Base
  intro i hi

  unfold baseCheckB windowSafeB at hcheck

  have hall :=
    List.all_eq_true.mp hcheck

  have hsafe :
      safeB (runFrom next initial i) = true :=
    hall i (by simpa using hi)

  exact (safeB_correct _).mp hsafe

lemma stepCheckB_sound
    {k : Nat}
    (hk : 0 < k)
    (hcheck : stepCheckB k = true) :
    Step next Safe k := by
  unfold Step
  intro cpt hwindow

  have hcptSafe : Safe cpt := by
    have hzero := hwindow 0 hk
    simpa only [runFrom_zero] using hzero

  have hcptRange : cpt < 101 := by
    unfold Safe at hcptSafe
    omega

  unfold stepCheckB at hcheck

  have hall :=
    List.all_eq_true.mp hcheck

  have hcurrent :=
    hall cpt (by simpa using hcptRange)

  have hwindowB :
      windowSafeB k cpt = true :=
    windowSafeB_sound hwindow

  simp [hwindowB] at hcurrent

  exact (safeB_correct _).mp hcurrent

/-! ## Automatically discovered k-inductive proof -/

theorem cpt_in_range (n : Nat) :
    runFrom next initial n ≤ 100 := by
  have hkPositive : 0 < discoveredK := by
    native_decide

  have hkPasses :
      kInductionCheckB discoveredK = true := by
    native_decide

  have hchecks :
      baseCheckB discoveredK = true ∧
      stepCheckB discoveredK = true := by
    simpa [kInductionCheckB] using hkPasses

  have hbase :
      Base next initial Safe discoveredK :=
    baseCheckB_sound hchecks.1

  have hstep :
      Step next Safe discoveredK :=
    stepCheckB_sound hkPositive hchecks.2

  have hsafe :
      Safe (runFrom next initial n) :=
    KInduction.sound
      next
      initial
      Safe
      (k := discoveredK)
      hbase
      hstep
      n

  exact hsafe

end KInductiveCounter
