import PolyContracts.Component.Method
import PolyContracts.Component.Behaviour
import PolyContracts.Component.Reference

namespace PolyContracts

/--
A component definition consists of a set of methods, a set of jobs,
a set of component references, and a requiring relation between
references and methods.
-/
structure Component where
  methods : Set Method
  jobs : Set Job
  references : Set Reference
  requiring : Set (Reference × Method)

namespace Component

/--
The set `R` of reference-method pairs requiring component `M`.
-/
def R (M : Component) : Set (Reference × Method) :=
  M.requiring

/--
The set `P` of methods belonging to component `M`.
-/
def P (M : Component) : Set Method :=
  M.methods

/--
Methods of `P` having visibility `v`.
-/
def P_supers_vis
    (P : Set Method)
    (v : Visibility) : Set Method :=
  {m | m ∈ P ∧ m.visibility = v}

/--
Methods of `P` having kind `k`.
-/
def P_supers_kind
    (P : Set Method)
    (k : MethodKind) : Set Method :=
  {m | m ∈ P ∧ m.kind = k}

/--
Methods of `P` having kind `k` and visibility `v`.
-/
def P_supers_kind_vis
    (P : Set Method)
    (k : MethodKind)
    (v : Visibility) : Set Method :=
  {m | m ∈ P ∧ m.kind = k ∧ m.visibility = v}

/--
A component is well formed when every data source and data well
belonging to the component is private.
-/
def WellFormed (M : Component) : Prop :=
  ∀ m ∈ M.P,
    (m.kind = MethodKind.source ∨
     m.kind = MethodKind.well) →
    m.visibility = Visibility.prv

/--
The set `E` of component references.
-/
def E (M : Component) : Set Reference :=
  M.references

/--
The set `J` of jobs belonging to component `M`.
-/
def J (M : Component) : Set Job :=
  M.jobs
end Component


/-! **## Visibility** -/

postfix:max "⁺" =>
  fun P : Set Method =>
    Component.P_supers_vis P Visibility.pbl

postfix:max "⁻" =>
  fun P : Set Method =>
    Component.P_supers_vis P Visibility.prv


/-! **## Method kinds** -/

postfix:max "ˢ" =>
  fun P : Set Method =>
    Component.P_supers_kind P MethodKind.service

postfix:max "ᵈ" =>
  fun P : Set Method =>
    Component.P_supers_kind P MethodKind.command

postfix:max "ᵒ" =>
  fun P : Set Method =>
    Component.P_supers_kind P MethodKind.source

postfix:max "ʷ" =>
  fun P : Set Method =>
    Component.P_supers_kind P MethodKind.well


/-! **## Kind × visibility** -/

postfix:max "ˢ⁺" =>
  fun P : Set Method =>
    Component.P_supers_kind_vis
      P MethodKind.service Visibility.pbl

postfix:max "ˢ⁻" =>
  fun P : Set Method =>
    Component.P_supers_kind_vis
      P MethodKind.service Visibility.prv

postfix:max "ᵈ⁺" =>
  fun P : Set Method =>
    Component.P_supers_kind_vis
      P MethodKind.command Visibility.pbl

postfix:max "ᵈ⁻" =>
  fun P : Set Method =>
    Component.P_supers_kind_vis
      P MethodKind.command Visibility.prv

postfix:max "ᵒ⁺" =>
  fun P : Set Method =>
    Component.P_supers_kind_vis
      P MethodKind.source Visibility.pbl

postfix:max "ᵒ⁻" =>
  fun P : Set Method =>
    Component.P_supers_kind_vis
      P MethodKind.source Visibility.prv

postfix:max "ʷ⁺" =>
  fun P : Set Method =>
    Component.P_supers_kind_vis
      P MethodKind.well Visibility.pbl

postfix:max "ʷ⁻" =>
  fun P : Set Method =>
    Component.P_supers_kind_vis
      P MethodKind.well Visibility.prv


namespace Component

/-! **## Behaviour domain** -/

/--
The behaviour domain of component `M` consists exactly of its
public methods and its jobs.

A public method is represented by `Behaviour.method`, while a job
is represented by `Behaviour.job`. This provides the Lean
counterpart of the mathematical domain `P⁺ ∪ J`.
-/
def BehaviourDomain
    (M : Component) : Set Behaviour :=
  {b |
    (∃ a : Method,
      a ∈ M.P⁺ ∧
      b = Behaviour.method a) ∨
    (∃ j : Job,
      j ∈ M.J ∧
      b = Behaviour.job j)}

end Component

/-! **## Sanity checks** -/

#check Component

#check fun (M : Component) => M.R
#check fun (M : Component) => M.P
#check fun (M : Component) => M.P⁺
#check fun (M : Component) => M.P⁻
#check fun (M : Component) => M.Pˢ
#check fun (M : Component) => M.Pᵈ
#check fun (M : Component) => M.Pᵒ
#check fun (M : Component) => M.Pʷ
#check fun (M : Component) => M.Pˢ⁺
#check fun (M : Component) => M.Pˢ⁻
#check fun (M : Component) => M.Pᵈ⁺
#check fun (M : Component) => M.Pᵈ⁻
#check fun (M : Component) => M.Pᵒ⁺
#check fun (M : Component) => M.Pᵒ⁻
#check fun (M : Component) => M.Pʷ⁺
#check fun (M : Component) => M.Pʷ⁻
#check fun (M : Component) => M.E
#check fun (M : Component) => M.Eˡ
#check fun (M : Component) => M.Eʳ
#check fun (M : Component) => M.BehaviourDomain

#check fun
    (M : Component)
    (b : Behaviour) =>
  b ∈ M.BehaviourDomain
end PolyContracts
