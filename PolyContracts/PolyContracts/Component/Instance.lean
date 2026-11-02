import PolyContracts.Component.Context

namespace PolyContracts

/-! **## Component instances** -/

/--
A component instance is an active run-time software entity
associated with a component definition.
-/
structure ComponentInstance where
  name : String
  component : Component


/--
`InstanceOf c M` states that the run-time instance `c`
has component definition `M`.
-/
def InstanceOf
    (c : ComponentInstance)
    (M : Component) : Prop :=
  c.component = M


/-! **## Instance notation** -/

namespace InstanceNotation

/--
Notation corresponding to the mathematical instance relation
`c :: M`.
-/
scoped infix:50 " :: " => InstanceOf

end InstanceNotation

open scoped InstanceNotation


/-! **## Reference resolution** -/

/--
The reference semantics determines the run-time component instance,
if any, denoted by a component reference.
-/
class ReferenceSemantics where
  resolve : Reference → Option ComponentInstance


/--
`ResolvesTo r c` states that component reference `r`
denotes the run-time component instance `c`.
-/
def ResolvesTo
    [ReferenceSemantics]
    (r : Reference)
    (c : ComponentInstance) : Prop :=
  ReferenceSemantics.resolve r = some c


/--
`Unresolved r` states that component reference `r`
does not denote any run-time component instance.
-/
def Unresolved
    [ReferenceSemantics]
    (r : Reference) : Prop :=
  ReferenceSemantics.resolve r = none


/-! **## Reference-resolution notation** -/

namespace ResolutionNotation

/--
`r ▷ c` denotes that reference `r` resolves to
run-time component instance `c`.
-/
scoped infix:60 " ▷ " => ResolvesTo


/--
`r ▷⊥` denotes that reference `r` is unresolved.
-/
scoped postfix:60 " ▷⊥" => Unresolved

end ResolutionNotation

open scoped ResolutionNotation


/-! **## Component-reference targets** -/

/--
`RefersToComponent r M` states that reference `r`
denotes an instance of component definition `M`.
-/
def RefersToComponent
    [ReferenceSemantics]
    (r : Reference)
    (M : Component) : Prop :=
  ∃ c : ComponentInstance,
    (r ▷ c) ∧
    (c :: M)


/-! **## Reference notation** -/

namespace ReferenceNotation

/--
`r ▶ M` denotes that reference `r` refers to an instance
of component definition `M`.
-/
scoped infix:60 " ▶ " => RefersToComponent

end ReferenceNotation

open scoped ReferenceNotation


/-! **## Component reference properties** -/

namespace Component

/--
A component is self-referencing when one of its component
references designates an instance of the component itself.
-/
def SelfReferencing
    [ReferenceSemantics]
    (M : Component) : Prop :=
  ∃ r : Reference,
    r ∈ M.E ∧
    RefersToComponent r M


/--
The references of component `M` are well formed with respect to
context `𝕄` when every referenced component definition belongs
to `𝕄` and exposes at least one public service or public command.
-/
def ReferencesWellFormed
    [ReferenceSemantics]
    (M : Component)
    (𝕄 : Context) : Prop :=
  ∀ r ∈ M.E,
    ∀ N : Component,
      RefersToComponent r N →
        N ∈ 𝕄 ∧
        (N.Pˢ⁺ ∪ N.Pᵈ⁺) ≠ ∅

end Component


/-! **## Sanity checks** -/

-- A run-time component instance is an instance of
-- a component definition.
#check fun
    (c : ComponentInstance)
    (M : Component) =>
  c :: M


-- A reference may resolve to a run-time component instance.
#check fun
    [ReferenceSemantics]
    (r : Reference)
    (c : ComponentInstance) =>
  r ▷ c


-- A reference may remain unresolved.
#check fun
    [ReferenceSemantics]
    (r : Reference) =>
  r ▷⊥


-- A reference may refer to an instance of component definition `M`
-- using the underlying predicate.
#check fun
    [ReferenceSemantics]
    (r : Reference)
    (M : Component) =>
  RefersToComponent r M


-- `r ▶ M` denotes that reference `r` refers to an instance
-- of component definition `M`.
#check fun
    [ReferenceSemantics]
    (r : Reference)
    (M : Component) =>
  r ▶ M


-- A component may be self-referencing.
#check fun
    [ReferenceSemantics]
    (M : Component) =>
  M.SelfReferencing


-- Component references may be checked for well-formedness
-- with respect to a context.
#check fun
    [ReferenceSemantics]
    (𝕄 : Context)
    (M : Component) =>
  M.ReferencesWellFormed 𝕄

end PolyContracts
