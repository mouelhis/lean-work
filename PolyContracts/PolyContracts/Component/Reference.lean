import PolyContracts.Basic

namespace PolyContracts

/--
A reference to a component instance in the environment.

A reference has a name and a location indicating whether
the referenced component is local or remote.
-/
structure Reference where
  name : String
  location : ReferenceLocation
  deriving Repr, DecidableEq


namespace Reference

/--
References of `E` having location `l`.
-/
def E_supers_loc
    (E : Set Reference)
    (l : ReferenceLocation) : Set Reference :=
  {r | r ∈ E ∧ r.location = l}

end Reference


/-! **## Reference locations** -/

/--
Local component references.
-/
postfix:max "ˡ" =>
  fun E : Set Reference =>
    Reference.E_supers_loc E ReferenceLocation.local

/--
Remote component references.
-/
postfix:max "ʳ" =>
  fun E : Set Reference =>
    Reference.E_supers_loc E ReferenceLocation.remote


/-! **## Sanity checks** -/

#check Reference

#check fun (E : Set Reference) => Eˡ
#check fun (E : Set Reference) => Eʳ

end PolyContracts
