import PolyContracts.Component.Method
import PolyContracts.Component.Job

namespace PolyContracts

/-! **## Behaviours** -/

/--
A behaviour is either a method or a job.

This type provides a common domain for notions defined uniformly
over methods and jobs, such as their attribute and local-variable
update sets.

The type itself does not impose a visibility restriction on methods.
The restriction to public methods will be expressed when defining
the component-level behaviour set.
-/
inductive Behaviour where
  | method (a : Method)
  | job (j : Job)
  deriving Repr, DecidableEq


namespace Behaviour

/-! **## Update sets** -/

/--
The set `f` of attributes updated by behaviour `b`.

For a method behaviour, this is the attribute update set of the
underlying method. For a job behaviour, it is the attribute update
set of the underlying job.
-/
def f (b : Behaviour) : Set Variable :=
  match b with
  | .method a => a.f
  | .job j => j.f


/--
The set `v` of local variables updated by behaviour `b`.

For a method behaviour, this is the local-variable update set of
the underlying method. For a job behaviour, it is the local-variable
update set of the underlying job.
-/
def v (b : Behaviour) : Set Variable :=
  match b with
  | .method a => a.v
  | .job j => j.v

end Behaviour


/-! **## Sanity checks** -/

#check Behaviour

#check fun (b : Behaviour) => b.f
#check fun (b : Behaviour) => b.v
#check fun (a : Method) => (Behaviour.method a).f
#check fun (a : Method) => (Behaviour.method a).v
#check fun (j : Job) => (Behaviour.job j).f
#check fun (j : Job) => (Behaviour.job j).v

end PolyContracts
