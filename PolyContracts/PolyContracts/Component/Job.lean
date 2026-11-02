import PolyContracts.Component.Method

namespace PolyContracts

/--
A job is an internal computation identified by a name and an
ordered list of typed input parameters.

A job has only input parameters; unlike a method, it has no
output or inout parameter modes.
-/
structure Job where
  name : String
  inputs : List Variable
  attributes : List Variable
  locals : List Variable
  deriving Repr, DecidableEq

/--
The signature of a job consists of its name and ordered
input parameters.
-/
structure JobSignature where
  name : String
  inputs : List Variable
  deriving Repr, DecidableEq

namespace Job

/--
The set `i` of input parameters of job `j`.
-/
def i (j : Job) : Set Variable :=
  {x | x ∈ j.inputs}

/--
The set `f` of attributes updated by job `j`.
-/
def f (j : Job) : Set Variable :=
  {x | x ∈ j.attributes}

/--
The set `v` of local variables updated by job `j`.
-/
def v (j : Job) : Set Variable :=
  {x | x ∈ j.locals}

/--
The signature of job `j`.
-/
def signature (j : Job) : JobSignature where
  name := j.name
  inputs := j.inputs

end Job


/-! **## Sanity checks** -/

#check Job

#check fun (j : Job) => j.i
#check fun (j : Job) => j.f
#check fun (j : Job) => j.v
#check fun (j : Job) => j.signature

end PolyContracts
