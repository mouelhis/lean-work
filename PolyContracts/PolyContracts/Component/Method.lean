import PolyContracts.Basic

namespace PolyContracts

/--
A value type associated with a variable.

`noType` represents `⊥`, the type of no value.
-/
inductive ValueType where
  | named (name : String)
  | noType
  deriving Repr, DecidableEq

/--
A typed variable from the universe `X`.

Each variable has a name and an associated type `T[x]`.
-/
structure Variable where
  name : String
  type : ValueType
  deriving Repr, DecidableEq

/--
Access mode of a method parameter.

A parameter is either:
- input: read-only,
- output: write-only, or
- inout: readable and modifiable.
-/
inductive ParameterMode where
  | input
  | output
  | inout
  deriving Repr, DecidableEq

/--
A method parameter is a typed variable together with its
access mode.
-/
structure Parameter where
  var : Variable
  mode : ParameterMode
  deriving Repr, DecidableEq

/--
An exception that may be raised by a method.
-/
structure Exception where
  name : String
  deriving Repr, DecidableEq

/--
A method definition.

A method has a name, a kind, a visibility, an ordered list of
parameters, an optional return variable, and a list of exceptions
that it may raise.
-/
structure Method where
  name : String
  kind : MethodKind
  visibility : Visibility
  parameters : List Parameter
  result : Option Variable
  exceptions : List Exception
  attributes : List Variable
  locals : List Variable
  deriving Repr, DecidableEq

/--
The signature of a method.

A method signature records the method name, ordered parameters,
optional return variable, and declared exceptions. Method kind
and visibility are properties of the method definition and are
not part of its signature.
-/
structure MethodSignature where
  name : String
  parameters : List Parameter
  result : Option Variable
  exceptions : List Exception
  deriving Repr, DecidableEq

namespace Method

/--
The set `p` of parameters of method `a`.
-/
def p (a : Method) : Set Parameter :=
  {p | p ∈ a.parameters}

/--
The set `i` of input (read-only) parameters of method `a`.
-/
def i (a : Method) : Set Parameter :=
  {p | p ∈ a.p ∧ p.mode = ParameterMode.input}

/--
The set `o` of output (write-only) parameters of method `a`.
-/
def o (a : Method) : Set Parameter :=
  {p | p ∈ a.p ∧ p.mode = ParameterMode.output}

/--
The set `io` of inout (readable and modifiable) parameters
of method `a`.
-/
def io (a : Method) : Set Parameter :=
  {p | p ∈ a.p ∧ p.mode = ParameterMode.inout}

/--
The return parameter `r` of method `a`.

`some r` represents a method returning `r`, while `none`
represents a void method.
-/
def r (a : Method) : Option Variable :=
  a.result

/--
The return type of method `a`.

If `a` returns a variable `r`, its return type is `T[r]`.
Otherwise the return type is `⊥`.
-/
def returnType (a : Method) : ValueType :=
  match a.result with
  | some r => r.type
  | none => ValueType.noType

/--
The set `e` of exceptions that may be raised by method `a`.
-/
def e (a : Method) : Set Exception :=
  {e | e ∈ a.exceptions}

/--
The set `f` of attributes updated by method `a`.
-/
def f (a : Method) : Set Variable :=
  {x | x ∈ a.attributes}


/--
The set `v` of local variables updated by method `a`.
-/
def v (a : Method) : Set Variable :=
  {x | x ∈ a.locals}

/--
The signature of method `a`.
-/
def signature
    (a : Method) : MethodSignature where
  name := a.name
  parameters := a.parameters
  result := a.result
  exceptions := a.exceptions


end Method

/-! ## Sanity checks -/

#check fun (a : Method) => a.p
#check fun (a : Method) => a.i
#check fun (a : Method) => a.o
#check fun (a : Method) => a.io
#check fun (a : Method) => a.r
#check fun (a : Method) => a.returnType
#check fun (a : Method) => a.e
#check fun (a : Method) => a.f
#check fun (a : Method) => a.v
#check fun (a : Method) => a.signature

end PolyContracts
