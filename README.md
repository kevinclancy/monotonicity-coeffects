λMC Prototype

The λMC prototype has one prerequisite: the Dotnet Core runtime 2.0, which is available for Windows, Mac, and Linux.
Once Dotnet Core has been installed, cd to the MonotonicityCoeffects subdirectory and type "dotnet run InteractiveShell.tb".
Make sure your computer is connected to the internet, as some dotnet packages will be installed upon the first execution
of the λMC prototype.

Kinding/formation rules
------------------------

Upon running "dotnet run InteractiveShell.tb", you will be presented with a prompt. Typing "help" gives a list of commands.
We begin by testing out the checkSemilat command, which decides the judgment τ ↩ τ₀ :: Δ, treating τ as an
input position and τ₀ as an output position.

> checkSemilat Nat
Semilattice formation check succeeded:
 Nat is a semilattice type with delta type Nat

As discussed in the paper, the primitive type Nat, of natural numbers, is a semilattice type whose delta type is Nat.

> checkSemilat Bool

Semilattice formation check succeeded:
 Bool is a semilattice type with delta type Unit

> checkSemilat Unit
checkSemilat Unit
line: 1 column: 1
  Type Unit is not a semilattice

Unit could be considered a semilattice type (with delta type 0 - the initial poset);
however, the point of a semilattice variable is to passively accumulate information.
Since Unit values contain no information, this probably wouldn't be useful.

We can also decide the judgment form τ :: ❉, which identifies τ as a toset type.

> checkToset Unit
``
Toset formation check succeeded:
 Unit is a toset type
``

Furthermore, we can decide the judgment form τ :: ⋆, which identifies τ as a poset type.

> checkPoset Unit
``
Poset formation check succeeded:
 Unit is a poset type
``

Let's try a compound type, using the |> type constructor for dictionary types. 

> checkPoset Nat |> Unit
``
line: 1 column: 1
  Type (Nat |> Unit) is not a poset: codomain is not a semilattice

line: 1 column: 8
  Type Unit is not a semilattice
``

Any well-formed λMC program has the form:

types 
  typdefs
in
  expr

InteractiveShell.tb places a hole (##) in the expr position, which triggers the interactive shell with
all defined types in scope.

``
Set = typefun (x : TOSET) x |> Bool end;
``

The first line defines a type operator: given any toset type T,
Set T is equal to the dictionary type T |> Bool, which intuitively 
corresponds to finite sets of element-type T.

The final definition contains a type constructor that we have not yet seen.
``
Cart = | Checkout | * (Set (ActionId * Action));
``

If T is a toset type, then | T | is the type of IVars with contents of type T.
Since all ivar types and dictionary types are semilattice types, we expect Cart to 
be a semilattice type as well.

> checkSemilat Cart
``
Semilattice formation check succeeded:
 Cart is a semilattice type with delta type ((? Checkout) + ((? (Nat * (Nat + Nat))) * Unit))
``


Type Syntax
-----------

Since we're using text source-code, the notation does not match the paper exactly.
We list the types supported by the prototype:
τ,σ,ι ::= 
 Unit - Unit type
 Bool - Booleans
 Nat - Natural Numbers 
 | τ | - IVar of content type τ
 τ * τ - Product
 τ + τ - Sum
 τ |> τ - Dictionary
 [ τ ] - Monotonically partial computations of result type T
 (τ τ ...) - Type application
 (typefun (x : K) τ) - Type function definition

K ::= SEMILATTICE | TOSET | POSET

Expression syntax
-----------------

Full syntax is given in Parser.fsy. As a general rule, applications need to be parenthesized,
so if the parser produces an error at an application, try parenthesizing the application.

Introduction forms
==================

λMC provides literals for natural numbers (0,1,2,...), booleans (true, false), and unit (unit).

A pair containing the values of e₁ and e₂ in the left and right components is written (e₁ , e₂).

A left injection into a sum type (τ + σ) is written inl τ σ e. Likewise, a right injection
is written inr τ σ e.

An ivar containing the value produced by e is written | e |.

We provide syntactic sugar for constructing dictionaries:
``
{ k₁ -> v₁ ... kₙ -> vₙ : σ }
``

is sugar for
``
(k₁ ↦ v₁) :: … :: (kₙ ↦ vₙ) :: ⊥σ
``

The unit for monotone partiality is written [e], producing a result containing e's value.

Bindings and Eliminators
========================

MonotoneCart.tb provides a good demonstration of expression syntax.

Let bindings are standard:

``
let x = e in e end
``

To chain multiple let bindings together, we provide "and notation"

``
let x = e₁
and y = e₂
and z = e₃
in e
end
``

We provide modified let bindings for IVar and dictionary elimination

For ivars, we have:

``
let | x | = e₁ in e₂ end
``

If e₁ has type |τ| and e₂ has semilattice type σ, this expression has
type [σ]. If e₁ evaluates to an empty ivar, the expression evaluates to [⊥σ], 
a monotonically partial result whose value is the bottom element of semilattice σ. 
If e₁ evaluates to a singleton { p }, then the expression evaluates to [ [p/x]e₂ ]. 
Otherwise, it evaluates to ⊤σ; i.e. the "undefined" value.

For dictionaries, we have:

``
let extract to σ with xk xv xacc = e₁ in e₂ end
``

If e₁ has a dictionary type τ |> ι and e₂ has a semilattice type σ then
this expression has type σ. It starts at the entry (k_n, v_n) of greatest key,
and, writing ⊔σ for σ's join operator, it evaluates 
w(n) = [k_n/xk][v_n/xv][⊥σ/xacc]e₂
w(n-1) = [k_{n-1}/xk][v_{n-1}/xv][w(n)/xacc]e₂ ⊔σ w(n) 
w(n-2) = [k_{n-2}/xk][v_{n-2}/xv][w(n-1)/xacc]e₂ ⊔σ w(n-1)
...
w(1) = [k_{1}/xk][v_{1}/xv][w(2)/xacc]e₂ ⊔σ w(2)

The value of w(1) is the value produced by the elimination form.

The binding form for monadic partiality appears as:
``
let [ x ] <- e₁ in e₂ end
``

If e₁ has type [τ] and e₂ has type [σ], the eliminator evaluates e₁
to a result. If the result is undefined, the eliminator produces an undefined result.
Otherwise, e₁ produces a result v of type σ; the value of the eliminator
is then the value of [v/x]e₂.

The binding form for monotone partiality cannot be mixed with other forms 
of partiality due to its status as a monadic binder. However, it can be
chained using "and notation", as seen in MonotoneCart.tb.

The eliminators for sums and products are standard. For products,
we use ``fst e`` to project the first component of e's value and
``snd e`` to project the second component of e's value.

A sum eliminator has the form 
``
case e to τ of 
inl x -> e₁
inr x -> e₂
``

Abstractions and applications
=============================

A term-level abstraction is written as follows:
``
fun (x₁ : τ₁ | K₁) … (xₙ : τₙ | Kₙ) e end
``
Here each argument can be either a value or a type, depending on whether it is 
ascribed with a type or a kind.

An application is written 
``
(e₁ e₂ … eₙ)
``
Where e₁ is a function and e₂ … eₙ are arguments. Any type arguments are prefixed with a !.

A central characteristic of λMC is the ability to define homomorphisms, through the use of 
homomorphism abstractions. A homomorphism abstraction appears as
``
hom (x : τ . τ₀) e
``
Here τ is a semilattice type and τ₀ is its delta type. The variable x is bound to
type τ₀ in e, and we require that it is used monotonically in e. The hom abstraction
then evaluates to the adjoint complement (along the free/forgetful adjunction between Posets and Semilats) 
of e  as a monotone function of x, which is a semilattice homomorphism of domain τ.

Examples
--------

The examples from section 2 have been implemented in various .tb files.

Equality on toset types -
Implemented in Datafun.tb as the "equal" function.

Monotone if -
Implemented in Datafun.tb as the "monoIf" function.

Dictionary lookup -
Implemented in Datafun.tb as the "lookup" function.

Set cardinality -
Implemented in MonotoneCart.tb as the "setCount" function.

Multirelation composition -
Implemented in Datafun.tb as the "comp" function.

Bloomᴸ monotone shopping cart -
Implemented in MonotoneCart.tb as the "isComplete" function (and Cart type definition).

LVars neighbors homomorphism -
Implemented in lvars.tb as the "neighbors" function.















 
