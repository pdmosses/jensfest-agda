\subsection{Agda Standard Library Notation}
\label{sec:semantic-definitions:standard-library}

The Agda definitions given below use the following modules from the standard library.%
\footnote{\url{https://agda.github.io/agda-stdlib/v2.0/}}
%
\begin{AgdaAlign}
\begin{code}
{-# OPTIONS --safe #-}
open import Data.Nat.Base      using ( ℕ; zero; suc; _≤_ )     -- natural numbers zero ≤ suc zero ≤ ...
open import Data.Maybe.Base    renaming (  Maybe to _+?;       -- A +? is disjoint union of A and {??}
                                           nothing to ??;      -- ?? represents absence of an A value
                                           maybe′ to [_,_]? )  -- [ f , x ]? is case analysis on A +?
open import Data.Product.Base  using (_×_; _,_; proj₁; proj₂)  -- A × B is Cartesian product, _,_ is pairing
open import Function           using (Inverse; _↔_; _∘_)       -- A ↔ B is isomorphism between A and B
\end{code}
%
For each instance argument \AgdaRef{\{\{ \}\}} with an isomorphism type \AgdaRef{A ↔ B},
the following declaration introduces overloaded inverse functions.
Such isomorphisms are usually left implicit in published semantic definitions,
but Agda requires them to be made explicit;
similarly for injections into separated sum domains.
%
\begin{code}
open Inverse {{ ... }}         using (to; from)                -- to : A → B; from : B → A
\end{code}


\subsection{Scott Domains}
\label{sec:semantic-definitions:scott-domains}

The parameters of the following module declare notation for Scott domains and the associated operations.
(For simplicity, the declarations are not universe-polymorphic.)
%
\begin{code}
module Inheritance.Definitions
    ( Domain  :  Set₁ )                                       -- Domain is a type of cpo
    ( ⟨_⟩     :  Domain → Set )                               -- ⟨ D ⟩ is the type of elements of D
    ( _⊑_     :  {D : Domain} → ⟨ D ⟩ → ⟨ D ⟩ → Set )         -- x ⊑ y is the partial order of D
    ( ⊥       :  {D : Domain} → ⟨ D ⟩ )                       -- ⊥ is the least element of D
    ( lub     :  {D : Domain} → (δ : ℕ → ⟨ D ⟩) → ⟨ D ⟩ )     -- least upper bound of chains δ
    ( fix     :  {D : Domain} → ( ⟨ D ⟩ → ⟨ D ⟩ ) → ⟨ D ⟩ )   -- fix f is the least fixed-point of f

    ( ?⊥      :  Domain )                                     -- ⊥ is the only element of ?⊥
    ( _+⊥_    :  Domain → Domain → Domain )                   -- D +⊥ E is the separated sum of D and E

    ( inl     :  {D E : Domain} → ⟨ D ⟩ → ⟨ D +⊥ E ⟩ )        -- inl injects elements of D into D +⊥ E
    ( inr     :  {D E : Domain} → ⟨ E ⟩ → ⟨ D +⊥ E ⟩ )        -- inr injects elements of E into D +⊥ E
    ( [_,_]⊥  :  {D E F : Domain} →                           -- [ f , g ]⊥ is case analysis on D +⊥ E
                   ( ⟨ D ⟩ → ⟨ F ⟩ ) → ( ⟨ E ⟩ → ⟨ F ⟩ ) → ⟨ D +⊥ E ⟩ → ⟨ F ⟩ )
\end{code}
%
Regarding the type of \AgdaRef{fix} declared above,
\emph{all} functions from \AgdaRef{⟨ D ⟩} to \AgdaRef{⟨ D ⟩}
are elements of the Agda function type \AgdaRef{⟨ D ⟩ → ⟨ D ⟩}.
The following type could be used to restrict arguments of \AgdaRef{fix} to continuous functions:
%
\begin{quote}
\AgdaRef{{D : Domain} → ( f : ⟨ D ⟩ → ⟨ D ⟩ ) → (is-continuous f) → ⟨ D ⟩}
\end{quote}
%
where \AgdaRef{is-continuous} checks the continuity of its argument.
The least fixed-point of \AgdaRef{f} would then need to be written \AgdaRef{fix f t}
with a proof term \AgdaRef{t : is-continuous f}.
In practice, however, \AgdaRef{fix} will be applied only to functions on \AgdaRef{⟨ D ⟩}
defined by lambda-abstraction and application, which ensures their continuity.
Omitting the proof-term argument of \AgdaRef{fix} does not affect
checking that the function to which it is applied is from some domain \AgdaRef{D} to itself.

\subsection{Method Systems}

The method systems defined in CP89 are a simple formalization of object-oriented programming.
They abstract from aspects such as instance variables, assignment, and object creation.
A method system corresponds to a snapshot in the execution of an object-oriented system.

In CP89, the ingredients of method systems are assumed to be elements of flat domains;
however, the least elements of these domains are irrelevant,
and it is simpler to declare them as ordinary Agda types instead of domains:
%
\begin{code}
    ( Instance   : Set )  -- objects
    ( Name       : Set )  -- class names
    ( Key        : Set )  -- method names
    ( Primitive  : Set )  -- function names
\end{code}
%
Both the operational and the denotational semantics of method systems in CP89 involve
the mutually-recursive domains \AgdaRef{Value}, \AgdaRef{Behavior}, and \AgdaRef{Fun}.
These domains cannot be defined (safely) as Agda types,
due to the termination check on recursive type definitions.
Scott domain theory ensures the existence of isomorphisms between the types of elements of these domains
when the elements of \AgdaRef{⟨ Value ⟩ → ⟨ Value ⟩} are restricted to continuous functions.
However, this restriction is irrelevant for checking the types of functions on domains,
so it is simply omitted.
%
\begin{code}
    ( Number    : Domain )       -- the domain of numbers is unconstrained
    ( Value     : Domain )       -- a value is (isomorphic to) a behavior or a number
    ( Behavior  : Domain )       -- a behaviour maps a method name to a fun, or to the only element of ?⊥
    ( Fun       : Domain )       -- a fun maps an argument value to a value (possibly ⊥)
    {{ isoᵛ     : ⟨ Value ⟩     ↔  ⟨ Behavior +⊥ Number ⟩     }}
    {{ isoᵇ     : ⟨ Behavior ⟩  ↔  ( Key → ⟨ Fun +⊥ ?⊥ ⟩ )    }}
    {{ isoᶠ     : ⟨ Fun ⟩       ↔  ( ⟨ Value ⟩ → ⟨ Value ⟩ )  }}
    ( apply⟦_⟧  : Primitive → ⟨ Value ⟩ → ⟨ Value ⟩ )
  where
variable ρ : Instance; m : Key; f : Primitive
variable ν : ⟨ Number ⟩; α : ⟨ Value ⟩; σ π : ⟨ Behavior ⟩; φ : ⟨ Fun ⟩
\end{code}
%
In the operational and denotational semantics of method systems in CP89,
elements $f$ of the flat domain \textbf{Primitive} are treated
as if they are elements of the function domain \textbf{Fun}.
When checking the corresponding part of the Agda formulation,
the Agda type checker reported this as an error.
The semantic function \AgdaRef{apply⟦ ⟧} declared above is assumed to map
elements of \AgdaRef{Primitive} to functions on \AgdaRef{⟨ Value ⟩},
and its use fixed the error.

In CP89, the inheritance hierarchy is assumed to be a finite tree.
Here, \AgdaRef{Class} is defined as the datatype of all finite trees.
This also avoids the need for the partial \textit{parent} function,
and for a predicate for testing whether a class is the root of the hierarchy.
%
\begin{code}
data Class : Set where
  child   : Name → Class → Class  -- a subclass
  origin  : Class                 -- the root class
variable κ : Class
\end{code}
%
The syntax of method expressions is defined by the inductive datatype \AgdaRef{Exp}:
%
\begin{code}
data Exp : Set where
  self   : Exp                    -- refers to the behavior of the current object
  super  : Exp                    -- refers to the behavior in the superclass of the object
  arg    : Exp                    -- denotes the single argument of the method expression
  call   : Exp → Key → Exp → Exp  -- "call e₁ m e₂" denotes calling method m of e₁ with argument e₂
  appl   : Primitive → Exp → Exp  -- "appl f e₁" denotes applying f to e₁
variable e : Exp
\end{code}
%
The parameters of the Semantics module are available in all the subsequent definitions:
%
\begin{code}
module Semantics
    ( class     : Instance → Class )         -- "class ρ" is the class of an object
    ( methods′  : Class → Key → (Exp +?) )   -- "methods′ κ m" is the method named m in κ
  where
  methods : Class → Key → (Exp +?)           -- "methods origin" overrides "methods′ origin"
  methods (child c κ) m  = methods′ (child c κ) m
  methods origin m       = ??
\end{code}

\subsection{Method Lookup Semantics}

The method lookup semantics uses mutually-recursive functions 
\AgdaRef{send}, \AgdaRef{lookup}, and \AgdaRef{do⟦ ⟧},
which can be non-terminating, 
They are therefore defined in Agda as the least fixed-point
of a non-recursive function \AgdaRef{g}
(as in the proof of Proposition~3 in CP89) on a domain \AgdaRef{Gᵍ}
that is isomorphic to~\AgdaRef{Dᵍ}:
%
\begin{code}
  Dᵍ =  ( Instance → ⟨ Behavior ⟩ ) ×
        ( Class → Instance → ⟨ Behavior ⟩ ) ×
        ( Exp → Instance → Class → ⟨ Fun ⟩ )

  module _
      { Gᵍ : Domain }
      {{ isoᵍ : ⟨ Gᵍ ⟩ ↔ Dᵍ }}
    where
    g : Dᵍ → Dᵍ
    g (s , l , d⟦_⟧) = (send , lookup , do⟦_⟧) where
\end{code}
%
The behavior of \AgdaRef{send ρ} is to use \AgdaRef{lookup} 
(to be supplied as the argument \AgdaRef{l} of \AgdaRef{g} above)
to obtain the behavior of \AgdaRef{ρ} using the class of \AgdaRef{ρ} itself:
%
\begin{code}
      send : Instance → ⟨ Behavior ⟩
      send ρ = l (class ρ) ρ
\end{code}
%
The behavior of \AgdaRef{lookup κ ρ} for a subclass \AgdaRef{κ} 
depends on whether it is called with a method \AgdaRef{m} defined by \AgdaRef{κ}:
if so, it uses \AgdaRef{do⟦ e ⟧} (via argument \AgdaRef{d⟦ ⟧} of \AgdaRef{g})
to execute the corresponding method expression;
if not, it recursively looks up \AgdaRef{m} in the superclass of {κ}.%
\footnote{The isomorphisms \AgdaRef{to} and \AgdaRef{from} and the injection \AgdaRef{inl} can be ignored.}
The behavior is undefined when \AgdaRef{κ} is the root of the inheritance hierarchy,
which has been defined to have no methods:
%
\begin{code}
      lookup : Class → Instance → ⟨ Behavior ⟩
      lookup (child c κ) ρ  = from λ m →  [  ( λ e → inl (d⟦ e ⟧ ρ (child c κ)) ) ,
                                             ( to (l κ ρ) m )
                                          ]? (methods (child c κ) m)
      lookup origin ρ       = ⊥
\end{code}
%
When applied to a value \AgdaRef{α}, the value returned by the function \AgdaRef{to (do⟦ e ⟧ ρ κ)} may be
a behavior, a number, or undefined (\AgdaRef{⊥}):
%
\begin{code}
      do⟦_⟧ : Exp → Instance → Class → ⟨ Fun ⟩
      do⟦ self          ⟧ ρ κ            = from λ α → from (inl (s ρ))
      do⟦ super         ⟧ ρ (child c κ)  = from λ α → from (inl (l κ ρ))
      do⟦ super         ⟧ ρ origin       = from λ α → ⊥
      do⟦ arg           ⟧ ρ κ            = from λ α → α
      do⟦ call e₁ m e₂  ⟧ ρ κ            = from λ α →
                                            [  ( λ σ →  [  ( λ φ →  to φ (to (d⟦ e₂ ⟧ ρ κ) α) ) ,
                                                           ( λ _ →  ⊥ )
                                                        ]⊥ (to σ m) ) ,
                                               ( λ ν →  ⊥ )
                                            ]⊥ (to (to (d⟦ e₁ ⟧ ρ κ) α))
      do⟦ appl f e₁     ⟧ ρ κ            = from λ α → apply⟦ f ⟧ (to (d⟦ e₁ ⟧ ρ κ) α)
\end{code}
%
The only complicated case is for calling method \AgdaRef{m} of object \AgdaRef{e₁} 
with argument \AgdaRef{e₂}.
When the value of \AgdaRef{e₁} is a behavior \AgdaRef{σ} that maps \AgdaRef{m} to a function \AgdaRef{φ},
that function is applied to the value of \AgdaRef{e₂};
otherwise the value of the call is undefined.
The undefined cases are not explicit in CP89.

The use of \AgdaRef{fix} below has the effect of making the above definitions mutually recursive:
%
\begin{code}
    γ : ⟨ Gᵍ ⟩ → ⟨ Gᵍ ⟩
    γ = from ∘ g ∘ to

    send     = proj₁ (to (fix γ))
    lookup   = proj₁ (proj₂ (to (fix γ)))
    do⟦_⟧    = proj₂ (proj₂ (to (fix γ)))
\end{code}
%
That completes the definition of the method lookup semantics.

\subsection{Denotational Semantics}

The denotational semantics of method expressions takes the behavior of the 
expressions \AgdaRef{self} (\AgdaRef{σ})
and \AgdaRef{super} (\AgdaRef{π}) as arguments, so their evaluation is trivial.
The evaluation of the other method expressions is similar to their method lookup semantics.
%
\begin{code}
  eval⟦_⟧ : Exp → ⟨ Behavior ⟩ → ⟨ Behavior ⟩ → ⟨ Fun ⟩
  eval⟦ self          ⟧ σ π  = from λ α → from (inl σ)
  eval⟦ super         ⟧ σ π  = from λ α → from (inl π )
  eval⟦ arg           ⟧ σ π  = from λ α → α
  eval⟦ call e₁ m e₂  ⟧ σ π  = from λ α →
                                [  ( λ σ′ →  [  ( λ φ →  to φ (to (eval⟦ e₂ ⟧ σ π) α) ) ,
                                                ( λ _ →  ⊥ )
                                             ]⊥ (to σ′ m) ) ,
                                   ( λ ν →   ⊥ )
                                ]⊥ (to (to (eval⟦ e₁ ⟧ σ π) α))
  eval⟦ appl f e₁     ⟧ σ π  = from λ α → apply⟦ f ⟧ (to (eval⟦ e₁ ⟧ σ π) α)
\end{code}
%
The recursively-defined function \AgdaRef{eval⟦ ⟧} is obviously total,
so there is no need for an explicit fixed point in its Agda definition.

According to the conceptual analysis of inheritance in CP89,
the behavior of an instance \AgdaRef{ρ} will be defined as the fixed point
of the generator associated with the class of \AgdaRef{ρ}.

The generator for a subclass is obtained by modifying the generator of its parent class
using a wrapper that provides the behavior of the methods defined by the subclass,
given the behavior of the expressions \AgdaRef{self} (\AgdaRef{σ})
and \AgdaRef{super} (\AgdaRef{π}) as arguments.

The auxiliary operation \AgdaRef{σ₁ ⊕ σ₂} combines its argument behaviors,
letting the methods of \AgdaRef{σ₁} shadow those of \AgdaRef{σ₂}.
The operation \AgdaRef{w ⍄ p} combines the wrapper of a subclass with the generator of its parent class.
See Figure~9 of CP89 for an illustration of wrapper application.
%
\begin{code}
  Generator = ⟨ Behavior ⟩ → ⟨ Behavior ⟩
  Wrapper   = ⟨ Behavior ⟩ → ⟨ Behavior ⟩ → ⟨ Behavior ⟩
  
  _⊕_ : ⟨ Behavior ⟩ → ⟨ Behavior ⟩ → ⟨ Behavior ⟩
  σ₁ ⊕ σ₂ = from λ m → [  ( λ φ → inl φ ) ,
                          ( λ _ → to σ₂ m ) 
                       ]⊥ (to σ₁ m)

  _⍄_ : Wrapper → Generator → Generator
  w ⍄ p = λ σ → (w σ (p σ)) ⊕ (p σ)

  wrap : Class → Wrapper
  wrap κ = λ σ → λ π → from λ m →  [  ( λ e →  inl (eval⟦ e ⟧ σ π) ) ,
                                      ( inr ⊥ )
                                   ]? (methods κ m)

  gen : Class → Generator
  gen (child c κ)  = wrap (child c κ) ⍄ gen κ
  gen origin       = λ σ → ⊥

  behave : Instance → ⟨ Behavior ⟩
  behave ρ = fix (gen (class ρ))
\end{code}
\end{AgdaAlign}
%
That concludes the Agda formulation of the denotational semantics defined in CP89.