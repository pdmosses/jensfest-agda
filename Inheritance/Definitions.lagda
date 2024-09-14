\subsection{Agda Standard Library Notation}
\label{sec:semantic-definitions:standard-library}

The Agda definitions given below use the following modules from the standard library (v2.1).%
\footnote{\url{https://agda.github.io/agda-stdlib/v2.1/}}
%
\begin{AgdaAlign}
\begin{code}
{-# OPTIONS --safe #-}            -- Agda        ~ CP89 notation
open import Data.Nat.Base
  using ( ℕ; zero; suc; _≤_ )     -- ℕ             ~ Nat
open import Data.Maybe.Base
  renaming ( Maybe to _+?;        -- A +?         ~ A + ?
             nothing to ??;       -- ??             ~ ⊥?
             maybe′ to [_,_]? )   -- [ f , x ]?    ~ [f, λ⊥?.x]
open import Data.Product.Base
  using (_×_; _,_; proj₁; proj₂)  -- A × B        ~ A × B
open import Function
  using (Inverse; _↔_; _∘_)       -- A ↔ B      ~ implicit
open Inverse {{ ... }}
  using (to; from)                -- to from     ~ implicit
\end{code}
%
The declaration \AgdaCode[\AgdaKeyword{open}\AgdaSpace{}%
\AgdaModule{Inverse}\AgdaSpace{}%
\AgdaSymbol{\{\{}\AgdaSpace{}%
\AgdaSymbol{...}\AgdaSpace{}%
\AgdaSymbol{\}\}}]
{open Inverse \{\{ ... \}\}} above introduces overloaded functions
\AgdaCode[\AgdaField{to}]
{to} and \AgdaCode[\AgdaField{from}]
{from} for each parameter of the form \AgdaCode[\AgdaSymbol{\{\{}\AgdaSpace{}%
\AgdaBound{i}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{A}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{↔}}\AgdaSpace{}%
\AgdaBound{B}\AgdaSpace{}%
\AgdaSymbol{\}\}}]
{\{\{ i : A ↔ B \}\}}.
The double braces specify so-called instance parameters,
which are the Agda equivalent of Haskell type class constraints.
%(Such isomorphisms are usually left implicit in published semantic definitions.)

\subsection{Domains}

The types and functions declared below as module parameters
correspond to assumptions about various features of Scott domains.
They are used when defining the semantics of method systems in Agda.

An element \AgdaCode[\AgdaBound{D}\AgdaSpace{}%
\AgdaSymbol{:}\AgdaSpace{}%
\AgdaBound{Domain}]
{D : Domain} is an Agda type corresponding to a domain used in CP89.
Such a type \AgdaCode[\AgdaBound{D}]
{D} has a type of elements \AgdaCode[\AgdaOperator{\AgdaBound{⟨}}\AgdaSpace{}%
\AgdaBound{D}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{⟩}}]
{⟨ D ⟩}
and a distinguished element \AgdaCode[\AgdaBound{⊥}]
{⊥}.
Further assumptions about domains
will be made in Section~\ref{sec:equivalence}, when proving results that
involve the partial order on \AgdaCode[\AgdaOperator{\AgdaBound{⟨}}\AgdaSpace{}%
\AgdaBound{D}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{⟩}}]
{⟨ D ⟩}.
%
\begin{code}
module Inheritance.Definitions
    ( Domain  :  Set₁ )                                     
    ( ⟨_⟩     :  Domain → Set )                             
    ( ⊥       :  {D : Domain} → ⟨ D ⟩ )                     
    ( fix     :  {D : Domain} → ( ⟨ D ⟩ → ⟨ D ⟩ ) → ⟨ D ⟩ ) 
\end{code}
%
The function \AgdaCode[\AgdaBound{fix}]
{fix} is supposed to correspond to the least fixed point operator
on the space of continuous functions on a domain.
To ensure that \AgdaCode[\AgdaBound{fix}]
{fix} can be applied only to continuous functions,
it would need to take a proof of continuity as an extra argument.

In practice, however, we intend to apply \AgdaCode[\AgdaBound{fix}]
{fix} only to functions on \AgdaCode[\AgdaOperator{\AgdaBound{⟨}}\AgdaSpace{}%
\AgdaBound{D}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{⟩}}]
{⟨ D ⟩}
that are defined by lambda-abstraction and application, 
and these are \emph{assumed} to correspond to continuous functions on domains.
It is superfluous to pass an \emph{assumption} of continuity as an explicit argument
– the same assumption can be made wherever it is needed
– so we simply omit the extra argument from the type of \AgdaCode[\AgdaBound{fix}]
{fix}.

\clearpage
\begin{code}
    ( ?⊥      :  Domain )                             
    ( _+⊥_    :  Domain → Domain → Domain )           
    ( inl     :  {D E : Domain} → ⟨ D ⟩ → ⟨ D +⊥ E ⟩ )
    ( inr     :  {D E : Domain} → ⟨ E ⟩ → ⟨ D +⊥ E ⟩ )
    ( [_,_]⊥  :  {D E F : Domain} →                   
                   ( ⟨ D ⟩ → ⟨ F ⟩ ) → ( ⟨ E ⟩ → ⟨ F ⟩ ) →
                   ⟨ D +⊥ E ⟩ → ⟨ F ⟩ )
\end{code}
%
\AgdaCode[\AgdaBound{?⊥}]
{?⊥} here corresponds to the 1-point domain written `$?$' in CP89;
its only element is \AgdaCode[\AgdaBound{⊥}]
{⊥} ($⊥_?$ in CP89).
\AgdaCode[\AgdaBound{D}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{+⊥}}\AgdaSpace{}%
\AgdaBound{E}]
{D +⊥ E} corresponds to the notation $D + E$ for separated sums of domains in CP89.
The injection functions \AgdaCode[\AgdaBound{inl}]
{inl} and \AgdaCode[\AgdaBound{inr}]
{inr} are left implicit in CP89.
(Case analysis \AgdaCode[\AgdaOperator{\AgdaFunction{[}}\AgdaSpace{}%
\AgdaBound{f}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{,}}\AgdaSpace{}%
\AgdaBound{g}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{]⊥}}]
{[ f , g ]⊥} on \AgdaCode[\AgdaBound{D}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{+⊥}}\AgdaSpace{}%
\AgdaBound{E}]
{D +⊥ E} is decorated with $⊥$ to avoid confusion with
the case analysis for ordinary disjoint union of Agda types.)

The Cartesian products of types provided by the standard Agda library support products of domains,
regarding a pair \AgdaCode[\AgdaSymbol{(}\AgdaBound{⊥}\AgdaSpace{}%
\AgdaOperator{\AgdaInductiveConstructor{,}}\AgdaSpace{}%
\AgdaBound{⊥}\AgdaSymbol{)}]
{(⊥ , ⊥)} as the least element of the product of two domains.  

\subsection{Method Systems}

The method systems defined in CP89 are a simple formalization of object-oriented programming.
They abstract from aspects such as instance variables, assignment, and object creation.
A method system corresponds to a snapshot in the execution of an object-oriented system.

In CP89, the ingredients of method systems are assumed to be elements of flat domains;
however, the least elements of these domains are irrelevant,
and it is simpler to declare them as ordinary Agda types instead of domains:
%
\begin{code}
    ( Instance   : Set )        -- objects
    ( Name       : Set )        -- class names
    ( Key        : Set )        -- method names
    ( Primitive  : Set )        -- function names
\end{code}
%
Both the operational and denotational semantics of method systems in CP89 involve
the mutually-recursive domains \AgdaCode[\AgdaBound{Value}]
{Value}, \AgdaCode[\AgdaBound{Behavior}]
{Behavior}, and \AgdaCode[\AgdaBound{Fun}]
{Fun}:
%
\begin{code}
    ( Number    : Domain )      -- unspecified
    ( Value     : Domain )      -- a value is a behavior or a number
    ( Behavior  : Domain )      -- a behavior maps keys to funs
    ( Fun       : Domain )      -- a fun maps values to values
\end{code}
%
These domains cannot be defined (safely) as Agda types,
due to the termination check on recursive type definitions.
Scott domain theory ensures the existence of isomorphisms between the types of elements of these domains
when the elements of \AgdaCode[\AgdaOperator{\AgdaBound{⟨}}\AgdaSpace{}%
\AgdaBound{Value}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{⟩}}\AgdaSpace{}%
\AgdaSymbol{→}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{⟨}}\AgdaSpace{}%
\AgdaBound{Value}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{⟩}}]
{⟨ Value ⟩ → ⟨ Value ⟩} are restricted to continuous functions.
However, this restriction is irrelevant for checking the types of functions on domains,
so it is omitted.
%
\begin{code}
    {{ isoᵛ     : ⟨ Value ⟩     ↔  ⟨ Behavior +⊥ Number ⟩     }}
    {{ isoᵇ     : ⟨ Behavior ⟩  ↔  ( Key → ⟨ Fun +⊥ ?⊥ ⟩ )    }}
    {{ isoᶠ     : ⟨ Fun ⟩       ↔  ( ⟨ Value ⟩ → ⟨ Value ⟩ )  }}
    ( apply⟦_⟧  : Primitive → ⟨ Value ⟩ → ⟨ Value ⟩ )
  where
variable ρ : Instance; m : Key; f : Primitive; ν : ⟨ Number ⟩
variable α : ⟨ Value ⟩; σ π : ⟨ Behavior ⟩; φ : ⟨ Fun ⟩
\end{code}
%
In the operational and denotational semantics of method systems in CP89,
elements $f$ of the flat domain \textbf{Primitive} are treated
as if they are elements of the function domain \textbf{Fun}.
When checking the corresponding part of the Agda formulation,
the Agda type checker reported this as an error.
The semantic function \AgdaCode[\AgdaOperator{\AgdaBound{apply⟦\AgdaUnderscore{}⟧}}]
{apply⟦ ⟧} declared above is assumed to map
elements of \AgdaCode[\AgdaBound{Primitive}]
{Primitive} to functions on \AgdaCode[\AgdaOperator{\AgdaBound{⟨}}\AgdaSpace{}%
\AgdaBound{Value}\AgdaSpace{}%
\AgdaOperator{\AgdaBound{⟩}}]
{⟨ Value ⟩},
and using it fixed the error.

In CP89, the inheritance hierarchy is assumed to be a finite tree.
Below, \AgdaCode[\AgdaDatatype{Class}]
{Class} is defined as the datatype of all finite trees.
Using a datatype avoids the need for the partial \textit{parent} function,
and for a predicate for testing whether a class is the root of the hierarchy.
%
\begin{code}
data Class : Set where
  child   : Name → Class → Class  -- a subclass
  origin  : Class                 -- the root class
variable κ : Class
\end{code}
%
The syntax of method expressions is defined by the inductive datatype \AgdaCode[\AgdaDatatype{Exp}]
{Exp}:
%
\begin{code}
data Exp : Set where
  self   : Exp                    -- current object behavior
  super  : Exp                    -- superclass behavior
  arg    : Exp                    -- method argument value
  call   : Exp → Key → Exp → Exp  -- call method with argument
  appl   : Primitive → Exp → Exp  -- apply primitive to value
variable e : Exp

module Semantics
    ( class     : Instance → Class )        -- the class of an object
    ( methods′  : Class → Key → (Exp +?) )  -- the methods of a class
  where
  methods : Class → Key → (Exp +?)          -- no root class methods
  methods (child c κ) m  = methods′ (child c κ) m
  methods origin m       = ??
\end{code}

\subsection{Method Lookup Semantics}

The method lookup semantics uses mutually-recursive functions 
\AgdaCode[\AgdaFunction{send}]
{send}, \AgdaCode[\AgdaFunction{lookup}]
{lookup}, and \AgdaCode[\AgdaOperator{\AgdaFunction{do⟦\AgdaUnderscore{}⟧}}]
{do⟦ ⟧},
which can be non-terminating, 
They are therefore defined in Agda as the least fixed point
of a non-recursive function \AgdaCode[\AgdaFunction{g}]
{g}
(as in the proof of Proposition~3 in CP89) on a domain \AgdaCode[\AgdaBound{Gᵍ}]
{Gᵍ}
that is isomorphic to~\AgdaCode[\AgdaFunction{Dᵍ}]
{Dᵍ}:
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
The behavior of \AgdaCode[\AgdaFunction{send}\AgdaSpace{}%
\AgdaBound{ρ}]
{send ρ} is to use \AgdaCode[\AgdaFunction{lookup}]
{lookup} 
(to be supplied as the argument \AgdaCode[\AgdaBound{l}]
{l} of \AgdaCode[\AgdaFunction{g}]
{g} above)
to obtain the behavior of \AgdaCode[\AgdaBound{ρ}]
{ρ} using the class of \AgdaCode[\AgdaBound{ρ}]
{ρ} itself:
%
\begin{code}
      send : Instance → ⟨ Behavior ⟩
      send ρ = l (class ρ) ρ
\end{code}
%
The behavior of \AgdaCode[\AgdaFunction{lookup}\AgdaSpace{}%
\AgdaBound{κ}\AgdaSpace{}%
\AgdaBound{ρ}]
{lookup κ ρ} for a subclass \AgdaCode[\AgdaBound{κ}]
{κ} 
depends on whether it is called with a method \AgdaCode[\AgdaBound{m}]
{m} defined by \AgdaCode[\AgdaBound{κ}]
{κ}:
if so, it uses \AgdaCode[\AgdaOperator{\AgdaFunction{do⟦}}\AgdaSpace{}%
\AgdaBound{e}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{⟧}}]
{do⟦ e ⟧} (via argument \AgdaCode[\AgdaOperator{\AgdaBound{d⟦\AgdaUnderscore{}⟧}}]
{d⟦ ⟧} of \AgdaCode[\AgdaFunction{g}]
{g})
to execute the corresponding method expression;
if not, it recursively looks up \AgdaCode[\AgdaBound{m}]
{m} in the superclass of \AgdaCode[\AgdaBound{κ}]
{κ}.
The behavior is undefined when \AgdaCode[\AgdaBound{κ}]
{κ} is the root of the inheritance hierarchy,
which has been defined to have no methods:
%
\begin{code}
      lookup : Class → Instance → ⟨ Behavior ⟩
      lookup (child c κ) ρ = 
        from λ m →  [  ( λ e → inl (d⟦ e ⟧ ρ (child c κ)) ) ,
                       ( to (l κ ρ) m )
                    ]? (methods (child c κ) m)
      lookup origin ρ = ⊥
\end{code}
%
When applied to a value \AgdaCode[\AgdaBound{α}]
{α}, the value returned by the function \AgdaCode[\AgdaField{to}\AgdaSpace{}%
\AgdaSymbol{(}\AgdaOperator{\AgdaFunction{do⟦}}\AgdaSpace{}%
\AgdaBound{e}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{⟧}}\AgdaSpace{}%
\AgdaBound{ρ}\AgdaSpace{}%
\AgdaBound{κ}\AgdaSymbol{)}]
{to (do⟦ e ⟧ ρ κ)} may be
a behavior, a number, or undefined (\AgdaCode[\AgdaFunction{⊥}]
{⊥}):
%
\begin{code}
      do⟦_⟧ : Exp → Instance → Class → ⟨ Fun ⟩
      do⟦ self          ⟧ ρ κ            = from λ α → from (inl (s ρ))
      do⟦ super         ⟧ ρ (child c κ)  = from λ α → from (inl (l κ ρ))
      do⟦ super         ⟧ ρ origin       = from λ α → ⊥
      do⟦ arg           ⟧ ρ κ            = from λ α → α
      do⟦ call e₁ m e₂  ⟧ ρ κ  = 
        from λ α → [ ( λ σ → [  ( λ φ → to φ (to (d⟦ e₂ ⟧ ρ κ) α) ) ,
                                ( λ _ → ⊥ )
                             ]⊥ (to σ m) ) ,
                     ( λ ν → ⊥ )
                   ]⊥ (to (to (d⟦ e₁ ⟧ ρ κ) α))
      do⟦ appl f e₁     ⟧ ρ κ  =
        from λ α → apply⟦ f ⟧ (to (d⟦ e₁ ⟧ ρ κ) α)
\end{code}
%
The only complicated case is for calling method \AgdaCode[\AgdaBound{m}]
{m} of object \AgdaCode[\AgdaBound{e₁}]
{e₁} 
with argument \AgdaCode[\AgdaBound{e₂}]
{e₂}.
When the value of \AgdaCode[\AgdaBound{e₁}]
{e₁} is a behavior \AgdaCode[\AgdaBound{σ}]
{σ} that maps \AgdaCode[\AgdaBound{m}]
{m} to a function \AgdaCode[\AgdaBound{φ}]
{φ},
that function is applied to the value of \AgdaCode[\AgdaBound{e₂}]
{e₂};
otherwise the value of the call is undefined.
The undefined cases are not explicit in CP89.

The use of \AgdaCode[\AgdaBound{fix}]
{fix} below has the effect of making the above definitions mutually recursive:
%
\begin{code}
    γ : ⟨ Gᵍ ⟩ → ⟨ Gᵍ ⟩
    γ = from ∘ g ∘ to
    send     = proj₁ (to (fix γ))
    lookup   = proj₁ (proj₂ (to (fix γ)))
    do⟦_⟧    = proj₂ (proj₂ (to (fix γ)))
\end{code}
%
That concludes the Agda definition of the method lookup semantics.

\subsection{Denotational Semantics}

The denotational semantics of method expressions takes the behavior of the 
expressions \AgdaCode[\AgdaInductiveConstructor{self}]
{self} (\AgdaCode[\AgdaBound{σ}]
{σ})
and \AgdaCode[\AgdaInductiveConstructor{super}]
{super} (\AgdaCode[\AgdaBound{π}]
{π}) as arguments, so their evaluation is trivial.
The evaluation of the other method expressions is similar to their method lookup semantics.
%
\begin{code}
  eval⟦_⟧ : Exp → ⟨ Behavior ⟩ → ⟨ Behavior ⟩ → ⟨ Fun ⟩
  eval⟦ self          ⟧ σ π = from λ α → from (inl σ)
  eval⟦ super         ⟧ σ π = from λ α → from (inl π )
  eval⟦ arg           ⟧ σ π = from λ α → α
  eval⟦ call e₁ m e₂  ⟧ σ π =
    from λ α → [ ( λ σ′ → [  ( λ φ → to φ (to (eval⟦ e₂ ⟧ σ π) α) ) ,
                             ( λ _ → ⊥ )
                          ]⊥ (to σ′ m) ) ,
                  ( λ ν → ⊥ )
               ]⊥ (to (to (eval⟦ e₁ ⟧ σ π) α))
  eval⟦ appl f e₁     ⟧ σ π =
    from λ α → apply⟦ f ⟧ (to (eval⟦ e₁ ⟧ σ π) α)
\end{code}
%
The recursively-defined function \AgdaCode[\AgdaOperator{\AgdaFunction{eval⟦\AgdaUnderscore{}⟧}}]
{eval⟦ ⟧} is obviously total,
so there is no need for an explicit fixed point.

According to the conceptual analysis of inheritance in CP89,
the behavior of an instance \AgdaCode[\AgdaBound{ρ}]
{ρ} is the fixed point
of the generator associated with the class of \AgdaCode[\AgdaBound{ρ}]
{ρ}.

The generator for a subclass is obtained by modifying the generator of its parent class
using a wrapper that provides the behavior of the methods defined by the subclass,
given the behavior of the expressions \AgdaCode[\AgdaInductiveConstructor{self}]
{self} (\AgdaCode[\AgdaBound{σ}]
{σ})
and \AgdaCode[\AgdaInductiveConstructor{super}]
{super} (\AgdaCode[\AgdaBound{π}]
{π}) as arguments.

The auxiliary operation \AgdaCode[\AgdaBound{σ₁}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{⊕}}\AgdaSpace{}%
\AgdaBound{σ₂}]
{σ₁ ⊕ σ₂} combines its argument behaviors,
letting the methods of \AgdaCode[\AgdaBound{σ₁}]
{σ₁} shadow those of \AgdaCode[\AgdaBound{σ₂}]
{σ₂}.
The operation \AgdaCode[\AgdaBound{w}\AgdaSpace{}%
\AgdaOperator{\AgdaFunction{⍄}}\AgdaSpace{}%
\AgdaBound{p}]
{w ⍄ p} combines the wrapper of a subclass with the generator of its parent class.
See Figure~9 of CP89 for an illustration of wrapper application.
%
\begin{code}
  Generator = ⟨ Behavior ⟩ → ⟨ Behavior ⟩
  Wrapper   = ⟨ Behavior ⟩ → ⟨ Behavior ⟩ → ⟨ Behavior ⟩

  _⊕_ : ⟨ Behavior ⟩ → ⟨ Behavior ⟩ → ⟨ Behavior ⟩
  σ₁ ⊕ σ₂ = from λ m →
    [ ( λ φ → inl φ ) , ( λ _ → to σ₂ m ) ]⊥ (to σ₁ m)
  _⍄_ : Wrapper → Generator → Generator
  w ⍄ p = λ σ → (w σ (p σ)) ⊕ (p σ)
  wrap : Class → Wrapper
  wrap κ = λ σ → λ π → from λ m →
    [ ( λ e → inl (eval⟦ e ⟧ σ π) ), ( inr ⊥ ) ]? (methods κ m)

  gen : Class → Generator
  gen (child c κ)  = wrap (child c κ) ⍄ gen κ
  gen origin       = λ σ → ⊥
  behave : Instance → ⟨ Behavior ⟩
  behave ρ = fix (gen (class ρ))
\end{code}%
\end{AgdaAlign}%
%
That concludes the Agda definition of the denotational semantics.