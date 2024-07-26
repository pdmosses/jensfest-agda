\section{Semantic Definitions}
\label{sec:semantic-definitions}

This section presents an Agda formulation of the denotational semantics of inheritance
given by William Cook and Jens Palsberg \cite{Cook1989PHD,Cook1989DSI,Cook1994DSI}.
%[Cook1989PHD]: https://cs.brown.edu/research/pubs/theses/phd/1989/cook.pdf
%[Cook1989DSI]: https://doi.org/10.1145/74877.74922 "OOPSLA '89"
%[Cook1994DSI]: https://doi.org/10.1006/INCO.1994.1090 "Inf. Comput."
The semantics is based on a conceptual analysis of inheritance in terms of
fixed points of generators and wrappers.

See the cited publications for motivation of inheritance and its fixed-point analysis.
The explanations given below are necessarily brief, and assume familiarity with the main ideas.
Readers who are not familiar with Agda notation may find it helpful to browse the Agda Wikipedia page%
\footnote{\url{https://en.wikipedia.org/wiki/Agda_(programming_language)}}
before proceeding.

The \LaTeX\ source of this section was generated by Agda from a literate Agda specification.%
\footnote{\url{???}}
Some Unicode characters used in Agda have been mapped to corresponding \LaTeX\ math symbols.

\subsection{Agda Standard Library Notation}
\label{sec:semantic-definitions:standard-library}

The Agda definitions use the following modules from the standard library.%
\footnote{\url{https://agda.github.io/agda-stdlib/v2.0/}}
%
\begin{AgdaAlign}
\begin{code}
open import Data.Nat.Base     using (ℕ; zero; suc; _≤_)       -- natural numbers
open import Data.Product.Base using (_×_; _,_)                -- A × B is Cartesian product
open import Data.Sum.Base     using (_⊎_; inj₁; inj₂; [_,_])  -- A ⊎ B is disjoint union
open import Data.Unit.Base    using (⊤; tt)                   -- tt is the only element of type ⊤
open import Function          using (Inverse; _↔_; _∘_)       -- A ↔ B is isomorphism between A and B

module Inheritance.Definitions
\end{code}

\subsection{Scott Domains}
\label{sec:semantic-definitions:scott-domains}

The following notation for Scott domains and their operations is assumed.
%
\begin{code}
    (Domain : Set₁)                                     -- Domain is a type of cpo
    (⟨_⟩    : Domain → Set)                             -- ⟨ D ⟩ is the type of elements of D
    (⊥      : {D : Domain} → ⟨ D ⟩)                     -- ⊥ is the least element of D
    (fix    : {D : Domain} → (⟨ D ⟩ → ⟨ D ⟩) → ⟨ D ⟩)   -- fix f is the least fixed-point of f
    (?⊥     : Domain)                                   -- ⊥ is the only element of ?⊥
    (_+⊥_   : Domain → Domain → Domain)                 -- D +⊥ E is the separated sum of D and E
    (inl    : {D E : Domain} → ⟨ D ⟩ → ⟨ D +⊥ E ⟩)      -- inl x injects elements x of D into D +⊥ E
    (inr    : {D E : Domain} → ⟨ E ⟩ → ⟨ D +⊥ E ⟩)      -- inr y injects elements y of E into D +⊥ E
    ([_,_]⊥ :                                           -- [ f , g ]⊥ is case analysis for D +⊥ E
              {D E F : Domain} → (⟨ D ⟩ → ⟨ F ⟩) → (⟨ E ⟩ → ⟨ F ⟩) → ⟨ D +⊥ E ⟩ → ⟨ F ⟩)
\end{code}
%
As usual in denotational semantics,
all declared domains are supposed to be cpos (complete posets)
with least elements and lubs (least upper bounds) of increasing chains.
All declared functions between domains are supposed to be Scott continuous.
Defining functions in lambda-notation preserves continuity.

It should be possible to define the above notation by importing
the DomainTheory modules from the TypeTopology library,
taking Domain to be DCPO⊥ (directed-complete posets with least elements).
However, all lambda-abstractions would then need to be accompanied by continuity proofs,
and all applications would need to explicitly extract the underlying functions.
This would signficantly complicate the semantic definitions given below.

Functions between domains are partially ordered pointwise,
and least function maps all elements to bottom.
Functions from unordered types to domains are trivially continuous,
and correspond to strict functions from flat domains obtained by lifting.

\subsection{Method Systems}

\begin{code}
    (Instance : Set)
    (Class-Name : Set)
    (Key : Set)
    (Primitive : Set)
  where
\end{code}
%
The inheritance hierarchy is required to be a finite tree.
Below, this is specified by defining the Class type inductively:
the origin class is the root of the tree,
and each child class has a class-name and a parent.
%
\begin{code}
data Class : Set where
  child  : Class-Name → Class → Class
  origin : Class
parent : Class → (Class ⊎ ⊤)
parent (child _ κ)  = inj₁ κ
parent origin       = inj₂ tt
variable
  ρ : Instance
  κ : Class
  m : Key
  f : Primitive
\end{code}
%
Applications of primitives are restricted here to a single argument.
This avoids the need for defining the semantics of vectors of expressions.
%
\begin{code}
data Exp : Set where
  self  : Exp
  super : Exp
  arg   : Exp
  call  : Exp → Key → Exp → Exp  -- unary methods
  appl  : Primitive → Exp → Exp  -- unary functions
variable
  e : Exp
\end{code}
%
Each instance has a unique class.
The value of methods κ m is either the local method expression defined by κ for key m,
or tt if κ doesn't define a method expression for m.
%
\begin{code}
module _ 
    (class   : Instance → Class)
    (methods : Class → Key → (Exp ⊎ ⊤))
\end{code}
%
Both the operational and the denotational semantics of method systems
involve iso-recursive domains.
The existence of isomorphisms between these domains is assumed below.
%
\begin{code}
    (Number : Domain)
    (Value : Domain)
    (Behavior : Domain)
    (Fun : Domain)
    {{ isoᵛ : ⟨ Value ⟩    ↔ ⟨ Behavior +⊥ Number ⟩  }}
    {{ isoᵇ : ⟨ Behavior ⟩ ↔ (Key → ⟨ Fun +⊥ ?⊥ ⟩)   }}
    {{ isoᶠ : ⟨ Fun ⟩      ↔ (⟨ Value ⟩ → ⟨ Value ⟩) }}
\end{code}
%
A semantic function for applying primitives to values is assumed:
%
\begin{code}
    (apply⟦_⟧ : Primitive → ⟨ Value ⟩ → ⟨ Value ⟩)
  where
  variable
    α : ⟨ Value ⟩
    σ σ′ π π′ : ⟨ Behavior ⟩
    φ : ⟨ Fun ⟩
\end{code}
%
The following declaration introduces overloaded inverse functions
"to" and "from"
corresponding to the isomorphisms specified above:%
\footnote
{Such isomorphisms are usually left implicit in semantic definitions,
but Agda requires them to be explicit;
similarly for injections into separated sum domains.}
%
\begin{code}
  open Inverse {{ ... }}
\end{code}

\subsection{Method Lookup Semantics}

To specify the semantic functions that correspond to the method lookup algorithm,
it appears necessary to use an explicit fixed-point of a non-recursive functional:
%
\begin{code}
  Γ = (Instance → ⟨ Behavior ⟩) ×
      (Class → Instance → ⟨ Behavior ⟩) ×
      (Exp → Instance → Class → ⟨ Fun ⟩)
  γ : Γ → Γ
  γ (sendʳ , lookupʳ , doʳ⟦_⟧) = (send , lookup , do⟦_⟧) where

    send : Instance → ⟨ Behavior ⟩
    send ρ = lookupʳ (class ρ) ρ

    lookup : Class → Instance → ⟨ Behavior ⟩
    lookup (child c κ) ρ = from λ m → [ ( λ e → inl (doʳ⟦ e ⟧ ρ (child c κ)) ) ,
                                        ( λ _ → to (lookupʳ κ ρ) m )
                                      ] (methods (child c κ) m)
    lookup origin ρ      = ⊥

    do⟦_⟧ : Exp → Instance → Class → ⟨ Fun ⟩
    do⟦ self ⟧ ρ κ            = from λ α → from (inl (sendʳ ρ))
    do⟦ super ⟧ ρ origin      = from λ α → ⊥
    do⟦ super ⟧ ρ (child c κ) = from λ α → from (inl (lookupʳ κ ρ))
    do⟦ arg ⟧ ρ κ             = from λ α → α
    do⟦ call e₁ m e₂ ⟧ ρ κ    = from λ α → [ ( λ σ → [ ( λ φ → to φ (to (doʳ⟦ e₂ ⟧ ρ κ) α) ) ,
                                                      ( λ _ → ⊥ )
                                                    ]⊥ (to σ m) ) ,
                                            ( λ ν → from (inr ν) )
                                          ]⊥ (to (to (doʳ⟦ e₁ ⟧ ρ κ) α))
    do⟦ appl f e₁ ⟧ ρ κ       = from λ α → apply⟦ f ⟧ (to (doʳ⟦ e₁ ⟧ ρ κ) α)
\end{code}
%
% The following definitions correspond to making the above definitions recursive:
%
\begin{code}[hide]
  module _
    (G : Domain)
    {{ isoᵍ : ⟨ G ⟩ ↔ Γ }}
    where
    g : ⟨ G ⟩ → ⟨ G ⟩
    g = from ∘ γ ∘ to

    send     = let (sendʳ , lookupʳ , doʳ⟦_⟧) = to (fix g) in sendʳ
    lookup   = let (sendʳ , lookupʳ , doʳ⟦_⟧) = to (fix g) in lookupʳ
    do⟦_⟧     = let (sendʳ , lookupʳ , doʳ⟦_⟧) = to (fix g) in doʳ⟦_⟧
\end{code}

\subsection{Denotational Semantics}

The types of generators and wrappers are defined as function spaces,
to avoid the need for further isomorphisms.
%
\begin{code}
  eval⟦_⟧ : Exp → ⟨ Behavior ⟩ → ⟨ Behavior ⟩ → ⟨ Fun ⟩
  eval⟦ self ⟧ σ π           = from λ α → from (inl σ)
  eval⟦ super ⟧ σ π          = from λ α → from (inl π )
  eval⟦ arg ⟧ σ π            = from λ α → α
  eval⟦ call e₁ m e₂ ⟧ σ π   = from λ α → [ ( λ σ′ → 
                                                [ ( λ φ → to φ (to (eval⟦ e₂ ⟧ σ π) α) ) ,
                                                  ( λ _ → ⊥ )
                                                ]⊥ (to σ′ m) ) ,
                                            ( λ ν → from (inr ν) )
                                           ]⊥ (to (to (eval⟦ e₁ ⟧ σ π) α))
  eval⟦ appl f e₁ ⟧ σ π      = from λ α → apply⟦ f ⟧ (to (eval⟦ e₁ ⟧ σ π) α)

  Generator = ⟨ Behavior ⟩ → ⟨ Behavior ⟩
  Wrapper   = ⟨ Behavior ⟩ → Generator
  
  _⊕_ : ⟨ Behavior ⟩ → ⟨ Behavior ⟩ → ⟨ Behavior ⟩
  σ₁ ⊕ σ₂ = from λ m → [ ( λ φ → inl φ ) , ( λ _ → to σ₂ m ) ]⊥ (to σ₁ m)

  _⍄_ : Wrapper → Generator → Generator
  w ⍄ p = λ σ → (w σ (p σ)) ⊕ (p σ)

  wrap : Class → Wrapper
  wrap κ = λ σ → λ π → from λ m → [ ( λ e → inl (eval⟦ e ⟧ σ π) ) ,
                                    ( λ _ → inr ⊥ )
                                  ] (methods κ m)

  gen : Class → Generator
  gen (child c κ)  = wrap (child c κ) ⍄ gen κ
  gen origin       = λ σ → ⊥

  behave : Instance → ⟨ Behavior ⟩
  behave ρ = fix (gen (class ρ))
\end{code}

\subsection{Intermediate Semantics}

Cases of Agda definitions are sequential:
below, putting the cases for 
\AgdaInductiveConstructor{zero}
before the corresponding cases for
\AgdaBound{n}
implies that
\AgdaBound{n}
is positive.
% This makes it straightforward for Agda to check that the mutual recursion terminates.
% Using
% \AgdaInductiveConstructor{suc}\AgdaSpace{}\AgdaBound{n}
% instead of
% \AgdaBound{n}
% would make the termination check fail.

\begin{code}
  send′    : ℕ → Instance → ⟨ Behavior ⟩
  lookup′  : ℕ → Class → Instance → ⟨ Behavior ⟩
  do′_⟦_⟧  : ℕ → Exp → Instance → Class → ⟨ Fun ⟩

  send′ n ρ = lookup′ n (class ρ) ρ

  lookup′ zero κ ρ         = ⊥
  lookup′ n origin ρ       = ⊥
  lookup′ n (child c κ) ρ  = from λ m → [ ( λ e → inl (do′ n ⟦ e ⟧ ρ (child c κ)) ) ,
                                          ( λ _ → to (lookup′ n κ ρ ) m )
                                        ] (methods (child c κ) m)

  do′ zero ⟦ e ⟧ ρ κ              = from λ α → ⊥
  do′ (suc n) ⟦ self ⟧ ρ κ        = from λ α → from (inl (send′ n ρ))
  do′ n ⟦ super ⟧ ρ origin        = from λ α → ⊥
  do′ n ⟦ super ⟧ ρ (child c κ)   = from λ α → from (inl (lookup′ n κ ρ))
  do′ n ⟦ arg ⟧ ρ κ               = from λ α → α
  do′ n ⟦ call e₁ m e₂ ⟧ ρ κ      = from λ α → [  ( λ σ → 
                                                     [  ( λ φ → to φ (to (do′ n ⟦ e₂ ⟧ ρ κ) α) ) ,
                                                        ( λ _ → ⊥ )
                                                     ]⊥ (to σ m) ) ,
                                                 ( λ ν → from (inr ν) )
                                            ]⊥ (to (to (do′ n ⟦ e₁ ⟧ ρ κ ) α))
  do′ n ⟦ appl f e₁ ⟧ ρ κ         = from λ α → apply⟦ f ⟧ (to (do′ n ⟦ e₁ ⟧ ρ κ) α)
\end{code}
