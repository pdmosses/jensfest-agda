\section{Semantic Definitions}
\label{sec:semantic-definitions}

This section presents an Agda formulation of the denotational semantics of inheritance
given by William Cook and Jens Palsberg in their OOPSLA '89 paper \cite{Cook1989DSI}
%[Cook1989DSI]: https://doi.org/10.1145/74877.74922 "OOPSLA '89"
(hereafter referred to as CP89).%
\footnote{The same semantics appears in \cite{Cook1989PHD,Cook1994DSI}.}
%[Cook1989PHD]: https://cs.brown.edu/research/pubs/theses/phd/1989/cook.pdf
%[Cook1994DSI]: https://doi.org/10.1006/INCO.1994.1090 "Inf. Comput."
It is based on a conceptual analysis of inheritance in terms of
fixed points of generators and wrappers.

See the cited publication for motivation of inheritance and its fixed-point analysis.
Apart from commenting on some differences from the original semantics,
the explanations given below focus on how various features are modeled as functions;
they are necessarily brief, and assume familiarity with the basic concepts of inheritance.

Readers who are not familiar with Agda notation may find it helpful to browse the Agda Wikipedia page%
\footnote{\url{https://en.wikipedia.org/wiki/Agda_(programming_language)}}
before proceeding.

The \LaTeX\ source of this section was generated by Agda from a literate Agda specification.%
\footnote{\url{???}}
Some Unicode characters used in Agda have been mapped to corresponding \LaTeX\ math symbols.

\subsection{Agda Standard Library Notation}
\label{sec:semantic-definitions:standard-library}

The Agda definitions given below use the following modules from the standard library.%
\footnote{\url{https://agda.github.io/agda-stdlib/v2.0/}}
%
\begin{AgdaAlign}
\begin{code}
open import Data.Nat.Base      using (ℕ; zero; suc; _≤_)       -- natural numbers
open import Data.Maybe.Base    using (Maybe; maybe′; just; nothing)
open import Data.Product.Base  using (_×_; _,_; proj₁; proj₂)  -- A × B is Cartesian product
open import Data.Sum.Base      using (_⊎_; inj₁; inj₂; [_,_])  -- A ⊎ B is disjoint union
open import Data.Unit.Base     using (⊤; tt)                   -- tt is the only element of the type ⊤
open import Function           using (Inverse; _↔_; _∘_)       -- A ↔ B is isomorphism between A and B
\end{code}
%
For each instance argument with an isomorphism type "A ↔ B",
the following declaration introduces overloaded inverse functions:%
\footnote
{Such isomorphisms are usually left implicit in published semantic definitions,
but Agda requires them to be made explicit;
similarly for injections into separated sum domains.}
%
\begin{code}
open Inverse {{ ... }}         using (to; from)                -- to : A → B; from : B → A
open import Relation.Binary.PropositionalEquality using (_≡_)  -- x ≡ y is equality of x and y

module Inheritance.Definitions
\end{code}

\subsection{Scott Domains}
\label{sec:semantic-definitions:scott-domains}

The following notation for Scott domains and their operations is assumed.
%
\begin{code}
    {Domain  :  Set₁}                                     -- Domain is a type of cpo
    {⟨_⟩     :  Domain → Set}                             -- ⟨ D ⟩ is the type of elements of D
    {⊥       :  {D : Domain} → ⟨ D ⟩}                     -- ⊥ is the least element of D
    {fix     :  {D : Domain} → (⟨ D ⟩ → ⟨ D ⟩) → ⟨ D ⟩}   -- fix f is the least fixed-point of f
    {?⊥      :  Domain}                                   -- ⊥ is the only element of ?⊥
    {_+⊥_    :  Domain → Domain → Domain}                 -- D +⊥ E is the separated sum of D and E
    {inl     :  {D E : Domain} → ⟨ D ⟩ → ⟨ D +⊥ E ⟩}      -- inl x injects elements x of D into D +⊥ E
    {inr     :  {D E : Domain} → ⟨ E ⟩ → ⟨ D +⊥ E ⟩}      -- inr y injects elements y of E into D +⊥ E
    {[_,_]⊥  :                                            -- [ f , g ]⊥ is case analysis for D +⊥ E
                {D E F : Domain} → (⟨ D ⟩ → ⟨ F ⟩) → (⟨ E ⟩ → ⟨ F ⟩) → ⟨ D +⊥ E ⟩ → ⟨ F ⟩}
\end{code}
%
As usual in denotational semantics,
all domains are supposed to be cpos (complete posets)
with least elements and lubs (least upper bounds) of increasing chains;
and all functions between domains are supposed to be Scott continuous.
Defining functions in lambda-notation preserves continuity.

It should be possible to define the notation declared above by importing
some of the DomainTheory modules from the TypeTopology library,
taking Domain to be DCPO⊥ (directed-complete posets with least elements).
However, all lambda-abstractions would then need to be accompanied by continuity proofs,
and all applications would need to explicitly extract the underlying functions.
This would signficantly complicate the semantic definitions given below,
and is left to future work.

Functions between domains are ordered pointwise,
and least function maps all elements to bottom;
Cartesian products of domains are ordered componentwise.
Unordered types can be regarded as discretely-ordered dcpos,
and all functions from an unordered type to a domain are then trivially continuous.

\subsection{Method Systems}

The method systems defined in CP89 are a simple formalization of object-oriented programming.
They abstract from aspects such as instance variables, assignment, and object creation.
A method system corresponds to a snapshot in the execution of an object-oriented system.

In CP89, the ingredients of method systems are assumed to be elements of flat domains;
however, the least elements of these domains are irrelevant,
and it is simpler to use ordinary Agda types instead of flat domains:
%
\begin{code}
    {Instance   : Set}  -- objects
    {Name       : Set}  -- class names
    {Key        : Set}  -- method names
    {Primitive  : Set}  -- function names
\end{code}
%
Both the operational and the denotational semantics of method systems in CP89 involve
the mutually-recursive domains "Value", "Behavior", and "Fun".
These domains cannot be defined (safely) as Agda types, due to a negative polarity.
However, the intended instantiation of the type "Domain" as a Scott domain
ensures the existence of isomorphisms between the types of elements of such domains:
%
\begin{code}
    {Number    : Domain}  -- the domain of numbers is unconstrained
    {Value     : Domain}  -- a value is (isomorphic to) a behavior or a number
    {Behavior  : Domain}  -- a behaviour maps a method name to a fun, or to the only element of ?⊥
    {Fun       : Domain}  -- a fun maps an argument value to a value (possibly ⊥)
    {{isoᵛ     : ⟨ Value ⟩     ↔ ⟨ Behavior +⊥ Number ⟩}}
    {{isoᵇ     : ⟨ Behavior ⟩  ↔ (Key → ⟨ Fun +⊥ ?⊥ ⟩)}}
    {{isoᶠ     : ⟨ Fun ⟩       ↔ (⟨ Value ⟩ → ⟨ Value ⟩)}}
\end{code}
%
A semantic function for applying primitive functions to values is needed:
%
\begin{code}
    {apply⟦_⟧  : Primitive → ⟨ Value ⟩ → ⟨ Value ⟩}
  where
variable
  ρ    : Instance
  m    : Key
  f    : Primitive
  ν    : ⟨ Number ⟩
  α    : ⟨ Value ⟩
  σ π  : ⟨ Behavior ⟩
  φ    : ⟨ Fun ⟩
\end{code}
%
In CP89, the inheritance hierarchy is required to be a finite tree.
Here, "Class" is defined as an inductive type;
the function "parent" maps each subclass to its superclass.
%
\begin{code}
data Class : Set where
  child   : Name → Class → Class  -- a subclass
  origin  : Class                 -- the root of the tree
variable κ : Class

-- parent : Class → (Class ⊎ ⊤)
-- parent (child _ κ)  = inj₁ κ
-- parent origin       = inj₂ tt
\end{code}
%
The syntax of method expressions is defined by the inductive type "Exp".
%
\begin{code}
data Exp : Set where
  self   : Exp                    -- the behavior of the current object
  super  : Exp                    -- the behavior in the superclass of the object
  arg    : Exp                    -- the single argument of the method expression
  call   : Exp → Key → Exp → Exp  -- "call e₁ m e₂" calls method m of object e₁ with argument e₂
  appl   : Primitive → Exp → Exp  -- "appl f e₁" applies the unary function f to the value of e₁
variable e : Exp
\end{code}
%
The parameters of the following module are available in all the subsequent semantic definitions.
%
\begin{code}
module Semantics
    {class       : Instance → Class}                        -- "class ρ" is the class of an object
    {methods′    : Class → Key → Maybe Exp}                 -- "methods′ κ m" is the method named m in κ
    -- {methodless  : (m : Key) → methods origin m ≡ nothing}  -- the root class defines no methods
  where

  methods : Class → Key → Maybe Exp
  methods (child c κ) m = methods′ (child c κ) m
  methods origin m      = nothing
\end{code}

\subsection{Method Lookup Semantics}

The method lookup semantics uses mutually-recursive functions "send", "lookup", and "do⟦ ⟧".
Agda supports mutual recursion, but functions defined in Agda are supposed to be total,%
\footnote{Agda can also be used in an unsafe mode that allows partial functions to be defined.}
and the mutual recursion required here can be non-terminating, 
These functions are therefore defined in Agda as the least fixed point of the following non-recursive function g
(as in the proof of Proposition~3 in CP89):
%
\begin{code}
  D′ = (Instance → ⟨ Behavior ⟩) ×
       (Class → Instance → ⟨ Behavior ⟩) ×
       (Exp → Instance → Class → ⟨ Fun ⟩)
  g′ : D′ → D′
  g′ (s , l , d⟦_⟧) = (send , lookup , do⟦_⟧) where
\end{code}
%
The behavior of "send ρ" is to use "lookup" (to be supplied as the argument l of g above)
to obtain the behavior of ρ using the class of ρ itself:
%
\begin{code}
    send : Instance → ⟨ Behavior ⟩
    send ρ = l (class ρ) ρ
\end{code}
%
The behavior of "lookup κ ρ" for a subclass κ depends on whether it is called with a method m defined by κ:
if so, it uses "do⟦ e ⟧" (via argument d⟦ ⟧ of g) to execute the corresponding method expression;
if not, it recursively looks up m in the superclass of κ.%
\footnote{The isomorphisms "to" and "from" and the injection "inl" can be ignored.}
The behavior is undefined when κ is the root of the inheritance hierarchy,
which is assumed not to define any methods:
%
\begin{code}
    lookup : Class → Instance → ⟨ Behavior ⟩
    lookup (child c κ) ρ  = from λ m →  maybe′  (λ e → inl (d⟦ e ⟧ ρ (child c κ)))
                                                (to (l κ ρ) m)
                                                (methods (child c κ) m)
    lookup origin ρ       = from λ m →  ⊥
\end{code}
%
When applied to a value α, the value returned by the function "do⟦ e ⟧ ρ κ" may be
a behavior, a number, or undefined:
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
The only complicated case is for calling method m of object e₁ with argument e₂.
When the value of e₁ is a behavior σ that maps m to a function φ,
that function is applied to the value of e₂;
otherwise the value of the call is undefined.

The following definitions correspond to making the above definitions mutually recursive,
using an auxilary domain G′ whose type of elements ⟨ G′ ⟩ is isomorphic to the type D′:
%
\begin{code}
  module _
      (G′ : Domain)
      {{ isoᵍ : ⟨ G′ ⟩ ↔ D′ }}
    where
    γ : ⟨ G′ ⟩ → ⟨ G′ ⟩
    γ = from ∘ g′ ∘ to

    send     = proj₁ (to (fix γ))
    lookup   = proj₁ (proj₂ (to (fix γ)))
    do⟦_⟧    = proj₂ (proj₂ (to (fix γ)))
\end{code}

That completes the definition of the method lookup semantics.

\subsection{Denotational Semantics}

The denotational semantics of method expressions takes the behavior of the expressions "self" (σ)
and "super" (π) as arguments, so their evaluation is trivial.
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
The evaluation function is obviously total,
so there is no need for an explicit fixed point in its Agda definition.

According to the conceptual analysis of inheritance in CP89,
the behavior of an instance ρ will be defined as the fixed-point
of the generator associated with the class of ρ.

The generator for a subclass is obtained by modifying the generator of its parent class
using a wrapper that provides the behavior of the methods defined by the subclass,
given the behavior of the expressions "self" (σ) and "super" (π) as arguments.

The auxiliary operation σ₁ ⊕ σ₂ combines its argument behaviors,
letting the methods of σ₁ shadow those of σ₂.
The operation w ⍄ p combines the wrapper of a subclass with the generator of its parent class.
Wrapper application is illstrated in Figure~9 of CP89.
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
  wrap κ = λ σ → λ π → from λ m → maybe′  (λ e →  inl (eval⟦ e ⟧ σ π))
                                          (inr ⊥)
                                          (methods κ m)

  gen : Class → Generator
  gen (child c κ)  = wrap (child c κ) ⍄ gen κ
  gen origin       = λ σ → from λ m → inr ⊥

  behave : Instance → ⟨ Behavior ⟩
  behave ρ = fix (gen (class ρ))
\end{code}

\subsection{Intermediate Semantics}

The intermediate semantics of method expressions given in CP89
is a step-indexed variant of the method lookup semantics.
It takes an extra argument n ranging over ℕ (the natural numbers),
which acts as sufficient `fuel' for up to n-1 uses of "self":
when n is zero, the intermediate semantics is the undefined behavior (⊥).
One of the lemmas proved in CP89 shows that the intermediate semantics at n
corresponds to the n'th approximation to the denotational semantics.

Cases of Agda definitions are sequential:
below, putting a case for \AgdaInductiveConstructor{zero}
before the corresponding case for \AgdaBound{n}
implies that \AgdaBound{n} is positive in the latter.

The functions used to specify the intermediate semantics are mutually recursive,
in the same way as in the method lookup semantics.
Here, however, the finiteness of the fuel argument ensures that the functions are total,
so they can be defined in Agda without an explicit least fixed-point:
%
\begin{code}
  send′    : ℕ → Instance → ⟨ Behavior ⟩
  lookup′  : ℕ → Class → Instance → ⟨ Behavior ⟩
  do′_⟦_⟧  : ℕ → Exp → Instance → Class → ⟨ Fun ⟩

  send′ n ρ = lookup′ n (class ρ) ρ

  lookup′ zero κ ρ         = from λ m → inr ⊥
  lookup′ n origin ρ       = from λ m → inr ⊥
  lookup′ n (child c κ) ρ  = from λ m → maybe′  (λ e → inl (do′ n ⟦ e ⟧ ρ (child c κ)))
                                                (to (lookup′ n κ ρ ) m)
                                                (methods (child c κ) m)

  do′ zero     ⟦ e             ⟧ ρ κ            = from λ α → ⊥
  do′ (suc n)  ⟦ self          ⟧ ρ κ            = from λ α → from (inl (send′ n ρ))
  do′ n        ⟦ super         ⟧ ρ origin       = from λ α → ⊥
  do′ n        ⟦ super         ⟧ ρ (child c κ)  = from λ α → from (inl (lookup′ n κ ρ))
  do′ n        ⟦ arg           ⟧ ρ κ            = from λ α → α
  do′ n        ⟦ call e₁ m e₂  ⟧ ρ κ            = from λ α → 
                                                   [  ( λ σ →  [  ( λ φ →  to φ (to (do′ n ⟦ e₂ ⟧ ρ κ) α) ) ,
                                                                  ( λ _ →  ⊥ )
                                                               ]⊥ (to σ m) ) ,
                                                      ( λ ν →  ⊥ )
                                                   ]⊥ (to (to (do′ n ⟦ e₁ ⟧ ρ κ ) α))
  do′ n        ⟦ appl f e₁     ⟧ ρ κ            = from λ α → apply⟦ f ⟧ (to (do′ n ⟦ e₁ ⟧ ρ κ) α)
\end{code}
\end{AgdaAlign}
%
That concludes the Agda formulation of the semantic definitions given in CP89.

\subsection{Summary}

In published presentations of semantic definitions,
it is common practice to leave some notational details implicit,
to focus attention on the significant items.
CP89 is no exception: it leaves injections into sum domains implicit,
and doesn't even mention the isomorphisms between recursively defined domains.
To type-check the semantics in Agda, however,
it appears that all injections and isomorphisms need to be made explicit.

Moreover, CP89 states some assumptions informally, e.g.,
``\emph{parent} defines the inheritance hierarchy, which is required to be a tree'', and
``the root of the inheritance hierarchy doesn't define any methods''.
When using Agda, all assumptions need to be formally stated.
Here, the inheritance hierarchy is defined as an inductive type:
a subclass is essentially just a name and the list of the names its superclasses.
The type of classes is infinite, but each class has only finitely many parents.
It would be possible to constrain the type to a finite tree using indexed types,
if needed.

It is well known \cite{Klein2012RYR} that \emph{running} a specification
can reveal unsuspected errors and omissions
in published presentations of semantic definitions and proofs.
After reformulating the definitions from CP89 in Agda
and adding the implicit details (as shown in Section~\ref{sec:definitions}),
the Agda type-checker revealed only a few minor issues in Figs.\ 14, 16, and 17 of CP89:
%
\begin{itemize}

\item The primitive $f$ in the syntax of method expressions is used as a function in the semantics.

\item The value of $e_1$ in a message-passing expression $e_1~m~e_2$ might be either a behaviour or a number,
but it is applied to $m$ in both cases.

\item The value of $\textit{parent}(\kappa)$ is in $\textbf{Class + ?}$,
but it is used as an argument of functions that take arguments of type \textbf{Class}.
In particular, the semantics of \textbf{super} should check whether $\textit{root}(\kappa)$ is true.

\end{itemize}
%



The next section illustrates the verification of some of the lemmas proved in CP89.