
\section{Equivalence}
\label{sec:proofs}

This section presents the verified Agda proofs of the first three lemmas from CP89,
using the definitions presented in \ref{sec:semantic-definitions}.
Development of Agda proofs of the remaining results is left to future work.

\begin{code}
open import Data.Maybe.Base    renaming (Maybe to _+?; maybe′ to [_,_]?; nothing to ??)
                                                               -- A +? is disjoint union of A and {??}
                                                               -- [ f , x ]? is case analysis on A +?
open import Data.Nat.Base      using (ℕ; zero; suc; _≤_)       -- natural numbers
open import Data.Product.Base  using (_×_; _,_; proj₁; proj₂)  -- A × B is Cartesian product
open import Function           using (Inverse; _↔_; _∘_)       -- A ↔ B is isomorphism between A and B
open Inverse {{ ... }}         using (to; from; inverseˡ)      -- to : A → B; from : B → A

open import Axiom.Extensionality.Propositional using (Extensionality)  -- function extensionality
import Relation.Binary.PropositionalEquality as Eq
open Eq                        using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning            -- using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Level              renaming (zero to lzero) hiding (suc)

module Inheritance.Equivalence
    {Domain  :  Set₁}                                     -- Domain is a type of cpo
    {⟨_⟩     :  Domain → Set}                             -- ⟨ D ⟩ is the type of elements of D
    {_⊑_     :  {D : Domain} → ⟨ D ⟩ → ⟨ D ⟩ → Set}       -- x ⊑ y is the partial order of D
    {⊥       :  {D : Domain} → ⟨ D ⟩}                     -- ⊥ is the least element of D
    (lub     :  {D : Domain} → (δ : ℕ → ⟨ D ⟩) → ⟨ D ⟩)   -- least upper bound of chains δ
    {fix     :  {D : Domain} → (⟨ D ⟩ → ⟨ D ⟩) → ⟨ D ⟩}   -- fix f is the least fixed-point of f
    {?⊥      :  Domain}                                   -- ⊥ is the only element of ?⊥
    {_+⊥_    :  Domain → Domain → Domain}                 -- D +⊥ E is the separated sum of D and E
    {inl     :  {D E : Domain} → ⟨ D ⟩ → ⟨ D +⊥ E ⟩}      -- inl x injects elements x of D into D +⊥ E
    {inr     :  {D E : Domain} → ⟨ E ⟩ → ⟨ D +⊥ E ⟩}      -- inr y injects elements y of E into D +⊥ E
    {[_,_]⊥  :                                            -- [ f , g ]⊥ is case analysis for D +⊥ E
                {D E F : Domain} → (⟨ D ⟩ → ⟨ F ⟩) → (⟨ E ⟩ → ⟨ F ⟩) → ⟨ D +⊥ E ⟩ → ⟨ F ⟩}

    {Instance   : Set}  -- objects
    {Name       : Set}  -- class names
    {Key        : Set}  -- method names
    {Primitive  : Set}  -- function names

    {Number    : Domain}  -- the domain of numbers is unconstrained
    {Value     : Domain}  -- a value is (isomorphic to) a behavior or a number
    {Behavior  : Domain}  -- a behaviour maps a method name to a fun, or to the only element of ?⊥
    {Fun       : Domain}  -- a fun maps an argument value to a value (possibly ⊥)
    {{isoᵛ       : ⟨ Value ⟩     ↔ ⟨ Behavior +⊥ Number ⟩}}
    {{isoᵇ       : ⟨ Behavior ⟩  ↔ (Key → ⟨ Fun +⊥ ?⊥ ⟩)}}
    {{isoᶠ       : ⟨ Fun ⟩       ↔ (⟨ Value ⟩ → ⟨ Value ⟩)}}

    {apply⟦_⟧  : Primitive → ⟨ Value ⟩ → ⟨ Value ⟩}
  where

open import Inheritance.Definitions
    {Domain} {⟨_⟩} {⊥} {fix} {?⊥} {_+⊥_} {inl} {inr} {[_,_]⊥}
    {Instance} {Name} {Key} {Primitive} {Number} {Value} {Behavior} {Fun}
    {{isoᵛ}} {{isoᵇ}} {{isoᶠ}} {apply⟦_⟧}

module _ 
    {class       : Instance → Class}         -- "class ρ" is the class of an object
    {methods′    : Class → Key → (Exp +?)}   -- "methods′ κ m" is the method named m in κ

    {ext : Extensionality lzero lzero}       -- function extensionality
    {[,]⊥-elim : {D E F : Domain} {A : Set}  -- [,]⊥-elim eliminates an application of [ f , g ]⊥
                 {f : ⟨ D ⟩ → ⟨ F ⟩} {g : ⟨ E ⟩ → ⟨ F ⟩} {x : A → ⟨ D ⟩} {y : ⟨ E ⟩} {z : A +?} →
                   [ f , g ]⊥ ( [ ( inl ∘ x ) , ( inr y ) ]? z ) ≡ [ ( f ∘ x ) , ( g y ) ]? z}
  where

  open Semantics {class} {methods′}

  module _
      {G′ : Domain}
      {{ isoᵍ : ⟨ G′ ⟩ ↔ D′ }}
    where

    open MethodLookup {G′} {{isoᵍ}}
\end{code}

\subsection{Lemma 1}

The proof of this lemma is a straightforward structural induction,
which is specified concisely in Agda using the rewrite feature.

\begin{code}
    lemma-1 : ∀ n e ρ c κ →
      do′ (suc n) ⟦ e ⟧ ρ (child c κ) ≡ eval⟦ e ⟧ ( send′ n ρ ) ( lookup′ (suc n) κ ρ )

    lemma-1 n self            ρ c κ = refl
    lemma-1 n super           ρ c κ = refl
    lemma-1 n arg             ρ c κ = refl
    lemma-1 n (call e₁ m e₂)  ρ c κ 
        rewrite lemma-1 n e₁  ρ c κ 
        rewrite lemma-1 n e₂  ρ c κ = refl
    lemma-1 n (appl f e₁)     ρ c κ 
        rewrite lemma-1 n e₁  ρ c κ = refl
\end{code}

\subsection{Lemma 2}

The proof of this lemma exhibits the same steps of equational reasoning as the corresponding proof in CP89.
As a novice user of Agda, I found it difficult to construct the terms representing the context for some of the steps;
Casper Bach Poulsen provided the two largest ones.

\begin{code}
    lemma-2 : ∀ κ n ρ →
      gen κ (send′ n ρ) ≡ lookup′(suc n) κ ρ

    lemma-2 origin n ρ = refl
    lemma-2 (child c κ) n ρ =
      let π = lookup′(suc n) κ ρ in
      begin
        gen (child c κ) (send′ n ρ)
      ≡⟨⟩ -- by definition of gen
        (wrap (child c κ) ⍄ gen κ) (send′ n ρ)
      ≡⟨⟩ -- by definition of _⍄_
        (wrap (child c κ) (send′ n ρ) (gen κ (send′ n ρ))) ⊕ (gen κ (send′ n ρ))
      ≡⟨ cong (λ X → wrap (child c κ) (send′ n ρ) X ⊕ X) (lemma-2 κ n ρ) ⟩ -- by Lemma 2 and definition of π
        (wrap (child c κ) (send′ n ρ) π) ⊕ π
      ≡⟨⟩ -- by definition of _⊕_
        (from λ m → [ ( λ φ → inl φ ) , ( λ _ → to π m ) ]⊥ (to (wrap (child c κ) (send′ n ρ) π) m))
      ≡⟨⟩ -- by definition of wrap
        (from λ m → [ ( λ φ → inl φ ) , ( λ _ → to π m ) ]⊥  
          (to (from (λ m → [ ( λ e → inl(eval⟦ e ⟧ (send′ n ρ) π) ) , ( inr ⊥ ) ]? (methods (child c κ) m))) m))
      ≡⟨ cong from (ext λ x → cong (λ X → [ _ , ( λ _ → to π x ) ]⊥ (X x)) (inverseˡ refl)) ⟩ -- by to ∘ from inverse and β
        (from λ m → [ ( λ φ → inl φ ) , ( λ _ → to π m ) ]⊥  
          ( [ ( λ e → inl (eval⟦ e ⟧ (send′ n ρ) π) ) , ( inr ⊥ ) ]? (methods (child c κ) m) ))
      ≡⟨ cong from (ext λ x → [,]⊥-elim {A = Exp} {x = λ e → eval⟦ e ⟧ (send′ n ρ) π} {y = ⊥} {z = methods (child c κ) x} ) ⟩
        (from λ m → [ ( λ e → inl (eval⟦ e ⟧ (send′ n ρ) π) ) , ( to π m ) ]? (methods (child c κ) m))
      ≡⟨⟩ -- by definition of π
        (from λ m → [ ( λ e → inl (eval⟦ e ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)) ) , ( to (lookup′ (suc n) κ ρ) m ) ]? (methods (child c κ) m))
      ≡⟨ cong from (ext λ m → 
            cong (λ X → [ X , ( to (lookup′ (suc n) κ ρ) m ) ]? (methods (child c κ) m))
                (ext λ e → cong inl (sym (lemma-1 n e _ _ _))) ) ⟩
        (from λ m → [ ( λ e → inl (do′ (suc n) ⟦ e ⟧ ρ (child c κ)) ) , ( to (lookup′ (suc n) κ ρ) m ) ]? (methods (child c κ) m))
      ≡⟨⟩ -- by definition of lookup′
        lookup′ (suc n) (child c κ) ρ
      ∎
\end{code}

TODO: Improve the layout of the above proof – perhaps defining the proof steps in a where-clause?

\subsection{Lemma 3}

As with Lemma~1, this straightforward induction proof is quite concise in Agda.

\begin{code}
    _^_ : Generator → ℕ → Generator
    (f ^ zero)   x  = x
    (f ^ suc n)  x  = f((f ^ n) x)

    lemma-3 : ∀ n ρ → 
      send′ n ρ ≡ (gen(class ρ) ^ n) ⊥

    lemma-3 zero     ρ = refl
    lemma-3 (suc n)  ρ rewrite  sym (lemma-3 n ρ) | 
                                sym (lemma-2 (class ρ) n ρ) = refl
\end{code}

\subsection{Statements of Remaining Results}

The proofs of the results stated below will require further assumptions about 
the properties of Scott domains, and use of a module with laws for posets.

\begin{code}
    is-chain : {D : Domain} → (δ : ℕ → ⟨ D ⟩) → Set
    is-chain δ = ∀ n → (δ n) ⊑ (δ (suc n))

    lemma-4 :
      ( ∀ ρ → is-chain (λ n → send′ n ρ) )          × 
      ( ∀ κ ρ → is-chain (λ n → lookup′ n κ ρ) )    × 
      ( ∀ e ρ κ → is-chain (λ n → do′ n ⟦ e ⟧ ρ κ) )
    lemma-4 =  (λ ρ n → {!   !}) , 
               (λ κ ρ n → {!   !}) , 
               (λ e ρ κ n → {!   !})

    interpret : Instance → ⟨ Behavior ⟩
    interpret ρ = lub (λ n → send′ n ρ)

    proposition-1 : ∀ ρ → interpret ρ ≡ behave ρ
    proposition-1 ρ = {!   !}

    proposition-2 : ∀ ρ → behave ρ ⊑ send ρ
    proposition-2 ρ = {!   !}

    proposition-3 : ∀ ρ → send ρ ⊑ interpret ρ
    proposition-3 ρ = {!   !}

    theorem-1 : ∀ ρ → send ρ ≡ behave ρ
    theorem-1 ρ = {!   !}
\end{code}
\end{AgdaAlign} 