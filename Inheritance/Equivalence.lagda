
\section{Equivalence}
\label{sec:proofs}

This section presents the verified Agda proofs of the first three lemmas from CP89,
using the definitions presented in \ref{sec:semantic-definitions}.
Development of Agda proofs of the remaining results is left to future work.

\begin{code}
{-# OPTIONS --safe #-}
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
    {G′ : Domain}
    {{ isoᵍ : ⟨ G′ ⟩ ↔ D′ }}

    {ext : Extensionality lzero lzero}       -- function extensionality
  where
  open Semantics {class} {methods′} {G′} {{isoᵍ}}
\end{code}

\subsection{Lemma 1}

The proof of this lemma is a straightforward structural induction.
It can be defined much more concisely in Agda:
the cases for self, super, and arg can simply be replaced by "refl".

\begin{code}
  lemma-1 : ∀ n e ρ c κ →
    do′ (suc n) ⟦ e ⟧ ρ (child c κ) ≡  eval⟦ e ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)

  lemma-1 n self ρ c κ =                                -- refl
    begin
      do′ (suc n) ⟦ self ⟧ ρ (child c κ)
    ≡⟨⟩
      ( from λ α → from (inl (send′ n ρ)) )
    ≡⟨⟩
      eval⟦ self ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)
    ∎
  lemma-1 n super ρ c (child c′ κ) =                    -- refl
    begin
      do′ (suc n) ⟦ super ⟧ ρ (child c (child c′ κ))
    ≡⟨⟩
      ( from λ α → from (inl (lookup′ (suc n) (child c′ κ) ρ)) )
    ≡⟨⟩
      eval⟦ super ⟧ (send′ n ρ) (lookup′ (suc n) (child c′ κ) ρ)
    ∎
  lemma-1 n super ρ c origin =                          -- refl
    begin
      do′ (suc n) ⟦ super ⟧ ρ (child c origin)
    ≡⟨⟩
      ( from λ α → from (inl ⊥ ) )
    ≡⟨⟩
      eval⟦ super ⟧ (send′ n ρ) (lookup′ (suc n) origin ρ)
    ∎
  lemma-1 n arg ρ c κ =                                 -- refl
    begin
      do′ (suc n) ⟦ arg ⟧ ρ (child c κ)
    ≡⟨⟩
      ( from λ α → α )
    ≡⟨⟩
      eval⟦ arg ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)
    ∎
  lemma-1 n (call e₁ m e₂) ρ c κ rewrite (lemma-1 n e₁ ρ c κ) rewrite (lemma-1 n e₂ ρ c κ) = refl
  -- lemma-1 n (appl f e₁) ρ c κ rewrite (lemma-1 n e₁ ρ c κ) = refl
  lemma-1 n (appl f e₁) ρ c κ =
    begin 
      do′ (suc n) ⟦ appl f e₁ ⟧ ρ (child c κ)
    ≡⟨⟩
      ( from λ α → apply⟦ f ⟧ (to (do′ (suc n) ⟦ e₁ ⟧ ρ (child c κ)) α) )
    ≡⟨ use-induction ⟩ 
      ( from λ α → apply⟦ f ⟧ (to (eval⟦ e₁ ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)) α) )
    ≡⟨⟩
      eval⟦ appl f e₁ ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)
    ∎
    where
      use-induction =
        cong from 
          (ext λ α → cong (λ X → apply⟦ f ⟧ ((to X) α)) (lemma-1 n e₁ ρ c κ))
\end{code}

\subsection{Lemma 2}

The proof of this lemma exhibits the same steps of equational reasoning as the corresponding proof in CP89.
As a novice user of Agda, I found it difficult to construct the terms representing the context for some of the steps;
Casper Bach Poulsen provided the two largest ones.

\begin{code}
  module _
    -- For Lemma 2:
      {[,]⊥-elim :                      -- [,]⊥-elim eliminates an application of [ f , g ]⊥
        {D E F : Domain} {A : Set}
        {f : ⟨ D ⟩ → ⟨ F ⟩} {g : ⟨ E ⟩ → ⟨ F ⟩}
        {x : A → ⟨ D ⟩} {y : ⟨ E ⟩} {z : A +?} →
          [ f , g ]⊥ ( [ ( inl ∘ x ) , ( inr y ) ]? z ) ≡ [ ( f ∘ x ) , ( g y ) ]? z}

    -- For Lemma 4:
      {⊥-is-least : {D : Domain} {x : ⟨ D ⟩} → ⊥ ⊑ x}
      {⊑-is-transitive : {D : Domain} {x y z : ⟨ D ⟩} → x ⊑ y → y ⊑ z → x ⊑ z}
      {is-assumed-monotone :
        {D E : Domain} (f : ⟨ D ⟩ → ⟨ E ⟩) (x y : ⟨ D ⟩) → (x ⊑ y) → (f x ⊑ f y)}
      {is-assumed-monotone-2 :
        {D E F : Domain} (f : ⟨ D ⟩ → ⟨ E ⟩ → ⟨ F ⟩) (x y : ⟨ D ⟩) → (x ⊑ y) → ({z : ⟨ E ⟩} → (f x z ⊑ f y z))}
       
    where

    lemma-2 : ∀ κ n ρ →
      gen κ (send′ n ρ) ≡ lookup′ (suc n) κ ρ

    lemma-2 origin n ρ =
      begin
        gen origin (send′ n ρ)
      ≡⟨⟩
        ⊥
      ≡⟨⟩
        lookup′ (suc n) origin ρ
      ∎
    lemma-2 (child c κ) n ρ =
      let π = lookup′ (suc n) κ ρ in
      begin
        gen (child c κ) (send′ n ρ)
      ≡⟨⟩ -- use definition of gen
        (wrap (child c κ) ⍄ gen κ) (send′ n ρ)
      ≡⟨⟩ -- use definition of _⍄_
        (wrap (child c κ) (send′ n ρ) (gen κ (send′ n ρ))) ⊕ (gen κ (send′ n ρ))
      ≡⟨ use-lemma-2 ⟩
        (wrap (child c κ) (send′ n ρ) π) ⊕ π
      ≡⟨⟩ -- use definition of _⊕_
        (from λ m →
          [ ( λ φ → inl φ ) , ( λ _ → to π m ) ]⊥
          (to (wrap (child c κ) (send′ n ρ) π) m))
      ≡⟨⟩ -- use definition of wrap
        (from λ m → 
          [ ( λ φ → inl φ ) , ( λ _ → to π m ) ]⊥  
          (to (from (λ m → 
            [ ( λ e → inl(eval⟦ e ⟧ (send′ n ρ) π) ) , ( inr ⊥ ) ]?
            (methods (child c κ) m))) m))
      ≡⟨ use-to∘from-inverse ⟩
        (from λ m →
          [ ( λ φ → inl φ ) , ( λ _ → to π m ) ]⊥  
          ( [ ( λ e → inl (eval⟦ e ⟧ (send′ n ρ) π) ) , ( inr ⊥ ) ]? (methods (child c κ) m) ))
      ≡⟨ use-[,]⊥-elim ⟩
        (from λ m → 
          [ ( λ e → inl (eval⟦ e ⟧ (send′ n ρ) π) ) ,
            ( to π m ) ]? (methods (child c κ) m))
      ≡⟨⟩ -- use definition of π
        (from λ m →
          [ ( λ e → inl (eval⟦ e ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)) ) , 
            ( to (lookup′ (suc n) κ ρ) m ) ]? (methods (child c κ) m))
      ≡⟨ use-lemma-1 ⟩
        (from λ m →
          [ ( λ e → inl (do′ (suc n) ⟦ e ⟧ ρ (child c κ)) ) , 
            ( to (lookup′ (suc n) κ ρ) m ) ]? (methods (child c κ) m))
      ≡⟨⟩ -- use definition of lookup′
        lookup′ (suc n) (child c κ) ρ
      ∎
      where
        π′ = -- TODO: how to refer to π instead of π′?
          lookup′(suc n) κ ρ
        use-lemma-2 =
          cong (λ X → wrap (child c κ) (send′ n ρ) X ⊕ X) (lemma-2 κ n ρ)
        use-to∘from-inverse =
          cong from (ext λ x → 
            cong (λ X → [ _ , ( λ _ → to π′ x ) ]⊥ (X x)) (inverseˡ refl))
        use-[,]⊥-elim =
          cong from (ext λ x → 
            [,]⊥-elim {A = Exp} {x = λ e → eval⟦ e ⟧ (send′ n ρ) π′} {y = ⊥} {z = methods (child c κ) x})
        use-lemma-1 =
          cong from (ext λ m → 
            cong (λ X → [ X , ( to (lookup′ (suc n) κ ρ) m ) ]? (methods (child c κ) m))
                (ext λ e → cong inl (sym (lemma-1 n e _ _ _))))
\end{code}

\subsection{Lemma 3}

\begin{code}
    iter : {D : Domain} → ℕ → (⟨ D ⟩ → ⟨ D ⟩) → ⟨ D ⟩
    iter zero g     = ⊥
    iter (suc n) g  = g (iter n g)

    lemma-3 : ∀ n ρ → 
      iter n (gen (class ρ)) ≡ send′ n ρ

    lemma-3 zero ρ =
      begin
        iter zero (gen (class ρ))
      ≡⟨⟩ 
        ⊥
      ≡⟨⟩ 
        send′ zero ρ
      ∎
    lemma-3 (suc n) ρ  =
      begin
        iter (suc n) (gen (class ρ))
      ≡⟨⟩
        gen (class ρ) (iter n (gen (class ρ)))
      ≡⟨ use-induction ⟩ 
        gen (class ρ) (send′ n ρ)
      ≡⟨ lemma-2 (class ρ) n ρ ⟩
        lookup′(suc n) (class ρ) ρ
      ≡⟨⟩
        send′ (suc n) ρ
      ∎
      where
        use-induction = cong (λ X → gen (class ρ) X) (lemma-3 n ρ)
\end{code}

\subsection{Lemma 4}

\begin{code}
    -- is-chain : {D : Domain} → (δ : ℕ → ⟨ D ⟩) → Set
    -- is-chain δ = ∀ n → (δ n) ⊑ (δ (suc n))

    iter-is-chain : {D : Domain} (n : ℕ) (g : ⟨ D ⟩ → ⟨ D ⟩) → iter n g ⊑ iter (suc n) g
    iter-is-chain zero g = ⊥-is-least
    iter-is-chain (suc n) g =
      is-assumed-monotone g (iter n g) (iter (suc n) g) (iter-is-chain n g)

    lemma-4-send′ : ∀ n ρ → send′ n ρ ⊑ send′ (suc n) ρ
    lemma-4-send′ n ρ 
      rewrite sym (lemma-3 n ρ)
      rewrite sym (lemma-3 (suc n) ρ) =
        iter-is-chain n (gen (class ρ))

    lemma-4-lookup′ : ∀ n κ ρ → lookup′ n κ ρ ⊑ lookup′ (suc n) κ ρ
    lemma-4-lookup′ zero κ ρ = ⊥-is-least
    lemma-4-lookup′ (suc n) κ ρ
      rewrite sym (lemma-2 κ n ρ)
      rewrite sym (lemma-2 κ (suc n) ρ) =
        is-assumed-monotone (gen κ) (send′ n ρ) (send′ (suc n) ρ) (lemma-4-send′ n ρ)

    lemma-4-do′ : ∀ n e ρ c κ →
      do′ (suc n) ⟦ e ⟧ ρ (child c κ) ⊑ do′ (suc (suc n)) ⟦ e ⟧ ρ (child c κ)
    lemma-4-do′ n e ρ c κ                -- do′ (suc n) ⟦ e ⟧ ρ (child c κ) ⊑ do′ (suc (suc n)) ⟦ e ⟧ ρ (child c κ)
      rewrite (lemma-1 (suc n) e ρ c κ)  -- eval⟦ e ⟧ (send′ (suc n) ρ) (lookup′ (suc (suc n))  κ ρ)
      rewrite (lemma-1 n e ρ c κ)        -- eval⟦ e ⟧ (send′ n       ρ) (lookup′ (suc n)        κ ρ)
      = ⊑-is-transitive
          (is-assumed-monotone-2 (eval⟦ e ⟧) (send′ n ρ) (send′ (suc n) ρ)
            (lemma-4-send′ n ρ))
          (is-assumed-monotone (eval⟦ e ⟧ (send′ (suc n) ρ)) (lookup′ (suc n) κ ρ) (lookup′ (suc (suc n)) κ ρ)
            (lemma-4-lookup′ (suc n) κ ρ))
\end{code}

In equational reasoning style, it would be:

begin
  do′ (suc n) ⟦ e ⟧ ρ κ
≡⟨ lemma-1 (suc n) e ρ c κ ⟩
  eval⟦ e ⟧ (send′ n ρ)       (lookup′ (suc n) κ ρ)
⊑⟨ is-assumed-monotone (eval⟦ e ⟧) (send′ n ρ) (send′ (suc n) ρ)
     (lemma-4-send′ n ρ) ⟩
  eval⟦ e ⟧ (send′ (suc n) ρ) (lookup′ (suc n) κ ρ)
⊑⟨ is-assumed-monotone (eval⟦ e ⟧ (send′ (suc n) ρ)) (lookup′ (suc n) κ ρ) (lookup′ (suc (suc n)) κ ρ)
     (lemma-4-lookup′ (suc n) κ ρ) ⟩
  eval⟦ e ⟧ (send′ (suc n) ρ) (lookup′ (suc (suc n)) κ ρ)
≡⟨ sym (lemma-1 (suc (suc n)) e ρ c κ) ⟩
  do′ (suc (suc n)) ⟦ e ⟧ ρ κ
∎

\subsection{Statements of Remaining Results}

\begin{code}
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