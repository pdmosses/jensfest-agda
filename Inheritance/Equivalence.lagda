\subsection{Intermediate Semantics}
%
\begin{AgdaAlign}
\begin{code}[hide]
{-# OPTIONS --allow-unsolved-metas #-}
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
  using (to; from; inverseˡ)      -- to from     ~ implicit
\end{code}%
\begin{code}
module Inheritance.Equivalence
\end{code}%
%
The imports and parameters of this module are the same as those of
\AgdaCode[\AgdaModule{Inheritance.Definitions}]
{Inheritance.Definitions},
and elided here.
%
\newcommand{\EquivalenceParameters}{
\begin{code}
    ( Domain  :  Set₁ )                                     
    ( ⟨_⟩     :  Domain → Set )                             
    ( _⊑_     :  {D : Domain} → ⟨ D ⟩ → ⟨ D ⟩ → Set )
    ( ⊥       :  {D : Domain} → ⟨ D ⟩ )                     
    ( fix     :  {D : Domain} → ( ⟨ D ⟩ → ⟨ D ⟩ ) → ⟨ D ⟩ ) 
    ( ?⊥      :  Domain )                             
    ( _+⊥_    :  Domain → Domain → Domain )           
    ( inl     :  {D E : Domain} → ⟨ D ⟩ → ⟨ D +⊥ E ⟩ )
    ( inr     :  {D E : Domain} → ⟨ E ⟩ → ⟨ D +⊥ E ⟩ )
    ( [_,_]⊥  :  {D E F : Domain} →                   
                   ( ⟨ D ⟩ → ⟨ F ⟩ ) → ( ⟨ E ⟩ → ⟨ F ⟩ ) →
                   ⟨ D +⊥ E ⟩ → ⟨ F ⟩ )
    ( Instance   : Set )        -- objects
    ( Name       : Set )        -- class names
    ( Key        : Set )        -- method names
    ( Primitive  : Set )        -- function names
    ( Number    : Domain )      -- unspecified
    ( Value     : Domain )      -- a value is a behavior or a number
    ( Behavior  : Domain )      -- a behavior maps keys to funs
    ( Fun       : Domain )      -- a fun maps values to values
    {{ isoᵛ     : ⟨ Value ⟩     ↔  ⟨ Behavior +⊥ Number ⟩     }}
    {{ isoᵇ     : ⟨ Behavior ⟩  ↔  ( Key → ⟨ Fun +⊥ ?⊥ ⟩ )    }}
    {{ isoᶠ     : ⟨ Fun ⟩       ↔  ( ⟨ Value ⟩ → ⟨ Value ⟩ )  }}
    ( apply⟦_⟧  : Primitive → ⟨ Value ⟩ → ⟨ Value ⟩ )
\end{code}}%
\begin{code}
  where
open import Inheritance.Definitions
    ( Domain ) ( ⟨_⟩ ) ( ⊥ ) ( fix ) ( ?⊥ )
    ( _+⊥_ ) ( inl ) ( inr ) ( [_,_]⊥ )
    ( Instance ) ( Name ) ( Key ) ( Primitive )
    ( Number ) ( Value ) ( Behavior ) ( Fun )
    {{ isoᵛ }} {{ isoᵇ }} {{ isoᶠ }} ( apply⟦_⟧ )

module _ 
    ( class     : Instance → Class )
    ( methods′  : Class → Key → (Exp +?) )
  where
  open Semantics ( class ) ( methods′ )
\end{code}
%
The intermediate semantics of method expressions given in CP89
is a step-indexed variant of the method lookup semantics.
It takes an extra argument $n$ ranging over \textbf{Nat} (the set of natural numbers),
which acts as sufficient `fuel' for up to $n-1$ uses of \textbf{self}:
when $n$ is zero, the intermediate semantics is the undefined behavior ($\bot$).
One of the lemmas proved in CP89 shows that the intermediate semantics at $n$
corresponds to the $n$th approximation to the denotational semantics.

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

  lookup′ zero κ ρ = ⊥
  lookup′ n (child c κ) ρ =
    from λ m → [ ( λ e → inl (do′ n ⟦ e ⟧ ρ (child c κ)) ) ,
                 ( to (lookup′ n κ ρ ) m )
               ]? (methods (child c κ) m)
  lookup′ n origin ρ = ⊥
\end{code}
%
Cases of Agda definitions are sequential:
putting a case for \AgdaCode[\AgdaInductiveConstructor{zero}]
{zero}
before the corresponding case for \AgdaCode[\AgdaBound{n}]
{n}
implies that \AgdaCode[\AgdaBound{n}]
{n} is positive in the latter.
%
\begin{code}
  do′ zero     ⟦ e     ⟧ ρ κ = ⊥

  do′ (suc n)  ⟦ self  ⟧ ρ κ = from λ α → from (inl (send′ n ρ))

  do′ n ⟦ super ⟧ ρ (child c κ) =
    from λ α → from (inl (lookup′ n κ ρ))
  do′ n ⟦ super ⟧ ρ origin = from λ α → ⊥
  do′ n ⟦ arg   ⟧ ρ κ = from λ α → α
  do′ n ⟦ call e₁ m e₂ ⟧ ρ κ =
    from λ α → [ ( λ σ → [ ( λ φ → to φ (to (do′ n ⟦ e₂ ⟧ ρ κ) α) ) ,
                           ( λ _ →  ⊥ )
                         ]⊥ (to σ m) ) ,
                 ( λ ν → ⊥ )
               ]⊥ (to (to (do′ n ⟦ e₁ ⟧ ρ κ ) α))
  do′ n ⟦ appl f e₁ ⟧ ρ κ =
    from λ α → apply⟦ f ⟧ (to (do′ n ⟦ e₁ ⟧ ρ κ) α)
\end{code}

\subsection{Proofs of Lemmas in Agda}

The proofs of the lemmas use the following additional modules from the standard library:
%
%  -- TODO: use Reasoning.PartialOrder instead of ≡-Reasoning
%  -- open import Relation.Binary.Core using (Rel; _⇒_)
%  -- open import Relation.Binary.Bundles using (Poset; Setoid)
%  -- open import Relation.Binary.Definitions using (Transitive; Antisymmetric)
%  -- import Relation.Binary.Reasoning.PartialOrder as ⊑-Reasoning renaming (_≤_ to _⊑_)
%  -- open ⊑-Reasoning P -- requires ⟨ D ⟩ to be viewed as P.Carrier where P : Poset _ _ _
%
\begin{code}
  open import Relation.Binary.PropositionalEquality.Core
    using (_≡_; refl; cong; sym)
  open import Relation.Binary.PropositionalEquality.Properties
  open import Relation.Binary.Reasoning.Syntax
  open ≡-Reasoning
  open import Axiom.Extensionality.Propositional
    using (Extensionality)
  open import Level
    renaming (zero to lzero) hiding (suc)

  module _ ( ext : Extensionality lzero lzero )
    where
\end{code}

Lemma~1 establishes a significant fact about the relationship
between the denotational semantics and the intermediate semantics of method systems.
Its Agda proof exhibits the equational reasoning steps of the original proof in CP89.
This checks the correctness not only of the stated result, but also of the steps themselves.

The Agda standard library defines the following notation for equational reasoning:
\begin{itemize}
\item \AgdaCode[\AgdaBound{x}\AgdaSpace{}%
\AgdaOperator{\AgdaDatatype{≡}}\AgdaSpace{}%
\AgdaBound{y}]
{x ≡ y} asserts the equality of \AgdaCode[\AgdaBound{x}]
{x} and \AgdaCode[\AgdaBound{y}]
{y};
\item \AgdaCode[\AgdaOperator{\AgdaFunction{begin}}]
{begin} starts a proof;
\item \AgdaCode[\AgdaFunction{≡⟨⟩}]
{≡⟨⟩} adds a step that Agda can check automatically;
\item \AgdaCode[\AgdaFunction{≡⟨}\AgdaSpace{}%
\AgdaBound{t}\AgdaSpace{}%
\AgdaFunction{⟩}]
{≡⟨ t ⟩} adds a step with an explicit proof term \AgdaCode[\AgdaBound{t}]
{t};
and
\item \AgdaCode[\AgdaOperator{\AgdaFunction{∎}}]
{∎} concludes a proof.
\end{itemize}

\begin{code}
    lemma-1 : ∀ n e ρ c κ →
      do′ (suc n) ⟦ e ⟧ ρ (child c κ) ≡
      eval⟦ e ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)
\end{code}
%
The restriction to the class \AgdaCode[\AgdaInductiveConstructor{child}\AgdaSpace{}%
\AgdaBound{c}\AgdaSpace{}%
\AgdaBound{κ}]
{child c κ} ensures that it is not the root class;
in CP89, the use of $\textit{parent}(κ)$ as an argument of type \textbf{Class}
in the statement of Lemma~1 leaves this restriction implicit.

The proof of this lemma is a straightforward structural induction:

\begin{code}
    lemma-1 n self ρ c κ =
      begin  do′ (suc n) ⟦ self ⟧ ρ (child c κ)
      ≡⟨⟩    ( from λ α → from (inl (send′ n ρ)) )
      ≡⟨⟩    eval⟦ self ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)
      ∎
    lemma-1 n super ρ c (child c′ κ) =
      begin  do′ (suc n) ⟦ super ⟧ ρ (child c (child c′ κ))
      ≡⟨⟩    ( from λ α → from (inl (lookup′ (suc n) (child c′ κ) ρ)) )
      ≡⟨⟩    eval⟦ super ⟧ (send′ n ρ) (lookup′ (suc n) (child c′ κ) ρ)
      ∎
    lemma-1 n super ρ c origin =
      begin  do′ (suc n) ⟦ super ⟧ ρ (child c origin)
      ≡⟨⟩    ( from λ α → from (inl ⊥ ) )
      ≡⟨⟩    eval⟦ super ⟧ (send′ n ρ) (lookup′ (suc n) origin ρ)
      ∎
    lemma-1 n arg ρ c κ =
      begin  do′ (suc n) ⟦ arg ⟧ ρ (child c κ)
      ≡⟨⟩    ( from λ α → α )
      ≡⟨⟩    eval⟦ arg ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)
      ∎
\end{code}
%
The equational reasoning proof steps in the inductive case for calling a method
are quite complicated in Agda.
This is mainly due to the case analysis required in the semantics of method calls
to make the semantics type-correct
(these cases are left implicit in CP89).
The use of \AgdaCode[\AgdaKeyword{rewrite}]
{rewrite} below succinctly verifies the correctness of the case analysis:
%
\begin{code}
    lemma-1 n (call e₁ m e₂) ρ c κ
      rewrite (lemma-1 n e₁ ρ c κ)
      rewrite (lemma-1 n e₂ ρ c κ) = refl
\end{code}
%
The inductive case for applying a primitive function is relatively simple,
and concludes the proof of Lemma 1.
%
\begin{code}
    lemma-1 n (appl f e₁) ρ c κ =
      begin
        do′ (suc n) ⟦ appl f e₁ ⟧ ρ (child c κ)
      ≡⟨⟩
        ( from λ α →
            apply⟦ f ⟧
              (to (do′ (suc n) ⟦ e₁ ⟧ ρ (child c κ)) α) )
      ≡⟨ use-induction ⟩ 
        ( from λ α →
            apply⟦ f ⟧
              (to (eval⟦ e₁ ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)) α) )
      ≡⟨⟩
        eval⟦ appl f e₁ ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)
      ∎
      where
        use-induction =
          cong from (ext λ α →
            cong (λ X →
              apply⟦ f ⟧ ((to X) α)) (lemma-1 n e₁ ρ c κ))
\end{code}
\end{AgdaAlign}%
%
The Agda proofs of the remaining lemmas are available in the accompanying auxiliary material.
%
\newcommand{\LemmaTwo}{
\subsection*{Lemma 2}

The proof of this lemma exhibits the same steps of equational reasoning
as the corresponding proof in CP89.%
\footnote{As a novice user of Agda, I found it difficult to construct the terms
representing the context for some of the steps;
Casper Bach Poulsen provided the two largest ones.}
%
\begin{code}
    module _
        ( [,]⊥-elim : -- [,]⊥-elim eliminates an application of [ f , g ]⊥
            {D E F : Domain} {A : Set}
            {f : ⟨ D ⟩ → ⟨ F ⟩} {g : ⟨ E ⟩ → ⟨ F ⟩}
            {x : A → ⟨ D ⟩} {y : ⟨ E ⟩} {z : A +?} →
              [ f , g ]⊥ ( [ ( inl ∘ x ) , ( inr y ) ]? z ) ≡ [ ( f ∘ x ) , ( g y ) ]? z )
      where
\end{code}
}%
\begin{code}
      lemma-2 : ∀ κ n ρ → gen κ (send′ n ρ) ≡ lookup′ (suc n) κ ρ
\end{code}
%
\newcommand{\LemmaTwoProof}{
\begin{code}
      -- lemma-2 : ∀ κ n ρ → gen κ (send‵′ n ρ) ≡ lookup′ (suc n) κ ρ

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
}%
\newcommand{\LemmaThree}{
\subsection*{Lemma 3}
}%
\begin{code}
      iter : {D : Domain} → ℕ → ( ⟨ D ⟩ → ⟨ D ⟩ ) → ⟨ D ⟩
      iter zero g     = ⊥
      iter (suc n) g  = g (iter n g)

      lemma-3 : ∀ n ρ → iter n (gen (class ρ)) ≡ send′ n ρ
\end{code}
%
\newcommand{\LemmaThreeProof}{
\begin{code}
      -- lemma-3 : ∀ n ρ → iter n (gen (class ρ)) ≡ send‵′ n ρ

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
}%
\newcommand{\LemmaFour}{
\subsection*{Lemma 4}

\begin{code}
      module _
          ( ⊥-is-least : {D : Domain} {x : ⟨ D ⟩}           → ⊥ ⊑ x )
          ( ⊑-is-reflexive : {D : Domain} {x y : ⟨ D ⟩}       → x ≡ y → x ⊑ y )
          ( ⊑-is-transitive : {D : Domain} {x y z : ⟨ D ⟩}  → x ⊑ y → y ⊑ z → x ⊑ z )
          ( is-assumed-monotone :
            {D E : Domain} (f : ⟨ D ⟩ → ⟨ E ⟩) (x y : ⟨ D ⟩) →
              (x ⊑ y) → (f x ⊑ f y) )
          ( is-assumed-monotone-2 :
            {D E F : Domain} (f : ⟨ D ⟩ → ⟨ E ⟩ → ⟨ F ⟩) (x y : ⟨ D ⟩) →
              (x ⊑ y) → ({z : ⟨ E ⟩} → (f x z ⊑ f y z)) )
        where
        -- 
        begin-⊑_ : {D : Domain} → {x y : ⟨ D ⟩ } → x ⊑ y → x ⊑ y
        begin-⊑ p = p
        _∎-⊑ : {D : Domain} → (x : ⟨ D ⟩ ) → x ⊑ x
        x ∎-⊑ = ⊑-is-reflexive refl
        _⊑⟨_⟩_ : {D : Domain} → (x : ⟨ D ⟩ ) → {y z : ⟨ D ⟩ } → x ⊑ y → y ⊑ z → x ⊑ z
        x ⊑⟨ p ⟩ q = ⊑-is-transitive p q
        _≡⊑⟨_⟩_ : {D : Domain} → (x : ⟨ D ⟩ ) → {y z : ⟨ D ⟩ } → x ≡ y → y ⊑ z → x ⊑ z
        x ≡⊑⟨ p ⟩ q =   ⊑-is-transitive (⊑-is-reflexive p) q
        _⊑≡⟨_⟩_ : {D : Domain} → (x : ⟨ D ⟩ ) → {y z : ⟨ D ⟩ } → x ⊑ y → y ≡ z → x ⊑ z
        x ⊑≡⟨ p ⟩ q =   ⊑-is-transitive p (⊑-is-reflexive q)
        _⊑⟨⟩_ : {D : Domain} → (x : ⟨ D ⟩ ) → {y : ⟨ D ⟩ } → x ⊑ y → x ⊑ y
        x ⊑⟨⟩ q = x ⊑⟨ ⊑-is-reflexive refl ⟩ q
        infix  1 begin-⊑_
        infixr 2 _⊑⟨_⟩_
        infixr 2 _⊑≡⟨_⟩_
        infixr 2 _≡⊑⟨_⟩_
        infixr 2 _⊑⟨⟩_
        infix  3 _∎-⊑

        -- is-chain : {D : Domain} → (δ : ℕ → ⟨ D ⟩) → Set
        -- is-chain δ = ∀ n → (δ n) ⊑ (δ (suc n))

        iter-is-chain : {D : Domain} (n : ℕ) (g : ⟨ D ⟩ → ⟨ D ⟩) → iter n g ⊑ iter (suc n) g
        iter-is-chain zero g = ⊥-is-least
        iter-is-chain (suc n) g =
          is-assumed-monotone g (iter n g) (iter (suc n) g) (iter-is-chain n g)
\end{code}
}%
\begin{code}
        lemma-4-send′ : ∀ n ρ →
          send′ n ρ ⊑ send′ (suc n) ρ
\end{code}
%
\newcommand{\LemmaFourSendProof}{
\begin{code}
        -- lemma-4-send‵′ : ∀ n ρ → 
        --   send‵′ n ρ ⊑ send‵′ (suc n) ρ

        lemma-4-send′ n ρ 
          rewrite sym (lemma-3 n ρ)
          rewrite sym (lemma-3 (suc n) ρ) =
            iter-is-chain n (gen (class ρ))
\end{code}
}%
\begin{code}
        lemma-4-lookup′ : ∀ n κ ρ →
          lookup′ n κ ρ ⊑ lookup′ (suc n) κ ρ
\end{code}
%
\newcommand{\LemmaFourLookupProof}{
\begin{code}
        -- lemma-4-lookup′ : ∀ n κ ρ → 
        --   lookup′ n κ ρ ⊑ lookup′ (suc n) κ ρ

        lemma-4-lookup′ zero κ ρ = ⊥-is-least
        lemma-4-lookup′ (suc n) κ ρ
          rewrite sym (lemma-2 κ n ρ)
          rewrite sym (lemma-2 κ (suc n) ρ) =
            is-assumed-monotone (gen κ) (send′ n ρ) (send′ (suc n) ρ) (lemma-4-send′ n ρ)
\end{code}
}%
\begin{code}
        lemma-4-do′ : ∀ n e ρ c κ →
          do′ (suc n) ⟦ e ⟧ ρ (child c κ) ⊑
          do′ (suc (suc n)) ⟦ e ⟧ ρ (child c κ)
\end{code}
%
\newcommand{\LemmaFourDoProof}{
\begin{code}
        -- lemma-4-do′ : ∀ n e ρ c κ →
        --   do′ (suc n) ⟦ e ⟧ ρ (child c κ) ⊑ 
        --   do′ (suc (suc n)) ⟦ e ⟧ ρ (child c κ)

        lemma-4-do′ n e ρ c κ =
          begin-⊑
            do′ (suc n) ⟦ e ⟧ ρ (child c κ)
          ≡⊑⟨ lemma-1 n e ρ c κ ⟩
            eval⟦ e ⟧ (send′ n ρ) (lookup′ (suc n) κ ρ)
          ⊑⟨ is-assumed-monotone-2 (eval⟦ e ⟧)
               (send′ n ρ) (send′ (suc n) ρ)
               (lemma-4-send′ n ρ) ⟩
            eval⟦ e ⟧ (send′ (suc n) ρ) (lookup′ (suc n) κ ρ)
          ⊑⟨ is-assumed-monotone (eval⟦ e ⟧ (send′ (suc n) ρ))
               (lookup′ (suc n) κ ρ) (lookup′ (suc (suc n)) κ ρ)
               (lemma-4-lookup′ (suc n) κ ρ) ⟩
            eval⟦ e ⟧ (send′ (suc n) ρ) (lookup′ (suc (suc n)) κ ρ)
          ≡⊑⟨ sym (lemma-1 (suc n) e ρ c κ) ⟩
            do′ (suc (suc n)) ⟦ e ⟧ ρ (child c κ)
          ∎-⊑
\end{code}
}

\subsection{Remaining Results}

When Agda proofs of the remaining propositions and correctness theorem from CP89
have been developed, they are to be made available at
\url{https://github.com/pdmosses/jensfest-agda}.

\begin{code}
        module _
            { Gᵍ : Domain }
            {{ isoᵍ : ⟨ Gᵍ ⟩ ↔ Dᵍ }}
            ( lub   :  {D : Domain} → (δ : ℕ → ⟨ D ⟩) → ⟨ D ⟩ )
          where

          interpret : Instance → ⟨ Behavior ⟩
          interpret ρ = lub (λ n → send′ n ρ)

          proposition-1 :  ∀ ρ → interpret ρ ≡ behave ρ
          proposition-2 :  ∀ ρ → behave ρ ⊑ send ρ
          proposition-3 :  ∀ ρ → send ρ ⊑ interpret ρ
          theorem-1 :      ∀ ρ → send ρ ≡ behave ρ
\end{code}
\begin{code}[hide]
          proposition-1 ρ = {!   !}
          proposition-2 ρ = {!   !}
          proposition-3 ρ = {!   !}
          theorem-1 ρ = {!   !}
\end{code}
