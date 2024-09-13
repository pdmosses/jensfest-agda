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
\clearpage
\begin{code}
module Inheritance.Definitions
    ( Domain  :  Set₁ )                                     
    ( ⟨_⟩     :  Domain → Set )                             
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
  where
variable ρ : Instance; m : Key; f : Primitive; ν : ⟨ Number ⟩
variable α : ⟨ Value ⟩; σ π : ⟨ Behavior ⟩; φ : ⟨ Fun ⟩

data Class : Set where
  child   : Name → Class → Class  -- a subclass
  origin  : Class                 -- the root class
variable κ : Class

data Exp : Set where
  self   : Exp                    -- current object behavior
  super  : Exp                    -- superclass behavior
  arg    : Exp                    -- method argument value
  call   : Exp → Key → Exp → Exp  -- call method with argument
  appl   : Primitive → Exp → Exp  -- apply primitive to value
variable e : Exp
\end{code}
\clearpage
\begin{code}
module Semantics
    ( class     : Instance → Class )        -- the class of an object
    ( methods′  : Class → Key → (Exp +?) )  -- the methods of a class
  where
  methods : Class → Key → (Exp +?)          -- no root class methods
  methods (child c κ) m  = methods′ (child c κ) m
  methods origin m       = ??
\end{code}

%\clearpage
\subsection*{Method Lookup Semantics}

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

      send : Instance → ⟨ Behavior ⟩
      send ρ = l (class ρ) ρ

      lookup : Class → Instance → ⟨ Behavior ⟩
      lookup (child c κ) ρ = 
        from λ m →  [  ( λ e → inl (d⟦ e ⟧ ρ (child c κ)) ) ,
                       ( to (l κ ρ) m )
                    ]? (methods (child c κ) m)
      lookup origin ρ = ⊥

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
\clearpage
\begin{code}
    γ : ⟨ Gᵍ ⟩ → ⟨ Gᵍ ⟩
    γ = from ∘ g ∘ to
    send     = proj₁ (to (fix γ))
    lookup   = proj₁ (proj₂ (to (fix γ)))
    do⟦_⟧    = proj₂ (proj₂ (to (fix γ)))
\end{code}

%\clearpage
\subsection*{Denotational Semantics}

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
