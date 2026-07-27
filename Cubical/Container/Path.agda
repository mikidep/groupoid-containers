-- {-# OPTIONS --allow-unsolved-metas #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Path
open import Cubical.Container.Base
open import Prelude.Shapes

module Cubical.Container.Path where

module _ {F G : Container} {α β : F ⇒ G} where
  open Container F
  open Container G renaming
    (
      S to S′
    ; P to P′
    )
  open _⇒_ α
  open _⇒_ β renaming
    (
      σ to σ′
    ; π to π′
    )

  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Equiv.Properties

  CMor≡′ : (∀ (s : S) → _,_ {B = λ s′ → P′ s′ → P s} (σ s) (π s) ≡ (σ′ s , π′ s))
    → α ≡ β
  CMor≡′ htpy = equivFun (congEquiv CMor′≃CMor) (funExt htpy)

module _ {F G : Container} {α β γ δ : F ⇒ G} 
  {αβ : α ≡ β}
  {γδ : γ ≡ δ}
  {αγ : α ≡ γ}
  {βδ : β ≡ δ} 
  where

  private module F = Container F
  open _⇒_

  CMor□′ :
    ((s : F.S) 
      → let f = λ (ξ : F ⇒ G) → CMor′⁻ ξ s
      in Square (cong f αβ) (cong f γδ) (cong f αγ) (cong f βδ))
    → Square αβ γδ αγ βδ
  CMor□′ sq i j .σ s = sq s i j .fst
  CMor□′ sq i j .π s = sq s i j .snd

  CMor□′⁻ :
    Square αβ γδ αγ βδ
    → (s : F.S) 
    → let f = λ (ξ : F ⇒ G) → CMor′⁻ ξ s
      in Square (cong f αβ) (cong f γδ) (cong f αγ) (cong f βδ)
  CMor□′⁻ sq s i j .fst = sq i j .σ s
  CMor□′⁻ sq s i j .snd p = sq i j .π s p



module _ {F G : Container} {α β γ δ ζ θ : F ⇒ G} where
  open Container F

  CMorHex′ :
    ∀ {p : α ≡ β}
      {q : β ≡ γ}
      {r : γ ≡ δ}
      {u : α ≡ ζ}
      {v : ζ ≡ θ}
      {w : θ ≡ δ}
    → (∀ (s : S) → let f = λ (x : F ⇒ G) → CMor′⁻ x s
      in Hex (cong f p) (cong f q) (cong f r) 
        (cong f u) (cong f v) (cong f w))
    → Hex p q r u v w
  CMorHex′ hexs = goal
    where
    goal : Σ _ (λ _ → Σ _ _)
    goal .fst = CMor≡′ λ s → hexs s .fst
    goal .snd .fst = CMor□′ λ s → hexs s .snd .fst
    goal .snd .snd = CMor□′ λ s → hexs s .snd .snd

module Displayed (S : Type) (P : S → Type) where
  -- Paths between vertical maps over
  -- related base maps
  module _ {s₁ s₂ : S} 
    {ps₁ : P s₁ → S} 
    {ps₂ : P s₂ → S}
    where
    _≡[_,_]ᴾ_ : 
      (π₁ : (p : P s₁) → P (ps₁ p)) 
      (s≡ : s₁ ≡ s₂) (ps≡ : PathP (λ i → P (s≡ i) → S) ps₁ ps₂) 
      (π₂ : (p : P s₂) → P (ps₂ p)) → Type
    π₁ ≡[ s≡ , ps≡ ]ᴾ π₂ = PathP (λ i → (p : P (s≡ i)) → P (ps≡ i p)) π₁ π₂

  -- How complicated can this get?
  module _ {s₀₀ s₀₁ s₁₀ s₁₁ : S}
    {s≡₀₋ : s₀₀ ≡ s₀₁}
    {s≡₁₋ : s₁₀ ≡ s₁₁}
    {s≡₋₀ : s₀₀ ≡ s₁₀}
    {s≡₋₁ : s₀₁ ≡ s₁₁}
    (s□ : Square s≡₀₋ s≡₁₋ s≡₋₀ s≡₋₁)
    {ps₀₀ : P s₀₀ → S}
    {ps₀₁ : P s₀₁ → S}
    {ps₁₀ : P s₁₀ → S}
    {ps₁₁ : P s₁₁ → S}
    {ps≡₀₋ : PathP (λ i → P (s≡₀₋ i) → S) ps₀₀ ps₀₁}
    {ps≡₁₋ : PathP (λ i → P (s≡₁₋ i) → S) ps₁₀ ps₁₁}
    {ps≡₋₀ : PathP (λ i → P (s≡₋₀ i) → S) ps₀₀ ps₁₀}
    {ps≡₋₁ : PathP (λ i → P (s≡₋₁ i) → S) ps₀₁ ps₁₁}
    (ps□ : SquareP (λ i j → P (s□ i j) → S) ps≡₀₋ ps≡₁₋ ps≡₋₀ ps≡₋₁)
    {π₀₀ : (p : P s₀₀) → P (ps₀₀ p)}
    {π₀₁ : (p : P s₀₁) → P (ps₀₁ p)}
    {π₁₀ : (p : P s₁₀) → P (ps₁₀ p)}
    {π₁₁ : (p : P s₁₁) → P (ps₁₁ p)}
    where

    Squareᴾ : 
      (π≡₀₋ : π₀₀ ≡[ s≡₀₋ , ps≡₀₋ ]ᴾ π₀₁)
      (π≡₁₋ : π₁₀ ≡[ s≡₁₋ , ps≡₁₋ ]ᴾ π₁₁)
      (π≡₋₀ : π₀₀ ≡[ s≡₋₀ , ps≡₋₀ ]ᴾ π₁₀)
      (π≡₋₁ : π₀₁ ≡[ s≡₋₁ , ps≡₋₁ ]ᴾ π₁₁)
      → Type
    Squareᴾ π≡₀₋ π≡₁₋ π≡₋₀ π≡₋₁ = SquareP
      (λ i j → (p : P (s□ i j)) → P (ps□ i j p))
      π≡₀₋ π≡₁₋ π≡₋₀ π≡₋₁

  module _ {sa sb sc sd se sf : S}
    {sab : sa ≡ sb}
    {sbc : sb ≡ sc}
    {scd : sc ≡ sd}
    {sae : sa ≡ se}
    {sef : se ≡ sf}
    {sfd : sf ≡ sd}
    (shex : Hex sab sbc scd sae sef sfd)
    {psa : P sa → S}
    {psb : P sb → S}
    {psc : P sc → S}
    {psd : P sd → S}
    {pse : P se → S}
    {psf : P sf → S}
    {psab : PathP (λ i → P (sab i) → S) psa psb}
    {psbc : PathP (λ i → P (sbc i) → S) psb psc}
    {pscd : PathP (λ i → P (scd i) → S) psc psd}
    {psae : PathP (λ i → P (sae i) → S) psa pse}
    {psef : PathP (λ i → P (sef i) → S) pse psf}
    {psfd : PathP (λ i → P (sfd i) → S) psf psd}
    (pshex : HexP' (λ s → P s → S) shex 
      psab psbc pscd psae psef psfd)
    {πa : (p : P sa) → P (psa p)}
    {πb : (p : P sb) → P (psb p)}
    {πc : (p : P sc) → P (psc p)}
    {πd : (p : P sd) → P (psd p)}
    {πe : (p : P se) → P (pse p)}
    {πf : (p : P sf) → P (psf p)}
    where

    Hexᴾ : 
      (πab : πa ≡[ sab , psab ]ᴾ πb)
      (πbc : πb ≡[ sbc , psbc ]ᴾ πc)
      (πcd : πc ≡[ scd , pscd ]ᴾ πd)
      (πae : πa ≡[ sae , psae ]ᴾ πe)
      (πef : πe ≡[ sef , psef ]ᴾ πf)
      (πfd : πf ≡[ sfd , psfd ]ᴾ πd)
      → Type
    Hexᴾ πab πbc πcd πae πef πfd = 
      HexP
        (λ i j k → (p : P (sfill i j k)) → P (psfill i j k p))
        πab πbc πcd πae πef πfd
      where
      sfill = Hex-filler shex
      psfill = HexP'-filler (λ s → P s → S) shex pshex

