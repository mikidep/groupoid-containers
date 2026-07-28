{-# OPTIONS -WnoUnsupportedIndexedMatch #-}

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (idfun)

module Prelude.Reassoc where

open import Cubical.Data.Nat
open import Prelude.Utils
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Foundations.GroupoidLaws

infixr 20 _∙′_
infix 45 ↑_

data Term {ℓ : Level} : {A : Type ℓ} → A → A → Type (ℓ-suc ℓ) where
  refl′ : ∀ {A} {x : A} → Term x x
  ↑_ : ∀ {A} {x y : A} (p : x ≡ y) → Term x y
  _∙′_ : ∀ {A} {x y z : A} → Term x y → Term y z → Term x z
  cong′ : ∀ {A} {B : Type ℓ} {x y : B}  
    (f : B → A)
    → Term x y
    → Term (f x) (f y)

data Ev {ℓ : Level} {A : Type ℓ} : (x y : A) → Type (ℓ-suc ℓ) where
  nil : ∀ {x : A} → Ev x x
  _∷_ : {x y z : A} 
        (p : x ≡ y) 
        (l : Ev y z) 
        → Ev x z

module _ {ℓ : Level} where
  embed nf : {A : Type ℓ} {x y : A} → Term x y → x ≡ y

  embed refl′ = refl
  embed (↑ p) = p
  embed (tm ∙′ tm₁) = embed tm ∙ embed tm₁
  embed (cong′ f tm) = cong f (embed tm)

  _++_ : {A : Type ℓ} {x y z : A}
    → Ev x y → Ev y z → Ev x z
  nil ++ ev₁ = ev₁
  (p ∷ ev) ++ ev₁ = p ∷ (ev ++ ev₁)

  ev-cong : {A B : Type ℓ} {x y : A}
    (f : A → B) → Ev x y → Ev (f x) (f y) 
  ev-cong _ nil = nil
  ev-cong f (p ∷ ev) = cong f p ∷ ev-cong f ev

  ev-∙ : {A : Type ℓ} {x y : A} → Ev x y → x ≡ y
  ev-∙ nil = refl
  ev-∙ (p ∷ ev) = p ∙ ev-∙ ev

  ev-++-∙ : {A : Type ℓ} {x y z : A}
    (ev : Ev x y) (ev' : Ev y z)
    → ev-∙ (ev ++ ev') ≡ ev-∙ ev ∙ ev-∙ ev'
  ev-++-∙ nil ev' = lUnit (ev-∙ ev')
  ev-++-∙ (p ∷ ev) ev' = 
    cong (p ∙_) (ev-++-∙ ev ev') 
    ∙ assoc p (ev-∙ ev) (ev-∙ ev')

  ev-cong-∙ :
    {A B : Type ℓ} {x y : A}
    (f : A → B) (ev : Ev x y) 
    → ev-∙ (ev-cong f ev) ≡ cong f (ev-∙ ev)
  ev-cong-∙ f nil = refl
  ev-cong-∙ f (p ∷ ev) = 
    cong (cong f p ∙_) (ev-cong-∙ f ev) 
    ∙ sym (congFunct f p (ev-∙ ev))

  ncomps : {A : Type ℓ} {x y : A} → Term x y → Ev x y
  ncomps refl′ = nil
  ncomps (↑ p) = p ∷ nil
  ncomps (tm ∙′ tm₁) = ncomps tm ++ ncomps tm₁
  ncomps (cong′ f tm) = ev-cong f (ncomps tm)

  nf tm = ev-∙ (ncomps tm)

  nf-sound : {A : Type ℓ} {x y : A} (tm : Term x y) 
    → embed tm ≡ nf tm
  nf-sound refl′ = refl
  nf-sound (↑ p) = rUnit p
  nf-sound (tm ∙′ tm₁) = 
    cong₂ _∙_ (nf-sound tm) (nf-sound tm₁)
    ∙ sym (ev-++-∙ (ncomps tm) (ncomps tm₁))
  nf-sound (cong′ f tm) = 
    cong (cong f) (nf-sound tm)
    ∙ sym (ev-cong-∙ f (ncomps tm))

  abstract
    reassoc : ∀ {A : Type ℓ} {x y : A} 
      (tm tm' : Term x y)
      → nf tm ≡ nf tm' → embed tm ≡ embed tm'
    reassoc tm tm' nf≡ = nf-sound tm ∙ nf≡ ∙ sym (nf-sound tm')

open import Cubical.WildCat.Base

module BicatReassoc {ℓC ℓC'} (WC : WildCat ℓC ℓC') where
  open WildCat WC

  infixr 41 _◃′_
  infixl 40 _▹′_

  _◃′_ : ∀ {a b c : ob}
    (f : Hom[ a , b ])
    {g h : Hom[ b , c ]}
    → Term g h
    → Term (f ⋆ g) (f ⋆ h)
  f ◃′ g≡h = cong′ (f ⋆_) g≡h

  _▹′_ : ∀ {a b c : ob}
    {f g : Hom[ a , b ]}
    → Term f g
    → (h : Hom[ b , c ])
    → Term (f ⋆ h) (g ⋆ h)
  f≡g ▹′ h = cong′ (_⋆ h) f≡g
