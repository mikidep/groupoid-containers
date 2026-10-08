open import Cubical.Foundations.Prelude

open import Cubical.Bicategory.Base

module Cubical.Bicategory.Instances.Walking where

open import Cubical.Data.Unit
open import Cubical.Data.Empty

module Walking where
  data ob : Type where
    𝟘 𝟙 : ob
  
  Hom[_,_] : ob → ob → Type 
  Hom[ 𝟘 , 𝟘 ] = Unit
  Hom[ 𝟘 , 𝟙 ] = Unit
  Hom[ 𝟙 , 𝟘 ] = ⊥
  Hom[ 𝟙 , 𝟙 ] = Unit

  id : {x : ob} → Hom[ x , x ]
  id {(𝟘)} = tt
  id {(𝟙)} = tt

  _⋆_ : {x y z : ob} → Hom[ x , y ] → Hom[ y , z ] → Hom[ x , z ]
  _⋆_ {(𝟘)} {(𝟘)} {(z)} tt g = g
  _⋆_ {(𝟘)} {(𝟙)} {(𝟙)} _ _ = tt
  _⋆_ {(𝟙)} {(𝟙)} {(𝟙)} _ _ = tt

  ⋆IdL : {x y : ob} (f : Hom[ x , y ]) 
    → id ⋆ f ≡ f 
  ⋆IdL {(𝟘)} {(𝟘)} f = refl
  ⋆IdL {(𝟘)} {(𝟙)} f = refl
  ⋆IdL {(𝟙)} {(𝟙)} f = refl

  ⋆IdR : {x y : ob} (f : Hom[ x , y ]) 
    → f ⋆ id ≡ f 
  ⋆IdR {(𝟘)} {(𝟘)} f = refl
  ⋆IdR {(𝟘)} {(𝟙)} f = refl
  ⋆IdR {(𝟙)} {(𝟙)} f = refl

  ⋆Assoc : {u v w x : ob} 
    (f : Hom[ u , v ]) 
    (g : Hom[ v , w ]) 
    (h : Hom[ w , x ])
    → (f ⋆ g) ⋆ h ≡ f ⋆ (g ⋆ h) 
  ⋆Assoc {(𝟘)} {(𝟘)} tt g h = refl
  ⋆Assoc {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ = refl
  ⋆Assoc {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ = refl

open Bicategory
open IsBicategory

open Walking using (𝟘; 𝟙) public

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

Walking : Bicategory _ _
Walking .str = record where
  open Walking using 
    ( ob
    ; Hom[_,_]
    ; id
    ; _⋆_
    ; ⋆IdL
    ; ⋆IdR
    ; ⋆Assoc
    )
Walking .isBicat .triangle {(𝟘)} {(𝟘)} {(𝟘)} _ _ = lUnit _
Walking .isBicat .triangle {(𝟘)} {(𝟘)} {(𝟙)} _ _ = lUnit _
Walking .isBicat .triangle {(𝟘)} {(𝟙)} {(𝟙)} _ _ = lUnit _
Walking .isBicat .triangle {(𝟙)} {(𝟙)} {(𝟙)} _ _ = lUnit _
Walking .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} _ _ _ _ = lUnit _
Walking .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} {(𝟙)} _ _ _ _ = lUnit _
Walking .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
Walking .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
Walking .isBicat .pentagon {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
Walking .isBicat .pentagon {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
Walking .isBicat .isGpdHom {(𝟘)} {(𝟘)} = isSet→isGroupoid isSetUnit
Walking .isBicat .isGpdHom {(𝟘)} {(𝟙)} = isSet→isGroupoid isSetUnit
Walking .isBicat .isGpdHom {(𝟙)} {(𝟙)} = isSet→isGroupoid isSetUnit

-- In a more convoluted way

-- open import Cubical.Bicategory.Instances.FromSetCat

-- open import Cubical.Categories.Instances.Free

-- Walking′ : Bicategory _ _
-- Walking′ = AsBicat ?

