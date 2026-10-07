open import Cubical.Foundations.Prelude

open import Cubical.Bicategory.Base

module Cubical.Bicategory.Instances.Arrow where

open import Cubical.Data.Unit
open import Cubical.Data.Empty

module Arrow where
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

open Arrow using (𝟘; 𝟙)

open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.HLevels

Arrow : Bicategory _ _
Arrow .str = record where
  open Arrow using 
    ( ob
    ; Hom[_,_]
    ; id
    ; _⋆_
    ; ⋆IdL
    ; ⋆IdR
    ; ⋆Assoc
    )
Arrow .isBicat .triangle {(𝟘)} {(𝟘)} {(𝟘)} _ _ = lUnit _
Arrow .isBicat .triangle {(𝟘)} {(𝟘)} {(𝟙)} _ _ = lUnit _
Arrow .isBicat .triangle {(𝟘)} {(𝟙)} {(𝟙)} _ _ = lUnit _
Arrow .isBicat .triangle {(𝟙)} {(𝟙)} {(𝟙)} _ _ = lUnit _
Arrow .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} _ _ _ _ = lUnit _
Arrow .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟘)} {(𝟙)} _ _ _ _ = lUnit _
Arrow .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟘)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
Arrow .isBicat .pentagon {(𝟘)} {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
Arrow .isBicat .pentagon {(𝟘)} {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
Arrow .isBicat .pentagon {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} {(𝟙)} _ _ _ _ = lUnit _
Arrow .isBicat .isGpdHom {(𝟘)} {(𝟘)} = isSet→isGroupoid isSetUnit
Arrow .isBicat .isGpdHom {(𝟘)} {(𝟙)} = isSet→isGroupoid isSetUnit
Arrow .isBicat .isGpdHom {(𝟙)} {(𝟙)} = isSet→isGroupoid isSetUnit
