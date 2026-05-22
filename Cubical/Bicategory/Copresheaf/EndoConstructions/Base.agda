open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.Bicategory.Copresheaf.EndoConstructions.Base
  (ℓ : Level) where

open import Cubical.Bicategory.Base
open import Cubical.Bicategory.Copresheaf ℓ
  using (Copresheaf; GPD; Is2Copresheaf; 2NatTrans; Is2NatTrans)
open import Cubical.Bicategory.Instances.Copresheaf ℓ

GpdEndo = Copresheaf GPD
GpdEndoWildCat = CopshWildCat GPD

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

open Bicategory GPD renaming (str to ⟨GPD⟩; Hom[_,_] to GPD[_,_])
open 2CellLaws ⟨GPD⟩

module _ where
  idEndo : GpdEndo
  idEndo .str .F-ob = idfun _
  idEndo .str .F-hom = idfun _
  idEndo .str .F-id = refl
  idEndo .str .F-seq _ _ = refl
  idEndo .is2Copresheaf .F-IdL _ = sym (lUnit _)
  idEndo .is2Copresheaf .F-IdR _ = sym (rUnit _)
  idEndo .is2Copresheaf .F-Assoc _ _ _ = lUnit _
