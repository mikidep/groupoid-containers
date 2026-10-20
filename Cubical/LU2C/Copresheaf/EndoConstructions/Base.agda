open import Cubical.Foundations.Prelude

open import Cubical.Foundations.Function
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws

open import Cubical.WildCat.Functor hiding (_$_)
open import Cubical.WildCat.Product renaming (_×_ to ProdCat)

module Cubical.LU2C.Copresheaf.EndoConstructions.Base
  (ℓ : Level) where

open import Cubical.LU2C.Base
open import Cubical.LU2C.Copresheaf ℓ
  using (Copresheaf; HGpd; Is2Copresheaf; PseudonatTrans; IsPseudonat)
open import Cubical.LU2C.Instances.Copresheaf ℓ

GpdEndo = Copresheaf HGpd
GpdEndoWildCat = CopshWildCat HGpd

open Copresheaf using (str; is2Copresheaf)
open WildFunctor
open Is2Copresheaf

module _ where
  idEndo : GpdEndo
  idEndo .str .F-ob = idfun _
  idEndo .str .F-hom = idfun _
  idEndo .str .F-id = refl
  idEndo .str .F-seq _ _ = refl
  idEndo .is2Copresheaf .F-IdL _ = sym (lUnit _)
  idEndo .is2Copresheaf .F-IdR _ = sym (rUnit _)
  idEndo .is2Copresheaf .F-Assoc _ _ _ = lUnit _
