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
  using (Copresheaf; Is2Copresheaf)
open import Cubical.LU2C.Instances.Groupoids ℓ
open import Cubical.LU2C.Instances.Copresheaf ℓ

GpdEndo = Copresheaf HGpd
GpdEndoWildCat = CopshWildCat HGpd

open WildFunctor
open Is2Copresheaf

module _ where
  idEndo : GpdEndo
  idEndo .fst .F-ob = idfun _
  idEndo .fst .F-hom = idfun _
  idEndo .fst .F-id = refl
  idEndo .fst .F-seq _ _ = refl
  idEndo .snd .F-IdL _ = sym (lUnit _)
  idEndo .snd .F-IdR _ = sym (rUnit _)
  idEndo .snd .F-Assoc _ _ _ = lUnit _
