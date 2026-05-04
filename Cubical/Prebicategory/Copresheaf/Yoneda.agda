open import Cubical.Foundations.Prelude
open import Cubical.Prebicategory.Base
open import Cubical.Prebicategory.Functor

module Cubical.Prebicategory.Copresheaf.Yoneda (ℓ : Level) 
  -- {ℓC ℓC' : Level}
  (C : Prebicategory ℓ ℓ)
  where

open import Cubical.Prebicategory.Copresheaf ℓ
open import Cubical.Prebicategory.Instances.Copresheaf ℓ

CopshC : Prebicategory _ _
CopshC = CopshPrebicat C 

module C = Prebicategory C

module _ (c : C.ob) where
  open import Cubical.WildCat.Functor

  open Copresheaf
  open WildFunctor
  open Is2Copresheaf
  open Prebicategory GPD
    using (_◃_; _▹_)
  open import Cubical.Foundations.Path
  open import Cubical.Foundations.GroupoidLaws
  open import Prelude.Square

  C[c,-] : Copresheaf C  
  C[c,-] .str .F-ob x = C.Hom[ c , x ] , C.isGpdHom
  C[c,-] .str .F-hom f h = h C.⋆ f
  C[c,-] .str .F-id = funExt C.⋆IdR
  C[c,-] .str .F-seq f g = funExt λ h → sym (C.⋆Assoc h f g)
  C[c,-] .is2Copresheaf .F-IdL {f} = funExtSquare λ h →
        sym (C.⋆Assoc h C.id f) ∙ C.⋆IdR h C.▹ f
      ≡⟨ {! !} ⟩
        h C.◃ C.⋆IdL f
      ∎
    -- sym (PathP→compPathR∙∙ (
    --   funExtSquare λ h →
    --     compPathR→PathP∙∙ (
    --         h C.◃ C.⋆IdL f
    --       ≡⟨ lUnit _ ⟩
    --         refl ∙ h C.◃ C.⋆IdL f
    --       ≡⟨ cong (_∙ h C.◃ C.⋆IdL f) (sym (lCancel _)) ⟩
    --         (sym (C.⋆Assoc h C.id f) ∙ C.⋆Assoc h C.id f)
    --           ∙ h C.◃ C.⋆IdL f
    --       ≡⟨ sym (assoc _ _ _) ⟩
    --         sym (C.⋆Assoc h C.id f) 
    --           ∙ C.⋆Assoc h C.id f ∙ h C.◃ C.⋆IdL f
    --       ≡⟨ cong (sym (C.⋆Assoc h C.id f) ∙_) 
    --           (C.triangle h f) ⟩
    --         sym (C.⋆Assoc h C.id f) ∙ C.⋆IdR h C.▹ f
    --       ∎
    --     )
    -- ))
    where open import Prelude
  C[c,-] .is2Copresheaf .F-IdR {f} = funExtSquare λ h → 
      sym (C.⋆Assoc h f C.id) ∙ C.⋆IdR (h C.⋆ f)
    ≡⟨ {! C.triangle !} ⟩
      h C.◃ C.⋆IdR f
    ∎

  C[c,-] .is2Copresheaf .F-Assoc = {! !}
