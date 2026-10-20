open import Cubical.Foundations.Prelude
open import Cubical.WildCat.Base hiding (_[_,_])
open import Cubical.LU2C.Base

open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Function 
  using (homotopyNatural)
open import Cubical.Foundations.GroupoidLaws
open import Prelude.ExtraGpdLaws
open import Prelude.Reassoc

module Cubical.LU2C.Properties {ℓ ℓ′ : Level} where 
  
open LU2CSyntax {{...}}

module _ (C : WildCat ℓ ℓ′) where
  open IsLU2C
  isPropIsLU2C : isProp (IsLU2C C)
  isPropIsLU2C x y i .triangle f g = x .isGpdHom _ _ _ _ (x .triangle f g) (y .triangle f g) i
  isPropIsLU2C x y i .pentagon f g h k = x .isGpdHom _ _ _ _ (x .pentagon f g h k) (y .pentagon f g h k) i
  isPropIsLU2C x y i .isGpdHom = isPropIsGroupoid (x .isGpdHom) (y .isGpdHom) i

module _ (C : LU2C ℓ ℓ′) where
  open LU2C C using (triangle; pentagon) 
    renaming (ob to C₀)

  open LU2CSyn2C C
  open LU2CReassoc (LU2C.str C)

  private variable
    x y z : C₀
    f f' : C [ x , y ]
    g g' : C [ y , z ]

  ⋆IdL-nat : 
    (p : f ≡ f')
    → ⋆IdL f ∙ p
    ≡ id ◃ p ∙ ⋆IdL f'
  ⋆IdL-nat {f} = J Q d
    where
    Q = λ f' p → ⋆IdL f ∙ p ≡ id ◃ p ∙ ⋆IdL f'
    d = sym (rUnit _) ∙ lUnit _

  ⋆IdR-nat :
    (p : f ≡ f')
    → ⋆IdR f ∙ p
    ≡ p ▹ id ∙ ⋆IdR f'
  ⋆IdR-nat {f} = J Q d
    where
    Q = λ f' p → ⋆IdR f ∙ p ≡ p ▹ id ∙ ⋆IdR f'
    d = sym (rUnit _) ∙ lUnit _

  ⋆Assoc-nat :
    {w x y z : C₀}
    {f f' : C [ w , x ]}
    {g g' : C [ x , y ]}
    {h h' : C [ y , z ]}
    (p : f ≡ f') (q : g ≡ g') (r : h ≡ h')
    → ⋆Assoc f g h ∙ (p ⋆₂ (q ⋆₂ r))
      ≡ ((p ⋆₂ q) ⋆₂ r) ∙ ⋆Assoc f' g' h'
  ⋆Assoc-nat p q r =
    homotopyNatural (λ (f , g , h) → ⋆Assoc f g h)
      (λ i → p i , q i , r i)

  id◃ : 
    (p q : f ≡ f')
    → id ◃ p ≡ id ◃ q 
    → p ≡ q
  id◃ {f} {f'} p q id◃≡ = lCancelEq goal
    where
    goal : ⋆IdL f ∙ p ≡ ⋆IdL f ∙ q
    goal = 
      ⋆IdL f ∙ p 
        ≡⟨ ⋆IdL-nat p ⟩ 
      id ◃ p ∙ ⋆IdL f' 
        ≡⟨ ∙r id◃≡  ⟩ 
      id ◃ q ∙ ⋆IdL f' 
        ≡⟨ sym (⋆IdL-nat q) ⟩ 
      ⋆IdL f ∙ q
        ∎

  ▹id : 
    (p q : f ≡ f')
    → p ▹ id ≡ q ▹ id 
    → p ≡ q
  ▹id {f} {f'} p q ▹id≡ = lCancelEq goal
    where
    goal : ⋆IdR f ∙ p ≡ ⋆IdR f ∙ q
    goal =
      ⋆IdR f ∙ p
        ≡⟨ ⋆IdR-nat p ⟩
      p ▹ id ∙ ⋆IdR f'
        ≡⟨ ∙r ▹id≡ ⟩
      q ▹ id ∙ ⋆IdR f'
        ≡⟨ sym (⋆IdR-nat q) ⟩
      ⋆IdR f ∙ q
        ∎

  -- Johnson Yau 2020, prop. 2.2.4

  ⋆IdL-⋆ : 
    {x y z : C₀} 
    (f : C [ x , y ]) 
    (g : C [ y , z ])
    → ⋆Assoc id f g ∙ ⋆IdL (f ⋆ g) 
      ≡ ⋆IdL f ▹ g
  ⋆IdL-⋆ f g = id◃ _ _ (lCancelEq (lCancelEq goal))
    where
    goal :
      ⋆Assoc id id f ▹ g ∙ ⋆Assoc id (id ⋆ f) g
        ∙ id ◃ (⋆Assoc id f g ∙ ⋆IdL (f ⋆ g))
      ≡ ⋆Assoc id id f ▹ g ∙ ⋆Assoc id (id ⋆ f) g
        ∙ id ◃ (⋆IdL f ▹ g)
    goal =
      ⋆Assoc id id f ▹ g ∙ ⋆Assoc id (id ⋆ f) g
        ∙ id ◃ (⋆Assoc id f g ∙ ⋆IdL (f ⋆ g))
        ≡⟨ reass₁ ⟩
      (⋆Assoc id id f ▹ g ∙ ⋆Assoc id (id ⋆ f) g
        ∙ id ◃ ⋆Assoc id f g) ∙ id ◃ ⋆IdL (f ⋆ g)
        ≡⟨ ∙r (pentagon id id f g) ⟩
      (⋆Assoc (id ⋆ id) f g ∙ ⋆Assoc id id (f ⋆ g))
        ∙ id ◃ ⋆IdL (f ⋆ g)
        ≡⟨ sym (assoc _ _ _) ⟩
      ⋆Assoc (id ⋆ id) f g
        ∙ ⋆Assoc id id (f ⋆ g) ∙ id ◃ ⋆IdL (f ⋆ g)
        ≡⟨ ∙l (triangle id (f ⋆ g)) ⟩
      ⋆Assoc (id ⋆ id) f g ∙ ⋆IdR id ▹ (f ⋆ g)
        ≡⟨ ⋆Assoc-nat (⋆IdR id) refl refl ⟩
      (⋆IdR id ▹ f) ▹ g ∙ ⋆Assoc id f g
        ≡⟨ ∙r cong (_▹ g) (sym (triangle id f)) ⟩
      (⋆Assoc id id f ∙ id ◃ ⋆IdL f) ▹ g ∙ ⋆Assoc id f g
        ≡⟨ reass₂ ⟩
      ⋆Assoc id id f ▹ g ∙ (id ◃ ⋆IdL f) ▹ g ∙ ⋆Assoc id f g
        ≡⟨ ∙l (sym (⋆Assoc-nat refl (⋆IdL f) refl)) ⟩
      ⋆Assoc id id f ▹ g ∙ ⋆Assoc id (id ⋆ f) g
        ∙ id ◃ (⋆IdL f ▹ g)
        ∎
      where
      reass₁ = reassoc
        (↑ (⋆Assoc id id f ▹ g) ∙′ ↑ (⋆Assoc id (id ⋆ f) g)
          ∙′ id ◃′ (↑ (⋆Assoc id f g) ∙′ ↑ (⋆IdL (f ⋆ g))))
        ((↑ (⋆Assoc id id f ▹ g) ∙′ ↑ (⋆Assoc id (id ⋆ f) g)
          ∙′ ↑ (id ◃ ⋆Assoc id f g)) ∙′ ↑ (id ◃ ⋆IdL (f ⋆ g))) 
        refl
      reass₂ = reassoc
        ((↑ (⋆Assoc id id f) ∙′ ↑ (id ◃ ⋆IdL f)) ▹′ g ∙′ ↑ (⋆Assoc id f g))
        (↑ (⋆Assoc id id f ▹ g) ∙′ ↑ ((id ◃ ⋆IdL f) ▹ g) ∙′ ↑ (⋆Assoc id f g)) 
        refl

  ⋆IdR-⋆ :
    {x y z : C₀}
    (f : C [ x , y ])
    (g : C [ y , z ])
    → ⋆Assoc f g id ∙ f ◃ ⋆IdR g
      ≡ ⋆IdR (f ⋆ g)
  ⋆IdR-⋆ f g = ▹id _ _ (rCancelEq goal)
    where
    goal :
      (⋆Assoc f g id ∙ f ◃ ⋆IdR g) ▹ id ∙ ⋆Assoc f g id
      ≡ ⋆IdR (f ⋆ g) ▹ id ∙ ⋆Assoc f g id
    goal =
      (⋆Assoc f g id ∙ f ◃ ⋆IdR g) ▹ id ∙ ⋆Assoc f g id
        ≡⟨ reass₁ ⟩
      ⋆Assoc f g id ▹ id ∙ (f ◃ ⋆IdR g) ▹ id ∙ ⋆Assoc f g id
        ≡⟨ ∙l (sym (⋆Assoc-nat refl (⋆IdR g) refl)) ⟩
      ⋆Assoc f g id ▹ id ∙ ⋆Assoc f (g ⋆ id) id
        ∙ f ◃ (⋆IdR g ▹ id)
        ≡⟨ ∙l ∙l cong (f ◃_) (sym (triangle g id)) ⟩
      ⋆Assoc f g id ▹ id ∙ ⋆Assoc f (g ⋆ id) id
        ∙ f ◃ (⋆Assoc g id id ∙ g ◃ ⋆IdL id)
        ≡⟨ reass₂ ⟩
      (⋆Assoc f g id ▹ id ∙ ⋆Assoc f (g ⋆ id) id
        ∙ f ◃ ⋆Assoc g id id) ∙ f ◃ (g ◃ ⋆IdL id)
        ≡⟨ ∙r (pentagon f g id id) ⟩
      (⋆Assoc (f ⋆ g) id id ∙ ⋆Assoc f g (id ⋆ id))
        ∙ f ◃ (g ◃ ⋆IdL id)
        ≡⟨ sym (assoc _ _ _) ⟩
      ⋆Assoc (f ⋆ g) id id
        ∙ ⋆Assoc f g (id ⋆ id) ∙ f ◃ (g ◃ ⋆IdL id)
        ≡⟨ ∙l (⋆Assoc-nat refl refl (⋆IdL id)) ⟩
      ⋆Assoc (f ⋆ g) id id ∙ (f ⋆ g) ◃ ⋆IdL id ∙ ⋆Assoc f g id
        ≡⟨ assoc _ _ _ ⟩
      (⋆Assoc (f ⋆ g) id id ∙ (f ⋆ g) ◃ ⋆IdL id) ∙ ⋆Assoc f g id
        ≡⟨ ∙r (triangle (f ⋆ g) id) ⟩
      ⋆IdR (f ⋆ g) ▹ id ∙ ⋆Assoc f g id
        ∎
      where
      reass₁ = reassoc
        ((↑ (⋆Assoc f g id) ∙′ ↑ (f ◃ ⋆IdR g)) ▹′ id ∙′ ↑ (⋆Assoc f g id))
        (↑ (⋆Assoc f g id ▹ id) ∙′ ↑ ((f ◃ ⋆IdR g) ▹ id) ∙′ ↑ (⋆Assoc f g id)) 
        refl
      reass₂ = reassoc
        (↑ (⋆Assoc f g id ▹ id) ∙′ ↑ (⋆Assoc f (g ⋆ id) id)
          ∙′ f ◃′ (↑ (⋆Assoc g id id) ∙′ ↑ (g ◃ ⋆IdL id)))
        ((↑ (⋆Assoc f g id ▹ id) ∙′ ↑ (⋆Assoc f (g ⋆ id) id)
          ∙′ ↑ (f ◃ ⋆Assoc g id id)) ∙′ ↑ (f ◃ (g ◃ ⋆IdL id))) 
        refl
