
compEndo : WildFunctor 
  (ProdCat GpdEndoWildCat GpdEndoWildCat) GpdEndoWildCat
compEndo .F-ob = uncurry compEndo₀
compEndo .F-hom {x = F , G} {y = H , K} = uncurry compEndo₁
compEndo .F-id = {! !}
compEndo .F-seq = {! !}
