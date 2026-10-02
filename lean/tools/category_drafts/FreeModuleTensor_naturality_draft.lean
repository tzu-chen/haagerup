-- DRAFT (not compiled; not part of the build).  Naturality of `freeTensorIso` in `X` and `Y`,
-- to be appended to `HaagerupIzumi/C8/Category/FreeModuleTensor.lean` inside
-- `namespace RightMod`, after `freeTensorIso_hom_hom` (same section variables).
-- An earlier `calc` version failed only with `Trans Eq Eq` (intermediate terms had defeq but
-- syntactically different source objects); this `Eq.trans` version has not been checked.
-- Ingredients that DO compile: `freeTensorXIso_whiskerRight`, `freeTensorXIso_whiskerLeft`,
-- `freeTensorIso_hom_hom` (in FreeModuleTensor.lean), and Mathlib's
-- `associator_inv_naturality_left/middle`.

/-- `freeTensorIso` is natural in `X`. -/
theorem freeTensorIso_natural_left {X' : C} (f : X ⟶ X') :
    Bimod.whiskerRight ((toBimod A).map (freeMap A f)) ((toBimod A).obj (free A Y)) ≫
        (freeTensorIso A X' Y).hom =
      (freeTensorIso A X Y).hom ≫ (toBimod A).map (freeMap A (f ▷ Y)) := by
  apply Bimod.hom_ext
  exact ((reassoc_of% (freeTensorXIso_whiskerRight A X ((toBimod A).obj (free A Y)) f))
      (α_ X' Y A.X).inv).trans
    ((congrArg (fun k => (freeTensorXIso A X ((toBimod A).obj (free A Y))).hom ≫ k)
      (MonoidalCategory.associator_inv_naturality_left f Y A.X)).trans
      (Category.assoc _ _ _).symm)

/-- `freeTensorIso` is natural in `Y`. -/
theorem freeTensorIso_natural_right {Y' : C} (g : Y ⟶ Y') :
    Bimod.whiskerLeft ((toBimod A).obj (free A X)) ((toBimod A).map (freeMap A g)) ≫
        (freeTensorIso A X Y').hom =
      (freeTensorIso A X Y).hom ≫ (toBimod A).map (freeMap A (X ◁ g)) := by
  apply Bimod.hom_ext
  exact ((reassoc_of% (freeTensorXIso_whiskerLeft A X ((toBimod A).map (freeMap A g))))
      (α_ X Y' A.X).inv).trans
    ((congrArg (fun k => (freeTensorXIso A X ((toBimod A).obj (free A Y))).hom ≫ k)
      (MonoidalCategory.associator_inv_naturality_middle X g A.X)).trans
      (Category.assoc _ _ _).symm)

