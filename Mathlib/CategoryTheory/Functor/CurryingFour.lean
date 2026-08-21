/-
Copyright (c) 2026 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Functor.CurryingThree
public import Mathlib.CategoryTheory.Products.Associator

/-!
# Currying of functors in four variables

We study the equivalence of categories
`currying₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ C₁ × C₂ × C₃ × C₄ ⥤ E`.
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C₁ C₂ C₃ C₄ D₁ D₂ D₃ D₄ E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* D₁] [Category* D₂] [Category* D₃] [Category* D₄] [Category* E]

/-- The equivalence of categories
`(C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ C₁ × C₂ × C₃ × C₄ ⥤ E`
given by currying functors in four variables. -/
def currying₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ≌ C₁ × C₂ × C₃ × C₄ ⥤ E :=
  currying.trans (currying.trans (currying.trans
    (((prod.associativity (C₁ × C₂) C₃ C₄).trans
      (prod.associativity C₁ C₂ (C₃ × C₄))).congrLeft)))

/-- Uncurrying a functor in four variables. -/
abbrev uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤ C₁ × C₂ × C₃ × C₄ ⥤ E :=
  currying₄.functor

/-- Currying a functor in four variables. -/
abbrev curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E :=
  currying₄.inverse

/-- Uncurrying functors in four variables gives a fully faithful functor. -/
def fullyFaithfulUncurry₄ :
    (uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤
      (C₁ × C₂ × C₃ × C₄ ⥤ E)).FullyFaithful :=
  currying₄.fullyFaithfulFunctor

/-- Currying functors in four variables gives a fully faithful functor. -/
def fullyFaithfulCurry₄ :
    (curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤
      (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)).FullyFaithful :=
  currying₄.fullyFaithfulInverse

instance : (uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤
    C₁ × C₂ × C₃ × C₄ ⥤ E).Full :=
  fullyFaithfulUncurry₄.full

instance : (uncurry₄ : (C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E) ⥤
    C₁ × C₂ × C₃ × C₄ ⥤ E).Faithful :=
  fullyFaithfulUncurry₄.faithful

instance : (curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E).Full :=
  fullyFaithfulCurry₄.full

instance : (curry₄ : (C₁ × C₂ × C₃ × C₄ ⥤ E) ⥤
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E).Faithful :=
  fullyFaithfulCurry₄.faithful

@[simp]
lemma curry₄_obj_map_app_app_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    {X₁ Y₁ : C₁} (f : X₁ ⟶ Y₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.obj F).map f).app X₂).app X₃).app X₄ =
      F.map ⟨f, 𝟙 X₂, 𝟙 X₃, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_map_app_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) {X₂ Y₂ : C₂} (f : X₂ ⟶ Y₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.obj F).obj X₁).map f).app X₃).app X₄ =
      F.map ⟨𝟙 X₁, f, 𝟙 X₃, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_obj_map_app (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) {X₃ Y₃ : C₃} (f : X₃ ⟶ Y₃) (X₄ : C₄) :
    ((((curry₄.obj F).obj X₁).obj X₂).map f).app X₄ =
      F.map ⟨𝟙 X₁, 𝟙 X₂, f, 𝟙 X₄⟩ := rfl

@[simp]
lemma curry₄_obj_obj_obj_obj_map (F : C₁ × C₂ × C₃ × C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) {X₄ Y₄ : C₄} (f : X₄ ⟶ Y₄) :
    ((((curry₄.obj F).obj X₁).obj X₂).obj X₃).map f =
      F.map ⟨𝟙 X₁, 𝟙 X₂, 𝟙 X₃, f⟩ := rfl

@[simp]
lemma curry₄_map_app_app_app_app {F G : C₁ × C₂ × C₃ × C₄ ⥤ E} (f : F ⟶ G)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((curry₄.map f).app X₁).app X₂).app X₃).app X₄ = f.app ⟨X₁, X₂, X₃, X₄⟩ := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma currying₄_unitIso_hom_app_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((currying₄.unitIso.hom.app F).app X₁).app X₂).app X₃).app X₄ = 𝟙 _ := by
  simp [currying₄, Equivalence.unit]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[simp]
lemma currying₄_unitIso_inv_app_app_app_app_app (F : C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E)
    (X₁ : C₁) (X₂ : C₂) (X₃ : C₃) (X₄ : C₄) :
    ((((currying₄.unitIso.inv.app F).app X₁).app X₂).app X₃).app X₄ = 𝟙 _ := by
  simp [currying₄, Equivalence.unitInv]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- Given functors `Fᵢ : Cᵢ ⥤ Dᵢ` for `1 ≤ i ≤ 4` and
`G : D₁ × D₂ × D₃ × D₄ ⥤ E`, this is the isomorphism between currying the
precomposition of `G` by the product of the `Fᵢ` and precomposing the four curried variables. -/
@[simps!]
def curry₄ObjProdComp (F₁ : C₁ ⥤ D₁) (F₂ : C₂ ⥤ D₂) (F₃ : C₃ ⥤ D₃)
    (F₄ : C₄ ⥤ D₄) (G : D₁ × D₂ × D₃ × D₄ ⥤ E) :
    curry₄.obj (F₁.prod (F₂.prod (F₃.prod F₄)) ⋙ G) ≅
      F₁ ⋙ curry₄.obj G ⋙ ((((whiskeringLeft₃ E).obj F₂).obj F₃).obj F₄) :=
  NatIso.ofComponents (fun X₁ ↦ NatIso.ofComponents (fun X₂ ↦
    NatIso.ofComponents (fun X₃ ↦ NatIso.ofComponents (fun X₄ ↦ Iso.refl _))))

end Functor

variable {C₁ C₂ C₃ C₄ C₂₃₄ C₃₄ E : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Category* C₂₃₄] [Category* C₃₄] [Category* E]

/-- Compose a bifunctor in the first variable with a trifunctor in the last three variables. -/
@[simps]
def trifunctorComp₂₃₄ (F : C₁ ⥤ C₂₃₄ ⥤ E) (G : C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj X₁ := (Functor.postcompose₃.obj (F.obj X₁)).obj G
  map f := (Functor.postcompose₃.map (F.map f)).app G

set_option backward.isDefEq.respectTransparency false in
/-- Composition in the last three variables, as a functor in the trifunctor being composed. -/
@[simps]
def trifunctorComp₂₃₄Functor (F : C₁ ⥤ C₂₃₄ ⥤ E) :
    (C₂ ⥤ C₃ ⥤ C₄ ⥤ C₂₃₄) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj G := trifunctorComp₂₃₄ F G
  map {G G'} τ :=
    { app X₁ := (Functor.postcompose₃.obj (F.obj X₁)).map τ
      naturality X₁ Y₁ f := by
        ext X₂ X₃ X₄
        change (F.map f).app (((G.obj X₂).obj X₃).obj X₄) ≫
            (F.obj Y₁).map ((((τ.app X₂).app X₃).app X₄)) =
          (F.obj X₁).map ((((τ.app X₂).app X₃).app X₄)) ≫
            (F.map f).app (((G'.obj X₂).obj X₃).obj X₄)
        exact ((F.map f).naturality _).symm }

/-- Substitute a bifunctor into the third variable of a trifunctor. -/
@[simps]
def trifunctorComp₃₄ (F : C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E) (G : C₃ ⥤ C₄ ⥤ C₃₄) :
    C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj X₁ := bifunctorComp₂₃ (F.obj X₁) G
  map f := (bifunctorComp₂₃Functor.map (F.map f)).app G

set_option backward.isDefEq.respectTransparency false in
/-- Substitution in the third variable, as a functor in the trifunctor being composed. -/
@[simps]
def trifunctorComp₃₄Functor (G : C₃ ⥤ C₄ ⥤ C₃₄) :
    (C₁ ⥤ C₂ ⥤ C₃₄ ⥤ E) ⥤ C₁ ⥤ C₂ ⥤ C₃ ⥤ C₄ ⥤ E where
  obj F := trifunctorComp₃₄ F G
  map {F F'} τ :=
    { app X₁ := (bifunctorComp₂₃Functor.map (τ.app X₁)).app G
      naturality X₁ Y₁ f := by
        ext X₂ X₃ X₄
        exact NatTrans.congr_app (NatTrans.congr_app (τ.naturality f) X₂)
          ((G.obj X₃).obj X₄) }

end CategoryTheory
