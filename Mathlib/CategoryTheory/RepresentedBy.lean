/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
import Mathlib.CategoryTheory.Yoneda

/-!
# `IsRepresentedBy` predicate

In this file we develop more API for representable functors.
-/

universe w' w v u v₁ u₁

open Opposite

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C]

/-- Variant of the Yoneda embedding which allows a raise in the universe level
for the category of types. -/
@[pp_with_univ, simps!]
def uliftCoyoneda : Cᵒᵖ ⥤ C ⥤ Type (max w v₁) :=
  coyoneda ⋙ (Functor.whiskeringRight _ _ _).obj uliftFunctor.{w}

/-- If `C` is a category with `[Category.{max w v₁} C]`, this is the isomorphism
`uliftCoyoneda.{w} (C := C) ≅ coyoneda`. -/
@[simps!]
def uliftCoyonedaIsoCoyoneda {C : Type u₁} [Category.{max w v₁} C] :
    uliftCoyoneda.{w} (C := C) ≅ coyoneda :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦ Equiv.ulift.toIso))

namespace Functor

variable {C : Type u} [Category.{v} C]

/-- Transport `RepresentableBy` along an isomorphism of the object. -/
@[simps]
def RepresentableBy.ofIsoObj {F : Cᵒᵖ ⥤ Type w} {X Y : C} (R : F.RepresentableBy X)
    (e : Y ≅ X) :
    F.RepresentableBy Y where
  homEquiv {Z} := e.homToEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

/-- Transport `RepresentableBy` along an isomorphism of the object. -/
@[simps]
def CorepresentableBy.ofIsoObj {F : C ⥤ Type w} {X Y : C} (R : F.CorepresentableBy X)
    (e : Y ≅ X) :
    F.CorepresentableBy Y where
  homEquiv {Z} := e.homFromEquiv.trans R.homEquiv
  homEquiv_comp := by simp [R.homEquiv_comp]

/-- If `Y` is isomorphic to `X`, representations of `F` by `X` are equivalent
to representations of `F` by `Y`. -/
@[simps]
def RepresentableBy.equivOfIsoObj {F : Cᵒᵖ ⥤ Type w} {X Y : C} (e : Y ≅ X) :
    F.RepresentableBy X ≃ F.RepresentableBy Y where
  toFun R := R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- If `Y` is isomorphic to `X`, corepresentations of `F` by `X` are equivalent
to corepresentations of `F` by `Y`. -/
@[simps]
def CorepresentableBy.equivOfIsoObj {F : C ⥤ Type w} {X Y : C} (e : Y ≅ X) :
    F.CorepresentableBy X ≃ F.CorepresentableBy Y where
  toFun R := R.ofIsoObj e
  invFun R := R.ofIsoObj e.symm
  left_inv _ := by ext; simp
  right_inv _ := by ext; simp

/-- Representing `F` composed with universe lifting is the same as representing `F`. -/
@[simps]
def representableByUliftFunctorEquiv {F : Cᵒᵖ ⥤ Type w} {X : C} :
    (F ⋙ uliftFunctor.{w'}).RepresentableBy X ≃ F.RepresentableBy X where
  toFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

/-- Corepresenting `F` composed with universe lifting is the same as corepresenting `F`. -/
@[simps]
def corepresentableByUliftFunctorEquiv {F : C ⥤ Type w} {X : C} :
    (F ⋙ uliftFunctor.{w'}).CorepresentableBy X ≃ F.CorepresentableBy X where
  toFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift
      homEquiv_comp f g := congr($(R.homEquiv_comp _ _).down) }
  invFun R :=
    { homEquiv {Y} := R.homEquiv.trans Equiv.ulift.symm
      homEquiv_comp f g := by simp [R.homEquiv_comp] }

/-- Version of `representableByEquiv` with more general universe assumptions. -/
@[simps]
def RepresentableBy.equivUliftYoneda (F : Cᵒᵖ ⥤ Type (max w v)) (X : C) :
    F.RepresentableBy X ≃ (uliftYoneda.obj X ≅ F) where
  toFun R := NatIso.ofComponents (fun X ↦ equivEquivIso (Equiv.ulift.trans R.homEquiv)) <| by
    intro X Y f
    ext x
    exact R.homEquiv_comp f.unop _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f.op) ⟨g⟩) }

/-- Version of `corepresentableByEquiv` with more general universe assumptions. -/
@[simps]
def CorepresentableBy.equivUliftCoyoneda (F : C ⥤ Type (max w v)) (X : C) :
    F.CorepresentableBy X ≃ (uliftCoyoneda.obj (op X) ≅ F) where
  toFun R := NatIso.ofComponents (fun X ↦ equivEquivIso (Equiv.ulift.trans R.homEquiv)) <| by
    intro X Y f
    ext x
    exact R.homEquiv_comp f _
  invFun e :=
    { homEquiv {X} := Equiv.ulift.symm.trans (equivEquivIso.symm (e.app _))
      homEquiv_comp {X Y} f g := congr($(e.hom.naturality f) ⟨g⟩) }

lemma isRepresentable_comp_uliftFunctor_iff {F : Cᵒᵖ ⥤ Type w} :
    (F ⋙ uliftFunctor.{w'}).IsRepresentable ↔ F.IsRepresentable := by
  refine ⟨fun ⟨X, ⟨R⟩⟩ ↦ ?_, fun ⟨X, ⟨R⟩⟩ ↦ ?_⟩
  · exact ⟨X, ⟨representableByUliftFunctorEquiv R⟩⟩
  · exact ⟨X, ⟨representableByUliftFunctorEquiv.symm R⟩⟩

lemma isCorepresentable_comp_uliftFunctor_iff {F : C ⥤ Type w} :
    (F ⋙ uliftFunctor.{w'}).IsCorepresentable ↔ F.IsCorepresentable := by
  refine ⟨fun ⟨X, ⟨R⟩⟩ ↦ ?_, fun ⟨X, ⟨R⟩⟩ ↦ ?_⟩
  · exact ⟨X, ⟨corepresentableByUliftFunctorEquiv R⟩⟩
  · exact ⟨X, ⟨corepresentableByUliftFunctorEquiv.symm R⟩⟩

end CategoryTheory.Functor

namespace CategoryTheory.Functor

open Opposite

variable {C : Type u} [Category.{v} C]

/--
A functor `F` is represented by `X` with universal element `x : F.obj X`
if the natural transformation `yoneda.obj X ⟶ F` induced by `x` is an isomorphism.
For better universe generality, we state this manually as for every `Y`, the
induced map `(Y ⟶ X) → F.obj Y` is bijective.
-/
@[mk_iff]
structure IsRepresentedBy {F : Cᵒᵖ ⥤ Type w} {X : C} (x : F.obj (op X)) : Prop where
  bijective_map {Y : C} : Function.Bijective (fun f : Y ⟶ X ↦ F.map f.op x)

variable {F : Cᵒᵖ ⥤ Type w} {X : C} {x : F.obj (op X)}

lemma IsRepresentedBy.iff_isIso_uliftYonedaEquiv :
    F.IsRepresentedBy x ↔
      IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
  rw [isRepresentedBy_iff, NatTrans.isIso_iff_isIso_app, Opposite.op_surjective.forall]
  refine forall_congr' fun Y ↦ ?_
  rw [isIso_iff_bijective, ← Function.Bijective.of_comp_iff _ Equiv.ulift.{w}.symm.bijective,
    ← Function.Bijective.of_comp_iff' Equiv.ulift.{v}.bijective]
  rfl

/-- If `F` is represented by `X` with universal element `x : F.obj X`, modulo universe
lifting, it is isomorphic to `yoneda.obj X`. -/
@[simps! hom]
noncomputable def IsRepresentedBy.uliftYonedaIso (h : F.IsRepresentedBy x) :
    uliftYoneda.obj X ≅ F ⋙ uliftFunctor.{v} :=
  haveI : IsIso ((uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩) := by
    rwa [IsRepresentedBy.iff_isIso_uliftYonedaEquiv] at h
  asIso <| (uliftYonedaEquiv (F := F ⋙ uliftFunctor.{v})).symm ⟨x⟩

/-- The canonical representation induced by the universal element `x : F.obj X`. -/
noncomputable
def IsRepresentedBy.representableBy (h : F.IsRepresentedBy x) :
    F.RepresentableBy X :=
  Functor.representableByUliftFunctorEquiv.{v}
    ((RepresentableBy.equivUliftYoneda _ _).symm <| h.uliftYonedaIso)

@[simp]
lemma IsRepresentedBy.representableBy_homEquiv_apply (h : F.IsRepresentedBy x)
    {Y : C} (f : Y ⟶ X) :
    h.representableBy.homEquiv f = F.map f.op x :=
  rfl

lemma RepresentableBy.isRepresentedBy (R : F.RepresentableBy X) :
    F.IsRepresentedBy (R.homEquiv (𝟙 X)) := by
  rw [IsRepresentedBy.iff_isIso_uliftYonedaEquiv]
  convert (RepresentableBy.equivUliftYoneda _ _ <|
    representableByUliftFunctorEquiv.{v}.symm R).isIso_hom
  ext
  dsimp
  ext
  simp [uliftYonedaEquiv, ← homEquiv_eq]

lemma IsRepresentedBy.iff_exists_representableBy :
    F.IsRepresentedBy x ↔ ∃ (R : F.RepresentableBy X), R.homEquiv (𝟙 X) = x :=
  ⟨fun h ↦ ⟨h.representableBy, by simp⟩, fun ⟨R, h⟩ ↦ h ▸ R.isRepresentedBy⟩

lemma IsRepresentedBy.of_natIso (h : F.IsRepresentedBy x) {F' : Cᵒᵖ ⥤ Type w}
    (e : F ≅ F') :
    F'.IsRepresentedBy (e.hom.app (op X) x) := by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIso e
  simp [RepresentableBy.ofIso]

lemma IsRepresentedBy.iff_natIso {F' : Cᵒᵖ ⥤ Type w} (e : F ≅ F') :
    F'.IsRepresentedBy (e.hom.app (op X) x) ↔ F.IsRepresentedBy x :=
  ⟨fun h ↦ by simpa using h.of_natIso e.symm, fun h ↦ .of_natIso h _⟩

lemma IsRepresentedBy.of_isoObj (h : F.IsRepresentedBy x) {Y : C} (e : Y ≅ X) :
    F.IsRepresentedBy (F.map e.hom.op x) := by
  rw [iff_exists_representableBy]
  use h.representableBy.ofIsoObj e
  simp

lemma IsRepresentedBy.iff_of_isoObj {Y : C} (e : Y ≅ X) :
    F.IsRepresentedBy (F.map e.hom.op x) ↔ F.IsRepresentedBy x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.of_isoObj e⟩
  have : x = F.map e.inv.op (F.map e.hom.op x) := by
    simp [← FunctorToTypes.map_comp_apply, ← op_comp]
  exact this ▸ .of_isoObj h e.symm

lemma IsRepresentedBy.of_isRepresentable [F.IsRepresentable] : F.IsRepresentedBy F.reprx :=
  F.representableBy.isRepresentedBy

lemma IsRepresentable.iff_exists_isRepresentedBy :
    F.IsRepresentable ↔ ∃ (X : C) (x : F.obj (op X)), F.IsRepresentedBy x :=
  ⟨fun _ ↦ ⟨F.reprX, F.reprx, .of_isRepresentable⟩,
    fun ⟨_, _, h⟩ ↦ h.representableBy.isRepresentable⟩

end CategoryTheory.Functor
