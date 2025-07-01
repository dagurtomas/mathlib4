/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Limits.Shapes.Countable
import Mathlib.Topology.Category.CompHaus.Basic
/-!

# Light profinite spaces

We construct the category `LightCompHaus` of light profinite topological spaces. These are
implemented as totally disconnected second countable compact Hausdorff spaces.

This file also defines the category `LightDiagram`, which consists of those spaces that can be
written as a sequential limit (in `Profinite`) of finite sets.

We define an equivalence of categories `LightCompHaus ≌ LightDiagram` and prove that these are
essentially small categories.

## Implementation

The category `LightCompHaus` is defined using the structure `CompHausLike`. See the file
`CompHausLike.Basic` for more information.

-/

/- The basic API for `LightCompHaus` is largely copied from the API of `Profinite`;
where possible, try to keep them in sync -/

universe v u

open CategoryTheory Limits Opposite Topology TopologicalSpace CompHausLike

/-- `LightCompHaus` is the category of second countable compact Hausdorff spaces. -/
abbrev LightCompHaus := CompHausLike
  (fun X ↦ SecondCountableTopology X)

namespace LightCompHaus

instance (X : Type*) [TopologicalSpace X]
    [SecondCountableTopology X] : HasProp (fun Y ↦ SecondCountableTopology Y) X :=
  ⟨(inferInstanceAs (SecondCountableTopology X))⟩

/--
Construct a term of `LightCompHaus` from a type endowed with the structure of a compact,
Hausdorff, totally disconnected and second countable topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] : LightCompHaus :=
  CompHausLike.of _ X

instance : Inhabited LightCompHaus :=
  ⟨LightCompHaus.of PEmpty⟩

instance {X : LightCompHaus} : SecondCountableTopology X :=
  X.prop

end LightCompHaus

/-- The fully faithful embedding of `LightCompHaus` in `Profinite`. -/
abbrev lightToCompHaus : LightCompHaus ⥤ CompHaus :=
  compHausLikeToCompHaus _

/-- `lightToCompHaus` is fully faithful. -/
abbrev lightToCompHausFullyFaithful : lightToCompHaus.FullyFaithful :=
  fullyFaithfulToCompHausLike _

/-- The fully faithful embedding of `LightCompHaus` in `TopCat`.
This is definitionally the same as the obvious composite. -/
abbrev LightCompHaus.toTopCat : LightCompHaus ⥤ TopCat :=
  CompHausLike.compHausLikeToTop _

namespace LightCompHaus

/-- An explicit limit cone for a functor `F : J ⥤ LightCompHaus`, for a countable category `J`
  defined in terms of `CompHaus.limitCone`, which is defined in terms of `TopCat.limitCone`. -/
def limitCone {J : Type v} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ LightCompHaus.{max u v}) :
    Limits.Cone F where
  pt :=
    { toTop := (CompHaus.limitCone.{v, u} (F ⋙ lightToCompHaus)).pt.toTop
      prop := by
        change SecondCountableTopology ({ u : ∀ j : J, F.obj j | _ } : Type _)
        apply IsInducing.subtypeVal.secondCountableTopology }
  π :=
  { app := (CompHaus.limitCone.{v, u} (F ⋙ lightToCompHaus)).π.app
    naturality := by
      intro j k f
      ext ⟨g, p⟩
      exact (p f).symm }

/-- The limit cone `LightCompHaus.limitCone F` is indeed a limit cone. -/
def limitConeIsLimit {J : Type v} [SmallCategory J] [CountableCategory J]
    (F : J ⥤ LightCompHaus.{max u v}) :
    Limits.IsLimit (limitCone F) where
  lift S :=
    (CompHaus.limitConeIsLimit.{v, u} (F ⋙ lightToCompHaus)).lift
      (lightToCompHaus.mapCone S)
  uniq S _ h := (CompHaus.limitConeIsLimit.{v, u} _).uniq (lightToCompHaus.mapCone S) _ h

noncomputable instance createsCountableLimits {J : Type v} [SmallCategory J] [CountableCategory J] :
    CreatesLimitsOfShape J lightToCompHaus.{max v u} where
  CreatesLimit {F} :=
    createsLimitOfFullyFaithfulOfIso (limitCone.{v, u} F).pt <|
      (CompHaus.limitConeIsLimit.{v, u} (F ⋙ lightToCompHaus)).conePointUniqueUpToIso
        (limit.isLimit _)

instance : HasCountableLimits LightCompHaus where
  out _ := { has_limit := fun F ↦ ⟨limitCone F, limitConeIsLimit F⟩ }

-- instance : PreservesLimitsOfShape ℕᵒᵖ (forget LightCompHaus.{u}) :=
--   have : PreservesLimitsOfSize.{0, 0} (forget CompHaus.{u}) := preservesLimitsOfSize_shrink _
--   inferInstanceAs (PreservesLimitsOfShape ℕᵒᵖ (lightToCompHaus ⋙ forget CompHaus))

variable {X Y : LightCompHaus.{u}} (f : X ⟶ Y)

/-- Any morphism of light profinite spaces is a closed map. -/
theorem isClosedMap : IsClosedMap f :=
  CompHausLike.isClosedMap _

/-- Any continuous bijection of light profinite spaces induces an isomorphism. -/
theorem isIso_of_bijective (bij : Function.Bijective f) : IsIso f :=
  haveI := CompHausLike.isIso_of_bijective (lightToCompHaus.map f) bij
  isIso_of_fully_faithful lightToCompHaus _

/-- Any continuous bijection of light profinite spaces induces an isomorphism. -/
noncomputable def isoOfBijective (bij : Function.Bijective f) : X ≅ Y :=
  letI := LightCompHaus.isIso_of_bijective f bij
  asIso f

instance forget_reflectsIsomorphisms : (forget LightCompHaus).ReflectsIsomorphisms := by
  constructor
  intro A B f hf
  rw [isIso_iff_bijective] at hf
  exact LightCompHaus.isIso_of_bijective _ hf

theorem epi_iff_surjective {X Y : LightCompHaus.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.continuous).isClosed
    let D := ({y} : Set Y)
    have hD : IsClosed D := isClosed_singleton
    have hCD : Disjoint C D := by
      rw [Set.disjoint_singleton_right]
      rintro ⟨y', hy'⟩
      exact hy y' hy'
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_isClosed hC hD hCD
    haveI : CompactSpace (ULift.{u} <| Set.Icc (0 : ℝ) 1) := Homeomorph.ulift.symm.compactSpace
    haveI : T2Space (ULift.{u} <| Set.Icc (0 : ℝ) 1) := Homeomorph.ulift.symm.t2Space
    let Z := of (ULift.{u} <| Set.Icc (0 : ℝ) 1)
    let g : Y ⟶ Z := ofHom _
      ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩,
        continuous_uliftUp.comp (φ.continuous.subtype_mk fun y' => hφ01 y')⟩
    let h : Y ⟶ Z := ofHom _
      ⟨fun _ => ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by
      rw [← cancel_epi f]
      ext x : 4
      simp [g, h, Z, hφ0 (Set.mem_range_self x)]
    apply_fun fun e => (e y).down.1 at H
    dsimp [g, h, Z] at H
    simp only [hφ1 (Set.mem_singleton y), Pi.one_apply] at H
    exact zero_ne_one H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget LightCompHaus).epi_of_epi_map

instance : lightToCompHaus.PreservesEpimorphisms where
  preserves f _ := (CompHaus.epi_iff_surjective _).mpr ((epi_iff_surjective f).mp inferInstance)

end LightCompHaus
