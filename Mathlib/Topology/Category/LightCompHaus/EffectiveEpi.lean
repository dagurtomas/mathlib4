/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.CompHaus.Basic
/-!

# Effective epimorphisms in `LightCompHaus`

This file proves that `EffectiveEpi` and `Surjective` are equivalent in `LightCompHaus`.
As a consequence we deduce from the material in
`Mathlib/Topology/Category/CompHausLike/EffectiveEpi.lean` that `LightCompHaus` is `Preregular`
and `Precoherent`.
-/

universe u w

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
Hausdorff and second countable topological space.
-/
abbrev of (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] : LightCompHaus :=
  CompHausLike.of _ X

instance : Inhabited LightCompHaus :=
  ⟨LightCompHaus.of PEmpty⟩

instance {X : LightCompHaus} : SecondCountableTopology X :=
  X.prop

end LightCompHaus

/-- The fully faithful embedding of `LightCompHaus` in `CompHaus`. -/
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

open CategoryTheory Limits CompHausLike

instance : HasExplicitPullbacks (fun Y ↦ SecondCountableTopology Y) where
  hasProp _ _ := {
    hasProp := show SecondCountableTopology {_xy : _ | _} from inferInstance }

instance : HasExplicitFiniteCoproducts.{w, u} (fun Y ↦ SecondCountableTopology Y) where
  hasProp _ := { hasProp :=
    show SecondCountableTopology (Σ (_a : _), _) from inferInstance }

/-- A one-element space is terminal in `LightCompHaus` -/
abbrev isTerminalPUnit : IsTerminal (LightCompHaus.of PUnit.{u + 1}) :=
  CompHausLike.isTerminalPUnit

example : FinitaryExtensive LightCompHaus.{u} := inferInstance

noncomputable example : PreservesFiniteCoproducts lightToCompHaus.{u} := inferInstance

end LightCompHaus

-- open CategoryTheory Limits CompHausLike

namespace LightCompHaus

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

theorem effectiveEpi_iff_surjective {X Y : LightCompHaus.{u}} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨effectiveEpiStruct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

instance : Preregular LightCompHaus.{u} := by
  apply CompHausLike.preregular
  intro _ _ f
  exact (effectiveEpi_iff_surjective f).mp

example : Precoherent LightCompHaus.{u} := inferInstance

end LightCompHaus
