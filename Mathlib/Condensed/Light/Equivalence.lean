/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
import Mathlib.Condensed.Light.Basic
/-!

# The category of light condensed sets is equivalent to sheaves on "light" compact Hausdorff spaces.

-/

universe u w

open CategoryTheory Limits Opposite Topology TopologicalSpace CompHausLike Function

/-- `LightCompHaus` is the category of second countable compact Hausdorff spaces. -/
abbrev LightCompHaus := CompHausLike (fun X ↦ SecondCountableTopology X)

namespace LightCompHaus

/--
This is a technical declaration saying that a topological space is second countable, in a
slightly weird way to make it work with the `CompHausLike` API.
-/
instance (X : Type*) [TopologicalSpace X] [SecondCountableTopology X] :
    HasProp (fun Y ↦ SecondCountableTopology Y) X :=
  ⟨(inferInstanceAs (SecondCountableTopology X))⟩

/--
Objects of `LightCompHaus` are second countable topological spaces.
-/
instance {X : LightCompHaus} : SecondCountableTopology X := X.prop

/--
This declaration says that `LightCompHaus` has pullbacks, again using the `CompHausLike` API.
For example, this gives an explicit description of the pullback as a subset of the product,
along with the fact that the inclusion functor to `CompHaus` preserves pullbacks.
-/
instance : HasExplicitPullbacks (fun Y ↦ SecondCountableTopology Y) where
  hasProp _ _ := { hasProp := inferInstanceAs <| SecondCountableTopology {_xy : _ | _} }

/--
This declaration says that `LightCompHaus` has finite coproducts, again using the `CompHausLike`
API. For example, this gives an explicit description of the coproduct as a sigma-type (i.e.
disjoint union) along with the fact that the inclusion functor to `CompHaus` preserves finite
coproducts.
-/
instance : HasExplicitFiniteCoproducts.{w, u} (fun Y ↦ SecondCountableTopology Y) where
  hasProp _ := { hasProp := inferInstanceAs <| SecondCountableTopology (Σ (_a : _), _) }

end LightCompHaus

namespace LightCompHaus

/--
Epimorphisms and surjective morphisms coincide in `LightCompHaus`.
-/
lemma epi_iff_surjective {X Y : LightCompHaus.{u}} (f : X ⟶ Y) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · dsimp [Function.Surjective]
    contrapose!
    rintro ⟨y, hy⟩ hf
    let C := Set.range f
    have hC : IsClosed C := (isCompact_range f.hom.continuous).isClosed
    let D : Set Y := {y}
    have hCD : Disjoint C D := by simp_all [C, D]
    obtain ⟨φ, hφ0, hφ1, hφ01⟩ := exists_continuous_zero_one_of_isClosed hC isClosed_singleton hCD
    let Z : LightCompHaus := CompHausLike.of _ (ULift.{u} <| Set.Icc (0 : ℝ) 1)
    let g : Y ⟶ Z := ofHom _ ⟨fun y' => ⟨⟨φ y', hφ01 y'⟩⟩, by continuity⟩
    let h : Y ⟶ Z := ofHom _ ⟨fun _ => ⟨⟨0, Set.left_mem_Icc.mpr zero_le_one⟩⟩, continuous_const⟩
    have H : h = g := by rw [← cancel_epi f]; ext; simp [g, h, Z, hφ0 (Set.mem_range_self _)]
    apply_fun fun e => (e y).down.1 at H
    simp [g, h, Z, hφ1 (Set.mem_singleton y)] at H
  · rw [← CategoryTheory.epi_iff_surjective]
    apply (forget LightCompHaus).epi_of_epi_map

/--
Effective epimorphisms and surjective morphisms coincide in `LightCompHaus`.
-/
lemma effectiveEpi_iff_surjective {X Y : LightCompHaus.{u}} (f : X ⟶ Y) :
    EffectiveEpi f ↔ Function.Surjective f := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨⟨effectiveEpiStruct f h⟩⟩⟩
  rw [← epi_iff_surjective]
  infer_instance

/--
`LightCompHaus` is a preregular category.
-/
instance : Preregular LightCompHaus.{u} := by
  apply CompHausLike.preregular
  intro _ _ f
  exact (effectiveEpi_iff_surjective f).mp

/--
`LightCompHaus` is finitary extensive.
-/
example : FinitaryExtensive LightCompHaus.{u} := inferInstance

/--
`LightCompHaus` is a precoherent category (because it is preregular and finitary extensive).
This allows us to define the coherent Grothendieck topology on `LightCompHaus`.
-/
example : Precoherent LightCompHaus.{u} := inferInstance

end LightCompHaus

/--
The functor from `LightProfinite` to `LightCompHaus`.
-/
def lightProfiniteToLightCompHaus : LightProfinite ⥤ LightCompHaus :=
  CompHausLike.toCompHausLike (fun _ ↦ inferInstance)

/--
The functor from `LightProfinite` to `LightCompHaus` is full.
-/
instance : lightProfiniteToLightCompHaus.Full := (CompHausLike.fullyFaithfulToCompHausLike _).full

/--
The functor from `LightProfinite` to `LightCompHaus` is faithful.
-/
instance : lightProfiniteToLightCompHaus.Faithful :=
  (CompHausLike.fullyFaithfulToCompHausLike _).faithful

/--
The functor from `LightProfinite` to `LightCompHaus` preserves finite coproducts.
-/
instance : Limits.PreservesFiniteCoproducts lightProfiniteToLightCompHaus :=
  inferInstanceAs (Limits.PreservesFiniteCoproducts (CompHausLike.toCompHausLike _))

/--
The functor from `LightProfinite` to `LightCompHaus` preserves effective epimorphisms.
-/
instance : lightProfiniteToLightCompHaus.PreservesEffectiveEpis where
  preserves _ h :=
    (LightCompHaus.effectiveEpi_iff_surjective _).mpr
      ((LightProfinite.effectiveEpi_iff_surjective _).mp h)

/--
The functor from `LightProfinite` to `LightCompHaus` reflects effective epimorphisms.
-/
instance : lightProfiniteToLightCompHaus.ReflectsEffectiveEpis where
  reflects _ h :=
    (LightProfinite.effectiveEpi_iff_surjective _).mpr
      ((LightCompHaus.effectiveEpi_iff_surjective _).mp h)

/--
The Hausdorff-Alexandroff theorem: every second countable compact Hausdorff space admits a
continuous surjection from the Cantor set.

This is the only `sorry` we depend on here, but this theorem has been formalized in Lean
and is in the process of being merged into mathlib.
-/
theorem hausdorff_alexandroff (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] : ∃ f : ((i : ℕ) → Bool) → X, Continuous f ∧ Surjective f := by
  sorry

/--
An effective presentation of an `X : LightCompHaus` with respect to the inclusion functor from
`LightProfinite`
-/
noncomputable def lightProfiniteToLightCompHausEffectivePresentation (X : LightCompHaus) :
    lightProfiniteToLightCompHaus.EffectivePresentation X where
  p := LightProfinite.of ((i : ℕ) → Bool)
  f := CompHausLike.ofHom _ ⟨(hausdorff_alexandroff X).choose,
    (hausdorff_alexandroff X).choose_spec.1⟩
  effectiveEpi := by
    rw [LightCompHaus.effectiveEpi_iff_surjective]
    exact (hausdorff_alexandroff X).choose_spec.2

/--
The functor from `LightProfinite` to `LightCompHaus` satisfies the condition in the general theorem
about equivalence of sheaf categories about every object admitting an effective epimorphism from
objects in the source.
-/
instance : lightProfiniteToLightCompHaus.{0}.EffectivelyEnough where
  presentation X := ⟨lightProfiniteToLightCompHausEffectivePresentation X⟩

open CategoryTheory Limits

/--
The equivalence from coherent sheaves on `LightProfinite` (i.e. light condensed sets) to coherent
sheaves on `LightCompHaus`.
-/
noncomputable
def LightCondensed.equivalence (A : Type*) [Category A]
    [∀ X, HasLimitsOfShape (StructuredArrow X lightProfiniteToLightCompHaus.op) A] :
    LightCondensed A ≌ Sheaf (coherentTopology LightCompHaus) A :=
  coherentTopology.equivalence' lightProfiniteToLightCompHaus A
