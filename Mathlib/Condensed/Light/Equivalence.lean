/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightCompHaus.EffectiveEpi
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular
import Mathlib.Condensed.Light.Basic
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
/-!

# The category of light condensed sets is equivalent to sheaves on "light" compact Hausdorff spaces.

-/

open CategoryTheory Function

def lightProfiniteToLightCompHaus : LightProfinite ⥤ LightCompHaus :=
  CompHausLike.toCompHausLike (fun _ ↦ inferInstance)

def lightProfiniteToLightCompHausFullyFaithful : lightProfiniteToLightCompHaus.FullyFaithful :=
  CompHausLike.fullyFaithfulToCompHausLike _

instance : lightProfiniteToLightCompHaus.Full := lightProfiniteToLightCompHausFullyFaithful.full

instance : lightProfiniteToLightCompHaus.Faithful :=
  lightProfiniteToLightCompHausFullyFaithful.faithful

instance : Limits.PreservesFiniteCoproducts lightProfiniteToLightCompHaus :=
  inferInstanceAs (Limits.PreservesFiniteCoproducts (CompHausLike.toCompHausLike _))

instance : lightProfiniteToLightCompHaus.PreservesEffectiveEpis where
  preserves _ h :=
    (LightCompHaus.effectiveEpi_iff_surjective _).mpr
      ((LightProfinite.effectiveEpi_iff_surjective _).mp h)

instance : lightProfiniteToLightCompHaus.ReflectsEffectiveEpis where
  reflects _ h :=
    (LightProfinite.effectiveEpi_iff_surjective _).mpr
      ((LightCompHaus.effectiveEpi_iff_surjective _).mp h)

theorem hausdorff_alexandroff (X : Type*) [TopologicalSpace X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] : ∃ f : ((i : ℕ) → Bool) → X, Continuous f ∧ Surjective f := by
  sorry

/--
An effective presentation of an `X : Profinite` with respect to the inclusion functor from `Stonean`
-/
noncomputable def lightProfiniteToLightCompHausEffectivePresentation (X : LightCompHaus) :
    lightProfiniteToLightCompHaus.EffectivePresentation X where
  p := LightProfinite.of ((i : ℕ) → Bool)
  f := CompHausLike.ofHom _ ⟨(hausdorff_alexandroff X).choose,
    (hausdorff_alexandroff X).choose_spec.1⟩
  effectiveEpi := by
    rw [LightCompHaus.effectiveEpi_iff_surjective]
    exact (hausdorff_alexandroff X).choose_spec.2

instance : lightProfiniteToLightCompHaus.{0}.EffectivelyEnough where
  presentation X := ⟨lightProfiniteToLightCompHausEffectivePresentation X⟩


open CategoryTheory Limits

namespace LightCondensed

/-- The equivalence from coherent sheaves on `Profinite` to coherent sheaves on `CompHaus`
    (i.e. condensed sets). -/
noncomputable
def equivalence (A : Type*) [Category A]
    [∀ X, HasLimitsOfShape (StructuredArrow X lightProfiniteToLightCompHaus.op) A] :
    LightCondensed A ≌ Sheaf (coherentTopology LightCompHaus) A :=
  coherentTopology.equivalence' lightProfiniteToLightCompHaus A

end LightCondensed
