import Mathlib.Topology.Category.LightCompHaus.EffectiveEpi
import Mathlib.Topology.Category.LightProfinite.EffectiveEpi
import Mathlib.CategoryTheory.Sites.Coherent.ReflectsPreregular

open CategoryTheory

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

/--
An effective presentation of an `X : Profinite` with respect to the inclusion functor from `Stonean`
-/
noncomputable def lightProfiniteToLightCompHausEffectivePresentation (X : LightCompHaus) :
    lightProfiniteToLightCompHaus.EffectivePresentation X where
  p := LightProfinite.of ((i : ℕ) → Bool)
  f := sorry
  effectiveEpi := sorry

instance : lightProfiniteToLightCompHaus.{0}.EffectivelyEnough where
  presentation X := ⟨lightProfiniteToLightCompHausEffectivePresentation X⟩
