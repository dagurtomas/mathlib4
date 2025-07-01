/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.EffectiveEpi
import Mathlib.Topology.Category.LightCompHaus.Limits
/-!

# Effective epimorphisms in `LightCompHaus`

This file proves that `EffectiveEpi` and `Surjective` are equivalent in `LightCompHaus`.
As a consequence we deduce from the material in
`Mathlib/Topology/Category/CompHausLike/EffectiveEpi.lean` that `LightCompHaus` is `Preregular`
and `Precoherent`.
-/

universe u

open CategoryTheory Limits CompHausLike

namespace LightCompHaus

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
