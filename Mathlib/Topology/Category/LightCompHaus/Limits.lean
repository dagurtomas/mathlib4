/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.CompHaus.Basic
-- import Mathlib.Topology.Category.LightCompHaus.Basic
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of
`LightCompHaus`.
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
