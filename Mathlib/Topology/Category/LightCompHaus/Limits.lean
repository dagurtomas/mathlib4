/-
Copyright (c) 2024 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.CompHausLike.Limits
import Mathlib.Topology.Category.LightCompHaus.Basic
/-!

# Explicit limits and colimits

This file applies the general API for explicit limits and colimits in `CompHausLike P` (see
the file `Mathlib/Topology/Category/CompHausLike/Limits.lean`) to the special case of
`LightCompHaus`.
-/

namespace LightCompHaus

universe u w

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
