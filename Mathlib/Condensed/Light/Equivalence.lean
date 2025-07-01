/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib.Topology.Category.LightCompHaus.ProfiniteComparison
import Mathlib.Condensed.Light.Basic
import Mathlib.CategoryTheory.Sites.Coherent.SheafComparison
/-!

# The category of light condensed sets is equivalent to sheaves on "light" compact Hausdorff spaces.

-/

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
