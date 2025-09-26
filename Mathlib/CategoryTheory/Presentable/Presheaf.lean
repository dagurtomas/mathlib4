import Mathlib

universe v u

namespace CategoryTheory

open Limits Functor

variable {C : Type u} [Category.{v} C] (X : C)

instance : IsFinitelyPresentable (yoneda.obj X) := sorry

variable (J : GrothendieckTopology C)

section

variable (A : Type*) [Category A] [HasWeakSheafify J A]

instance : (sheafToPresheaf J A ⋙ presheafToSheaf J A).IsEquivalence where
  faithful := Faithful.of_iso (asIso (sheafificationAdjunction J A).counit).symm
  full := Full.of_iso (asIso (sheafificationAdjunction J A).counit).symm
  essSurj := { mem_essImage X := ⟨X, ⟨(asIso (sheafificationAdjunction J A).counit).app X⟩⟩ }

end

namespace GrothendieckTopology

class IsFinitelyCovered (J : GrothendieckTopology C) (X : C) : Prop where
  exists_finite (S : Sieve X) (_ : S ∈ J X) :
    ∃ (P : Presieve X), P.uncurry.Finite ∧ .generate P ∈ J X ∧ P ≤ S

abbrev IsFinitary (J : GrothendieckTopology C) := ∀ X, J.IsFinitelyCovered X

variable {J : GrothendieckTopology C}

attribute [local instance] Types.instConcreteCategory

instance (U : C) [J.IsFinitelyCovered U] :
    PreservesFilteredColimits ((sheafSections J (Type max u v)).obj ⟨U⟩) where
  preserves_filtered_colimits I := { preservesColimit {K} := { preserves {c} hc := sorry } }

end GrothendieckTopology

end CategoryTheory
