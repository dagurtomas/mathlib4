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

-- abbrev IsFinitary (J : GrothendieckTopology C) := ∀ X, J.IsFinitelyCovered X

class IsFinitary (J : GrothendieckTopology C) : Prop where
  exists_finite : ∃ K : Coverage C, (∀ X : C, ∀ P, P ∈ K X → P.uncurry.Finite) ∧
    K.toGrothendieck = J

variable {J : GrothendieckTopology C}

attribute [local instance] Types.instConcreteCategory

@[simps]
def pointwiseCocone {A I : Type*} [Category A] [Category I] {K : I ⥤ Sheaf J A}
    (c : Cocone (K ⋙ sheafToPresheaf J A)) (hcpt : Presheaf.IsSheaf J c.pt) : Cocone K where
  pt := ⟨c.pt, hcpt⟩
  ι := {
    app X := ⟨c.ι.app X⟩
    naturality _ _ f := by
      ext1
      simpa using c.ι.naturality f }

def pointwiseCoconeIsColimit {A I : Type*} [Category A] [Category I] {K : I ⥤ Sheaf J A}
    (c : Cocone (K ⋙ sheafToPresheaf J A)) (hcpt : Presheaf.IsSheaf J c.pt) (hc : IsColimit c) :
    IsColimit (pointwiseCocone c hcpt) where
  desc s := ⟨hc.desc ((sheafToPresheaf _ _).mapCocone s)⟩
  uniq s m h := by
    ext1
    apply hc.uniq ((sheafToPresheaf _ _).mapCocone s)
    intro i
    simpa using Sheaf.hom_ext_iff.mp (h i)

lemma isSheafFor_colimit_of_finite {I : Type*} [Category I] [IsFiltered I]
    {K : I ⥤ Sheaf J (Type max u v)} (c : Cocone (K ⋙ sheafToPresheaf _ _)) (hc : IsColimit c)
    {X : C} (R : Presieve X) (hR : R.uncurry.Finite) :
    Presieve.IsSheafFor c.pt R := by
  sorry

lemma isSheaf_colimit_of_finitary {I : Type*} [Category I] [IsFiltered I] [J.IsFinitary]
    {K : I ⥤ Sheaf J (Type max u v)} (c : Cocone (K ⋙ sheafToPresheaf _ _)) (hc : IsColimit c) :
    Presieve.IsSheaf J c.pt := by
  obtain ⟨L, h, rfl⟩ := IsFinitary.exists_finite (J := J)
  rw [Presieve.isSheaf_coverage]
  intro X R hR
  apply isSheafFor_colimit_of_finite c hc
  grind

instance [J.IsFinitary] (U : C) :
    PreservesFilteredColimits ((sheafSections J (Type max u v)).obj ⟨U⟩) where
  preserves_filtered_colimits I := { preservesColimit {K} := { preserves {c} hc := sorry } }

end GrothendieckTopology

end CategoryTheory
