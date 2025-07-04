import Mathlib
import Mathlib.CategoryTheory.Limits.PresheafUniv

noncomputable section

universe v v' u u' v₃ u₃

open CategoryTheory Limits ObjectProperty Functor

variable {C : Type u} {D : Type u'} [Category.{v} C] [Category.{v} D]
  [HasFilteredColimitsOfSize.{v, v} D]

namespace CategoryTheory

variable (C D) in
abbrev Functor' := ObjectProperty.FullSubcategory
  (C := Ind C ⥤ D) (fun G ↦ PreservesFilteredColimitsOfSize.{v, v} G)

variable (C D) in
def Ind.precompYoneda : Functor' C D ⥤ C ⥤ D :=
  ObjectProperty.ι _ ⋙ (whiskeringLeft _ _ _).obj Ind.yoneda

def Ind.costructuredArrowEquivalence (X : Ind C) :
    CostructuredArrow Ind.yoneda X ≌ CostructuredArrow yoneda X.1 :=
  (asEquivalence (CostructuredArrow.post Ind.yoneda (Ind.inclusion C) X)).trans
    (CostructuredArrow.mapNatIso yonedaCompInclusion)

instance (X : Ind C) : IsFiltered (CostructuredArrow Ind.yoneda X) := by
  exact RepresentablyCoflat.filtered X

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow Ind.yoneda X) D :=
  Functor.Final.hasColimitsOfShape_of_final (E := D)
    (X.presentation.toCostructuredArrow ⋙ (Ind.costructuredArrowEquivalence X).inverse)

instance (F : Ind C ⥤ D) [PreservesFilteredColimitsOfSize.{v, v} F] (X : Ind C) :
    PreservesColimitsOfShape (CostructuredArrow Ind.yoneda X) F :=
  Functor.Final.preservesColimitsOfShape_of_final
    (X.presentation.toCostructuredArrow ⋙ (Ind.costructuredArrowEquivalence X).inverse) _

def Ind.lan : (C ⥤ D) ⥤ Ind C ⥤ D := Ind.yoneda.lan

def Ind.yonedaLanAdj : Ind.lan (C := C) (D := D) ⊣ (whiskeringLeft _ _ _).obj Ind.yoneda :=
  Ind.yoneda.lanAdjunction D

instance (F : C ⥤ D) : IsIso ((Ind.yonedaLanAdj (C := C) (D := D)).unit.app F) := by
  dsimp [Ind.yonedaLanAdj]
  infer_instance

instance : IsIso (Ind.yonedaLanAdj (C := C) (D := D)).unit := by
  apply NatIso.isIso_of_isIso_app

def Ind.lanFullyFaithful : (Ind.lan (C := C) (D := D)).FullyFaithful :=
  (Ind.yonedaLanAdj (C := C) (D := D)).fullyFaithfulLOfIsIsoUnit

instance : (Ind.lan (C := C) (D := D)).Full := Ind.lanFullyFaithful.full

instance : (Ind.lan (C := C) (D := D)).Faithful := Ind.lanFullyFaithful.faithful

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow yoneda
    ((Ind.inclusion (C := C)).obj X)) (Ind C) :=
  Functor.Final.hasColimitsOfShape_of_final (E := Ind C) (X.presentation.toCostructuredArrow)

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow yoneda X.obj) (Ind C) :=
  Functor.Final.hasColimitsOfShape_of_final (E := Ind C) (X.presentation.toCostructuredArrow)

instance (X : Ind C) : HasColimitsOfShape (CostructuredArrow Ind.yoneda X) (Ind C) := inferInstance

def Ind.isoColimit (X : Ind C) : X ≅
    colimit (CostructuredArrow.proj Ind.yoneda X ⋙ Ind.yoneda) := by
  refine X.colimitPresentationCompYoneda.symm ≪≫ ?_
  let j : X.presentation.F ≅ X.presentation.toCostructuredArrow ⋙
      CostructuredArrow.proj yoneda X.obj :=
    Iso.refl _
  refine colim.mapIso (isoWhiskerRight j _) ≪≫ colim.mapIso (Functor.associator _ _ _) ≪≫
    Functor.Final.colimitIso _ _ ≪≫
    (HasColimit.isoOfEquivalence (Ind.costructuredArrowEquivalence X) (Iso.refl _)).symm

attribute [local instance] preservesColimitsOfSize_rightOp

instance (F : C ⥤ D) : PreservesFilteredColimitsOfSize.{v, v} (Ind.lan.obj F) where
  preserves_filtered_colimits J _ _ := by
    let D' : Type _ := (D ⥤ Type v)ᵒᵖ
    letI : Category D' := inferInstance
    let i : D ⥤ D' := coyoneda.rightOp
    have : (yoneda ⋙ (whiskeringRight _ _ _).obj
        uliftFunctor.{max u' v}).HasPointwiseLeftKanExtension (F ⋙ i) := by
      sorry
    let H := leftKanExtension (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{max u' v}) (F ⋙ i)
    let α : F ⋙ i ⟶ Ind.yoneda ⋙ (Ind.inclusion C ⋙
        (whiskeringRight _ _ _).obj uliftFunctor.{max u' v} ⋙ H) :=
      (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{max u' v}).leftKanExtensionUnit (F ⋙ i) ≫
        (Functor.associator _ _ _).hom ≫ (isoWhiskerRight Ind.yonedaCompInclusion _).inv ≫
          (Functor.associator _ _ _).hom
    let β : F ⟶ Ind.yoneda ⋙ Ind.lan.obj F := leftKanExtensionUnit _ _

    --
    -- have hi : i.PreservesPointwiseLeftKanExtension F Ind.yoneda := by
    --   intro X
    --   dsimp [i]
    --   infer_instance

    --
    -- have hi' : i.PreservesPointwiseLeftKanExtension F
    --     (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{max u' v})  := by
    --   intro X
    --   dsimp [i]
    --   infer_instance


    --
    -- have : PreservesColimitsOfShape J H := by
    --   dsimp [H]
    --   infer_instance

    have hβ : (Ind.lan.obj F).IsLeftKanExtension β := by stop
      dsimp [β, Ind.lan, Functor.lan]
      infer_instance

    --
    -- have hβi : (Ind.lan.obj F ⋙ i).IsLeftKanExtension
    --     ((whiskerRight β i) ≫ (Functor.associator _ _ _).hom) := by
    --   infer_instance

    --
    have : H.IsLeftKanExtension ((yoneda ⋙ (whiskeringRight _ _ _).obj
        uliftFunctor.{max u' v}).leftKanExtensionUnit (F ⋙ i)) := by stop
      dsimp [H]
      infer_instance

    have hα : (Ind.inclusion C ⋙
        (whiskeringRight _ _ _).obj uliftFunctor.{max u' v} ⋙ H).IsLeftKanExtension α := by
      sorry

    let e : (Ind.inclusion C ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{max u' v} ⋙ H) ≅
        Ind.lan.obj F ⋙ i :=
      (Ind.inclusion C ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{max u' v} ⋙
        H).leftKanExtensionUnique α (Ind.lan.obj F ⋙ i)
          (((whiskerRight β i) ≫ (Functor.associator _ _ _).hom))
    suffices PreservesColimitsOfShape J (Ind.lan.obj F ⋙ i) by
      apply preservesColimitsOfShape_of_reflects_of_preserves _ i
    exact preservesColimitsOfShape_of_natIso e

lemma foo : (Ind.lan (C := C) (D := D)).essImage =
    (fun G ↦ PreservesFilteredColimitsOfSize.{v, v} G) := by
  ext F
  constructor
  · intro h
    obtain ⟨G, ⟨i⟩⟩ := h
    constructor
    intro J _ _
    exact preservesColimitsOfShape_of_natIso i
  · intro h
    refine ⟨Ind.yoneda ⋙ F, ⟨?_⟩⟩
    let i : Ind.lan.obj (Ind.yoneda ⋙ F) ≅
        pointwiseLeftKanExtension Ind.yoneda (Ind.yoneda ⋙ F) :=
      sorry
    refine i ≪≫ NatIso.ofComponents (fun X ↦
      colim.mapIso (Functor.associator _ _ _).symm ≪≫
        (preservesColimitIso F _).symm ≪≫ F.mapIso X.isoColimit.symm) ?_
    sorry

/--
`Functor' C D` is the full subcategory of `Ind C ⥤ D` spanned by the functors which preserve
filtered colimits.
-/
def Ind.universalProperty : Functor' C D ≌ C ⥤ D :=
  Equivalence.trans (ObjectProperty.fullSubcategoryCongr (foo (C := C) (D := D))).symm
    (asEquivalence ((Ind.lan (C := C) (D := D)).toEssImage)).symm

end CategoryTheory
