import Mathlib

noncomputable section

section ProObject

universe v v' u u'

open Opposite

namespace CategoryTheory.Limits

section NonSmall

variable {C : Type u} [Category.{v} C]

/-- The data that witnesses that a copresheaf `A` is a pro-object. It consists of a small
    cofiltered indexing category `I`, a diagram `F : I ⥤ C` and the data for a limit cone on
    `F ⋙ coyoneda : I ⥤ C ⥤ Type v` with cocone point `A`. -/
structure ProObjectPresentation (A : (C ⥤ Type v)ᵒᵖ) where
  /-- The indexing category of the cofiltered limit presentation -/
  I : Type v
  /-- The indexing category of the cofiltered limit presentation -/
  [ℐ : SmallCategory I]
  [hI : IsCofiltered I]
  /-- The diagram of the cofiltered limit presentation -/
  F : I ⥤ C
  /-- Use `IndObjectPresentation.cocone` instead. -/
  π : (Functor.const I).obj A ⟶ F ⋙ coyoneda.rightOp
  /-- Use `IndObjectPresentation.coconeIsColimit` instead. -/
  isLimit : IsLimit (Cone.mk A π)

namespace ProObjectPresentation

/-- Alternative constructor for `IndObjectPresentation` taking a cocone instead of its defining
    natural transformation. -/
@[simps]
def ofCone {I : Type v} [SmallCategory I] [IsCofiltered I] {F : I ⥤ C}
    (c : Cone (F ⋙ coyoneda.rightOp)) (hc : IsLimit c) : ProObjectPresentation c.pt where
  I := I
  F := F
  π := c.π
  isLimit := hc

variable {A : (C ⥤ Type v)ᵒᵖ} (P : ProObjectPresentation A)

instance : SmallCategory P.I := P.ℐ
instance : IsCofiltered P.I := P.hI

/-- The (colimit) cocone with cocone point `A`. -/
@[simps pt]
def cone : Cone (P.F ⋙ coyoneda.rightOp) where
  pt := A
  π := P.π

/-- `P.cocone` is a colimit cocone. -/
def coneIsLimit : IsLimit P.cone :=
  P.isLimit

/-- If `A` and `B` are isomorphic, then an ind-object presentation of `A` can be extended to an
    ind-object presentation of `B`. -/
@[simps!]
noncomputable def extend {A B : (C ⥤ Type v)ᵒᵖ} (P : ProObjectPresentation A) (η : B ⟶ A)
    [IsIso η] : ProObjectPresentation B :=
  .ofCone (P.cone.extend η) (P.coneIsLimit.extendIso (by exact η))

/-- The canonical comparison functor between the indexing category of the presentation and the
    comma category `CostructuredArrow yoneda A`. This functor is always final. -/
@[simps! obj_left_as obj_right obj_hom map_left]
def toStructuredArrow : P.I ⥤ StructuredArrow A coyoneda.rightOp :=
  P.cone.toStructuredArrow ⋙ StructuredArrow.pre _ _ _

end ProObjectPresentation

end NonSmall

end CategoryTheory.Limits

end ProObject

universe v u

open CategoryTheory Limits Functor

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable (C) in
/-- The category of pro-objects of `C`. -/
def Pro : Type (max u (v + 1)) := (Ind Cᵒᵖ)ᵒᵖ

instance : Category.{v} (Pro C) :=
  inferInstanceAs (Category.{v} (Ind Cᵒᵖ)ᵒᵖ)

instance : HasCofilteredLimits (Pro C) := inferInstanceAs (HasCofilteredLimits (Ind Cᵒᵖ)ᵒᵖ)

variable (C) in
def Pro.inclusion : Pro C ⥤ (C ⥤ Type v)ᵒᵖ :=
  (Ind.inclusion (C := Cᵒᵖ)).op ⋙ (opOpEquivalence C).congrLeft.functor.op

instance : (Pro.inclusion C).Full := by
  sorry

instance : (Pro.inclusion C).Faithful :=
  sorry

protected def Pro.inclusion.fullyFaithful : (Ind.inclusion C).FullyFaithful :=
  sorry

def Pro.yoneda : C ⥤ Pro C := (Ind.yoneda (C := Cᵒᵖ)).rightOp

instance : (Pro.yoneda (C := C)).Full := sorry

instance : (Pro.yoneda (C := C)).Faithful := sorry

protected def Pro.yoneda.fullyFaithful : (Pro.yoneda (C := C)).FullyFaithful := sorry

/-- The composition `C ⥤ Ind C ⥤ (Cᵒᵖ ⥤ Type v)` is just the Yoneda embedding. -/
noncomputable def Pro.yonedaCompInclusion : Pro.yoneda ⋙ Pro.inclusion C ≅ coyoneda.rightOp :=
  sorry

universe v₁ u₁ in
def yonedaCoyonedaIso {I : Type u₁} [Category.{v₁} I] (F : I ⥤ Cᵒᵖ) :
    ((F ⋙ CategoryTheory.yoneda) ⋙ (whiskeringLeft C Cᵒᵖᵒᵖ (Type v)).obj (opOp C)).op ≅
    F.leftOp ⋙ coyoneda.rightOp := by
  refine NatIso.ofComponents (fun X ↦ (NatIso.ofComponents (fun Y ↦ ?_) ?_).op) ?_
  · exact Equiv.toIso {
      toFun f := f.op
      invFun f := f.unop
      left_inv := by intro; simp
      right_inv := by intro; simp }
  · aesop
  · aesop

def Pro.presentation (X : Pro C) : ProObjectPresentation ((Pro.inclusion C).obj X) where
  I := X.unop.presentation.Iᵒᵖ
  F := X.unop.presentation.F.leftOp
  π := NatTrans.op (whiskerRight (X.unop.presentation.ι.op).unop
      (opOpEquivalence C).congrLeft.functor) ≫ (yonedaCoyonedaIso X.unop.presentation.F).hom
  isLimit := (IsLimit.postcomposeHomEquiv _ _).symm <|
      isLimitOfPreserves ((opOpEquivalence C).congrLeft (E := Type v)).functor.op
      X.unop.presentation.isColimit.op

-- This should probably be proved in more generality by dualizing.
-- Let's leave it as `sorry` for now.
instance (X : Pro C) : (Pro.presentation X).toStructuredArrow.Initial := by
  let j := yonedaCoyonedaIso (opOpEquivalence C).inverse
  let e : StructuredArrow ((Pro.inclusion C).obj X) coyoneda.rightOp ≌
      StructuredArrow (Opposite.op ((Ind.inclusion Cᵒᵖ).obj (Opposite.unop X))) yoneda.op := by
    sorry
  have : (X.unop.presentation.toCostructuredArrow.op ⋙
    (costructuredArrowOpEquivalence _ _).functor ⋙ e.inverse).Initial := inferInstance
  let i : X.unop.presentation.toCostructuredArrow.op ⋙
      (costructuredArrowOpEquivalence _ _).functor ⋙ e.inverse ≅
        X.presentation.toStructuredArrow :=
    sorry
  exact Functor.initial_of_natIso i

def Pro.lim (I : Type v) [SmallCategory I] [IsCofiltered I] : (I ⥤ C) ⥤ Pro C :=
  (whiskeringRight _ _ _).obj Pro.yoneda ⋙ Limits.lim

-- universe w in
-- instance {α : Type w} [SmallCategory α] [FinCategory α] [HasLimitsOfShape α C] {I : Type v}
--     [SmallCategory I] [IsCofiltered I] :
--     PreservesLimitsOfShape α (Pro.lim I : (I ⥤ C) ⥤ _) :=
--   inferInstanceAs (PreservesLimitsOfShape α (_ ⋙ lim))

def Pro.limNatTrans {I J : Type v} [SmallCategory I] [IsCofiltered I] [SmallCategory J]
    [IsCofiltered J] (F : I ⥤ J) :
    Pro.lim (C := C) J ⟶ ((whiskeringLeft _ _ _).obj F) ⋙ Pro.lim (C := C) I where
  app G := limit.pre _ _
  naturality _ _ _ := by simpa [Pro.lim] using limit.map_pre _ _

def Pro.limMap {I J : Type v} [SmallCategory I] [IsCofiltered I] [SmallCategory J] [IsCofiltered J]
    (F : I ⥤ J) (G : J ⥤ C) : (Pro.lim J).obj G ⟶ (Pro.lim I).obj (F ⋙ G) :=
  limit.pre _ _

/-- A way to understand morphisms in `Pro C`: every morphism is induced by a natural transformation
of diagrams. -/
theorem Pro.exists_nonempty_arrow_mk_iso_pro_lim {A B : Pro C} {f : A ⟶ B} :
    ∃ (I : Type v) (_ : SmallCategory I) (_ : IsCofiltered I) (F G : I ⥤ C) (φ : F ⟶ G),
      Nonempty (Arrow.mk f ≅ Arrow.mk ((Pro.lim _).map φ)) := by
  obtain ⟨I, _, _, F, G, φ, ⟨g⟩⟩ := Ind.exists_nonempty_arrow_mk_iso_ind_lim (f := f.unop)
  refine ⟨Iᵒᵖ, inferInstance, inferInstance, G.leftOp, F.leftOp, φ.leftOp, ⟨?_⟩⟩
  sorry

section

universe v' u'

variable {C : Type u} [Category.{v} C]
variable {D : Type u'} [Category.{v'} D] [HasCofilteredLimitsOfSize.{v} D]

variable (C D) in
def Pro.precompYoneda :
  ObjectProperty.FullSubcategory (C := (Pro C ⥤ D))
    (fun G ↦ PreservesCofilteredLimitsOfSize.{v, v} G) ⥤ C ⥤ D :=
  ObjectProperty.ι _ ⋙ (whiskeringLeft _ _ _).obj Pro.yoneda

instance (X : Pro C) : IsCofiltered (StructuredArrow X Pro.yoneda) := by
  have : X.presentation.toStructuredArrow.Initial := inferInstance
  sorry

def Pro.ran : (C ⥤ D) ⥤ Pro C ⥤ D := Pro.yoneda.ran

def Pro.yonedaRanAdj : (whiskeringLeft _ _ _).obj Pro.yoneda ⊣ Pro.ran (C := C) (D := D) :=
  Pro.yoneda.ranAdjunction D

instance (F : C ⥤ D) : PreservesCofilteredLimitsOfSize.{v, v} (Pro.ran.obj F) := sorry

instance (F : C ⥤ D) : IsIso ((Pro.yonedaRanAdj (C := C) (D := D)).counit.app F) := by
  dsimp [Pro.yonedaRanAdj]
  infer_instance

instance : IsIso (Pro.yonedaRanAdj (C := C) (D := D)).counit := by
  apply NatIso.isIso_of_isIso_app

def Pro.ranFullyFaithful : (Pro.ran (C := C) (D := D)).FullyFaithful :=
  (Pro.yonedaRanAdj (C := C) (D := D)).fullyFaithfulROfIsIsoCounit

instance : (Pro.ran (C := C) (D := D)).Full := Pro.ranFullyFaithful.full

instance : (Pro.ran (C := C) (D := D)).Faithful := Pro.ranFullyFaithful.faithful

instance (X : Pro C) : HasLimitsOfShape (StructuredArrow X Pro.yoneda) (Pro C) := sorry

def Pro.isoLimit (X : Pro C) : X ≅ limit (StructuredArrow.proj X Pro.yoneda ⋙ Pro.yoneda) := by
  sorry

lemma foo : (Pro.ran (C := C) (D := D)).essImage =
    (fun G ↦ PreservesCofilteredLimitsOfSize.{v, v} G) := by
  ext F
  constructor
  · intro h
    obtain ⟨G, ⟨i⟩⟩ := h
    constructor
    intro J _ _
    exact preservesLimitsOfShape_of_natIso i
  · intro h
    refine ⟨Pro.yoneda ⋙ F, ⟨?_⟩⟩
    let i : Pro.ran.obj (Pro.yoneda ⋙ F) ≅
        pointwiseRightKanExtension Pro.yoneda (Pro.yoneda ⋙ F) :=
      sorry
    have (X : Pro C) : PreservesLimitsOfShape (StructuredArrow X Pro.yoneda) F := sorry
    refine i ≪≫ NatIso.ofComponents (fun X ↦
      lim.mapIso (Functor.associator _ _ _).symm ≪≫
        (preservesLimitIso F _).symm ≪≫ F.mapIso X.isoLimit.symm) ?_
    sorry

variable (C D) in
def Pro.universalProperty : ObjectProperty.FullSubcategory (C := (Pro C ⥤ D))
      (fun G ↦ PreservesCofilteredLimitsOfSize.{v, v} G) ≌ (C ⥤ D) :=
  Equivalence.trans (ObjectProperty.fullSubcategoryCongr (foo (C := C) (D := D))).symm
    (asEquivalence ((Pro.ran (C := C) (D := D)).toEssImage)).symm





















def Pro.ran' : (C ⥤ D) ⥤ ObjectProperty.FullSubcategory (C := (Pro C ⥤ D))
    (fun G ↦ PreservesCofilteredLimitsOfSize.{v, v} G) where
  obj F := ⟨Pro.ran.obj F, inferInstance⟩
  map f := Pro.ran.map f

variable (C D) in
def Pro.precompYonedaRanAdj : Pro.precompYoneda C D ⊣ Pro.ran' :=
  (Pro.yoneda.ranAdjunction D).restrictFullyFaithful (iC := ObjectProperty.ι _) (iD := 𝟭 _)
    (ObjectProperty.fullyFaithfulι _) (FullyFaithful.id _) (Iso.refl _) (Iso.refl _)

instance (F : C ⥤ D) : IsIso ((Pro.precompYonedaRanAdj C D).counit.app F) := by
  suffices IsIso ((𝟭 _).map ((Pro.precompYonedaRanAdj C D).counit.app F)) by simpa
  simp only [Pro.precompYonedaRanAdj, Adjunction.map_restrictFullyFaithful_counit_app]
  simp only [comp_obj, id_obj, ObjectProperty.ι_obj, whiskeringLeft_obj_obj, Iso.refl_inv,
    NatTrans.id_app, whiskeringLeft_obj_map, ranAdjunction_counit]
  erw [Category.id_comp, whiskerLeft_id, Category.id_comp]
  infer_instance

instance : IsIso (Pro.precompYonedaRanAdj C D).counit := by
  apply NatIso.isIso_of_isIso_app

def Pro.ran'FullyFaithful : (Pro.ran' (C := C) (D := D)).FullyFaithful :=
  (Pro.precompYonedaRanAdj C D).fullyFaithfulROfIsIsoCounit

-- instance : ((whiskeringLeft C (Pro C) D).obj Pro.yoneda).Full :=
--   sorry

-- instance : ((whiskeringLeft C (Pro C) D).obj Pro.yoneda).Faithful := sorry



instance (F : ObjectProperty.FullSubcategory (C := (Pro C ⥤ D))
    (fun G ↦ PreservesCofilteredLimitsOfSize.{v, v} G)) :
    IsIso ((Pro.precompYonedaRanAdj C D).unit.app F) := by
  simp only [id_obj, comp_obj, Pro.precompYonedaRanAdj, Adjunction.restrictFullyFaithful,
    ObjectProperty.ι_obj, whiskeringLeft_obj_obj, Iso.refl_symm, Equiv.trans_def,
    Adjunction.mkOfHomEquiv_unit_app, Equiv.trans_apply, Iso.homCongr_apply, Iso.app_inv,
    Iso.refl_inv, NatTrans.id_app, Iso.refl_hom, Category.comp_id, Category.id_comp, Iso.app_hom]
  sorry
  -- suffices IsIso ((ObjectProperty.ι _).map ((Pro.precompYonedaRanAdj C D).unit.app F)) from
  --   (ObjectProperty.fullyFaithfulι _).isIso_of_isIso_map _
  -- simp only [Pro.precompYonedaRanAdj, Adjunction.map_restrictFullyFaithful_unit_app,
  --   id_obj, ObjectProperty.ι_obj, comp_obj, whiskeringLeft_obj_obj, Iso.refl_hom,
  --   NatTrans.id_app, Functor.map_id, Category.comp_id]
  -- -- infer_instance
  -- rw [isIso_ranAdjunction_unit_app_iff]
  -- constructor
  -- constructor
  -- change IsTerminal _
  -- fapply IsTerminal.ofUniqueHom
  -- · sorry
  -- · sorry

variable (C D) in
def Pro.universalProperty'' : ObjectProperty.FullSubcategory (C := (Pro C ⥤ D))
      (fun G ↦ PreservesCofilteredLimitsOfSize.{v, v} G) ≌ (C ⥤ D) :=
  (Pro.precompYonedaRanAdj C D).toEquivalence

variable (C D) in
def Pro.universalProperty' : (C ⥤ D) ≌
    ObjectProperty.FullSubcategory (C := (Pro C ⥤ D))
      (fun G ↦ PreservesCofilteredLimitsOfSize.{v, v} G) where
  functor := sorry
  inverse := precompYoneda C D
  unitIso := sorry
  counitIso := sorry
  functor_unitIso_comp := sorry

def Pro.precompYonedaFullyFaithful : (Pro.precompYoneda C D).FullyFaithful where
  preimage {G H} f := sorry
  map_preimage := sorry
  preimage_map := sorry

instance : (Pro.precompYoneda C D).Full := by
  sorry

instance : (Pro.precompYoneda C D).Faithful := by
  sorry

instance : (Pro.precompYoneda C D).EssSurj := by
  sorry

instance : (Pro.precompYoneda C D).IsEquivalence where

instance (X : Pro FintypeCat.{u}) :
    HasLimitsOfShape (StructuredArrow X Pro.yoneda) Profinite.{u} :=
  hasLimitsOfShape_of_equivalence
    (asEquivalence (StructuredArrow.pre X FintypeCat.Skeleton.incl _))

instance (X : Pro C) (F : C ⥤ D) :
    (Pro.yoneda).HasPointwiseRightKanExtensionAt F X := by
  -- have : HasInitial (StructuredArrow X Pro.yoneda) := by sorry
  have : IsCofiltered (StructuredArrow X Pro.yoneda) := by
    apply (config := { allowSynthFailures := true }) Comma.isCofiltered_of_initial
    · sorry
    · sorry
  infer_instance

def Pro.functorExtend (F : C ⥤ D) : Pro C ⥤ D :=
  pointwiseRightKanExtension Pro.yoneda F

instance (F : C ⥤ D) :  (Pro.functorExtend F).IsRightKanExtension
    (Pro.yoneda.pointwiseRightKanExtensionCounit F) := by
  dsimp [Pro.functorExtend]
  infer_instance

def Pro.functorExtendCongr (F G : C ⥤ D) (i : F ≅ G) :
    Pro.functorExtend F ≅ Pro.functorExtend G :=
  rightKanExtensionUniqueOfIso _ (pointwiseRightKanExtensionCounit _ _) i _
    (pointwiseRightKanExtensionCounit _ _)

def Pro.yonedaCompExtend (F : C ⥤ D) : Pro.yoneda ⋙ functorExtend F ≅ F := by
  dsimp [functorExtend]
  sorry

def Pro.functorExtendUnique (F : C ⥤ D) (G : Pro C ⥤ D) [PreservesCofilteredLimits G]
    (i : Pro.yoneda ⋙ G ≅ F) : G ≅ functorExtend F :=
  sorry

instance (F : C ⥤ D) : PreservesCofilteredLimits (Pro.functorExtend F) := by
  sorry

def Pro.functorExt (F G : Pro C ⥤ D) [PreservesCofilteredLimits F]
    [PreservesCofilteredLimits G] (i : Pro.yoneda ⋙ F ≅ Pro.yoneda ⋙ G) : F ≅ G :=
  Pro.functorExtendUnique (Pro.yoneda ⋙ F) F (Iso.refl _) ≪≫
    Pro.functorExtendCongr _ _ i ≪≫
    (Pro.functorExtendUnique (Pro.yoneda ⋙ G) G (Iso.refl _)).symm

end

end CategoryTheory

namespace Profinite

@[simps]
def dqFunctor {S T : Profinite.{u}} (f : S ⟶ T) : DiscreteQuotient T ⥤ DiscreteQuotient S where
  obj i := i.comap f.hom
  map := fun ⟨⟨h⟩⟩ ↦ ⟨⟨by mono⟩⟩

@[simp]
lemma dqFunctor_id (S : Profinite.{u}) : dqFunctor (𝟙 S) = 𝟭 _ := rfl

@[simp]
lemma dqFunctor_comp (S T U : Profinite.{u}) (f : S ⟶ T) (g : T ⟶ U) :
    dqFunctor (f ≫ g) = dqFunctor g ⋙ dqFunctor f := rfl

@[simps]
def dqFunctorPrecompHom {S T : Profinite.{u}} (f : S ⟶ T) :
    dqFunctor f ⋙ S.fintypeDiagram ⟶ T.fintypeDiagram where
  app i := Quotient.map' f.hom (fun _ _ h ↦ h)
  naturality _ _ _ := by ext ⟨⟩; rfl

@[simp]
lemma dqFunctorPrecompHom_id (S : Profinite.{u}) : dqFunctorPrecompHom (𝟙 S) = 𝟙 _ := by
  ext ⟨⟩
  simp
  change Quotient.map' id _ _ = _
  sorry

@[simp]
lemma dqFunctorPrecompHom_comp {S T U : Profinite.{u}} (f : S ⟶ T) (g : T ⟶ U) :
    dqFunctorPrecompHom (f ≫ g) =
      whiskerLeft (dqFunctor g) (dqFunctorPrecompHom f) ≫ dqFunctorPrecompHom g  := by
  ext ⟨⟩
  simp
  sorry

def equivalence.functor : Profinite.{u} ⥤ Pro (FintypeCat.{u}) where
  -- this is a translation to the `Pro` API of what we did yesterday:
  obj S := (Pro.lim (DiscreteQuotient S)).obj S.fintypeDiagram
  map {S T} f := Pro.limMap (dqFunctor f) _ ≫ (Pro.lim _).map (dqFunctorPrecompHom f)
  map_id S := by
    simp [Pro.limMap]
    rw [limit.id_pre]
    exact Limits.lim.map_id _
  map_comp {S T U} f g := by
    simp [Pro.limMap, Pro.lim]
    change _ ≫ Limits.lim.map (_ ≫ _) = _ ≫ Limits.lim.map _ ≫ _
    rw [Limits.lim.map_comp, ← Category.assoc]
    simp only [← Category.assoc]
    rw [← limit.pre_pre]
    simp only [Category.assoc]
    congr 1
    simp only [← Category.assoc]
    rw [limit.map_pre]
    rfl

-- instance : equivalence.functor.Faithful where
--   map_injective {S T} f₁ f₂ := by
--     simp [equivalence.functor]
--     sorry

-- instance : equivalence.functor.Full := sorry

-- instance : equivalence.functor.EssSurj where
--   mem_essImage X := by
--     unfold Functor.essImage
--     use limit (X.presentation.F ⋙ FintypeCat.toProfinite)
--     sorry

-- instance : IsEquivalence equivalence.functor where

-- def equivalence' : Profinite.{u} ≌ Pro (FintypeCat.{u}) := asEquivalence (equivalence.functor)



def equivalence.inverse' : Pro (FintypeCat.{u}) ⥤ Profinite.{u} :=
  pointwiseRightKanExtension Pro.yoneda FintypeCat.toProfinite

instance : HasCofilteredLimitsOfSize.{u} Profinite.{u} :=
  sorry

def equivalence.inverse : Pro (FintypeCat.{u}) ⥤ Profinite.{u} :=
  Pro.functorExtend FintypeCat.toProfinite

instance : PreservesCofilteredLimits equivalence.inverse :=
  inferInstanceAs (PreservesCofilteredLimits (Pro.functorExtend _))

instance : PreservesCofilteredLimits equivalence.functor := by
  sorry

instance : PreservesFiniteLimits (Pro.yoneda (C := FintypeCat)) := sorry

def _root_.FintypeCat.asLimit (S : FintypeCat) :
    S ≅ limit (FintypeCat.toProfinite.obj S).fintypeDiagram :=
  sorry

instance (S : FintypeCat) :
    FinCategory (DiscreteQuotient (FintypeCat.toProfinite.obj S)) :=
  sorry

instance : HasCofilteredLimitsOfSize.{u} (Pro FintypeCat.{u}) :=
  sorry

def equivalence : Profinite.{u} ≌ Pro (FintypeCat.{u}) where
  functor := equivalence.functor
  inverse := equivalence.inverse
  unitIso := by
    refine NatIso.ofComponents (fun S ↦ ?_) ?_
    · refine ?_ ≪≫ (preservesLimitIso (Pro.functorExtend _) _).symm
      refine ?_ ≪≫ Limits.lim.mapIso
        (isoWhiskerLeft S.fintypeDiagram (Pro.yonedaCompExtend _).symm)
      exact S.isoAsLimitConeLift ≪≫ IsLimit.conePointUniqueUpToIso (limitConeIsLimit S.diagram)
        (limit.isLimit S.diagram)
    · sorry
  counitIso := by
    apply Pro.functorExt
    dsimp [equivalence.inverse]
    refine (Functor.associator _ _ _).symm ≪≫ ?_
    refine (isoWhiskerRight (Pro.yonedaCompExtend _) equivalence.functor) ≪≫ ?_
    refine NatIso.ofComponents (fun S ↦ ?_) ?_
    · refine (preservesLimitIso Pro.yoneda _).symm ≪≫ ?_
      exact (Pro.yoneda.mapIso S.asLimit).symm
    · sorry
  functor_unitIso_comp := sorry

end Profinite

#exit

namespace CategoryTheory














variable (C) in
structure ProObject where
  I : Type v
  smallCategory : SmallCategory I := by infer_instance
  isCofiltered : IsCofiltered I := by infer_instance
  diagram : I ⥤ C

attribute [instance] ProObject.smallCategory ProObject.isCofiltered

structure ProObjectHom (P Q : ProObject C) where
  hom (i : P.I) (j : Q.I) : P.diagram.obj i ⟶ Q.diagram.obj j
  transition₁ {i₁ i₂ : P.I} (j : Q.I) (f : i₁ ⟶ i₂) : sorry

def ProObjectHomFunctor (P Q : ProObject C) : P.Iᵒᵖ × Q.I ⥤ Type v :=
  P.diagram.op.prod Q.diagram ⋙ uncurry.obj coyoneda

instance : CategoryStruct.{v} (ProObject C) where
  Hom P Q := limit (curry.obj (ProObjectHomFunctor P Q) ⋙ colim)
  id P := by
    apply (Types.isLimitEquivSections (limit.isLimit _)).invFun
    simp [Functor.sections]
    sorry
  comp := sorry


end CategoryTheory
