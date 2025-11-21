import Mathlib.AdicSpace.TopologicalFunctor
import Mathlib.CategoryTheory.Sites.Canonical
import Mathlib.CategoryTheory.RepresentedBy

universe w' w v' u' v₃ u₃ v₂ u₂ v₁ u₁ v u

open CategoryTheory Limits Opposite

namespace CategoryTheory

namespace Functor

variable {C : Type u} [Category.{v} C]

section General

end General

variable {C : Type u} [Category.{v} C]

instance {F : Cᵒᵖ ⥤ Type w} [F.IsRepresentable] (X : Cᵒᵖ) : Small.{v} (F.obj X) :=
  (small_congr F.representableBy.homEquiv).mp inferInstance

end Functor

variable {C : Type u} [Category.{v} C]

  --homEquiv {Y} :=
  --  { toFun f := F.map f.op x
  --    invFun y := sorry
  --    left_inv := sorry
  --    right_inv := sorry }
  --homEquiv_comp := by simp

variable {C D E : Type*} [Category C] [Category D] [Category E] in
instance {J : Type*} [Category J]
    (F : J ⥤ C ⥤ D) (K : D ⥤ E) [HasLimitsOfShape J D]
    [∀ X, PreservesLimit (F ⋙ (evaluation C D).obj X) K] :
    PreservesLimit F ((Functor.whiskeringRight C D E).obj K) := by
  apply CategoryTheory.Limits.preservesLimit_of_evaluation
  intro X
  dsimp
  apply comp_preservesLimit


--noncomputable def foo
--    {J : Type*} [Category J] {F : J ⥤ Cᵒᵖ ⥤ Type w}
--    (c : Cone F)
--    (hc : IsLimit c) (X : J ⥤ C)
--    (d : Cone X) (hd : IsLimit d)
--    (hG : ∀ j, (F.obj j).RepresentableBy (X.obj j))
--    (H : ∀ {i j : J} (f : i ⟶ j),
--      (F.map f).app _ ((hG i).homEquiv (𝟙 <| X.obj i)) =
--        ((hG j).homEquiv (X.map f))) :
--    c.pt.RepresentableBy d.pt where
--  homEquiv {X} :=
--    { toFun f :=
--        let F' := F.flip.obj (op X)
--        let c' : Cone F' := sorry
--        _
--      invFun := _
--      left_inv := _
--      right_inv := _ }
--  homEquiv_comp := sorry

--noncomputable def foo (hc : IsLimit c) (X : J ⥤ C)
--    (d : Cone X) (hd : IsLimit d)
--    (hG : ∀ j, (F.obj j).RepresentableBy (X.obj j))
--    (H : ∀ {i j : J} (f : i ⟶ j),
--      (F.map f).app _ ((hG i).homEquiv (𝟙 <| X.obj i)) =
--        ((hG j).homEquiv (X.map f))) :
--    c.pt.RepresentableBy d.pt := by
--  refine (Functor.RepresentableBy.equivULiftYoneda _ _).symm ?_
--  symm
--  apply hc.conePointsIsoOfNatIso (isLimitOfPreserves uliftYoneda.{v, v, u} hd)
--  refine NatIso.ofComponents (fun j ↦ ?_) ?_
--  · exact ((Functor.RepresentableBy.equivULiftYoneda _ _) (hG j)).symm
--  · intro i j f
--    ext ⟨Z⟩ a
--    simp
--    ext
--    simp
--    sorry

variable (C) in
def isRepresentable : ObjectProperty (Cᵒᵖ ⥤ Type w) :=
  fun F ↦ F.IsRepresentable

lemma Functor.IsRepresentable.of_natIso {F G : Cᵒᵖ ⥤ Type w}
    (e : F ≅ G) [F.IsRepresentable] :
    G.IsRepresentable :=
  ⟨_, ⟨.ofIso F.representableBy e⟩⟩

/-- `uliftYoneda.obj X` is represented by `X`. -/
def Functor.RepresentableBy.uliftYoneda (X : C) :
    (uliftYoneda.obj X).RepresentableBy X where
  homEquiv {Y} := Equiv.ulift.symm
  homEquiv_comp := by cat_disch

instance (X : C) : (uliftYoneda.obj X).IsRepresentable where
  has_representation := ⟨X, ⟨.uliftYoneda X⟩⟩

variable (C) in
lemma essImage_yoneda : yoneda.essImage = isRepresentable C := by
  ext F
  exact ⟨fun ⟨X, ⟨e⟩⟩ ↦ .of_natIso e,
    fun ⟨X, ⟨e⟩⟩ ↦ ⟨X, ⟨Functor.representableByEquiv e⟩⟩⟩

variable (C) in
lemma essImage_uliftYoneda :
    (uliftYoneda.{w} (C := C)).essImage = isRepresentable.{max w v} C := by
  ext F
  exact ⟨fun ⟨X, ⟨e⟩⟩ ↦ .of_natIso e,
    fun ⟨X, ⟨e⟩⟩ ↦ ⟨X, ⟨(Functor.RepresentableBy.equivUliftYoneda _ _) e⟩⟩⟩

variable (C) in
@[simps! -isSimp]
noncomputable
def yonedaEquivIsRepresentable :
    C ≌ (isRepresentable.{max w v} C).FullSubcategory :=
  (uliftYoneda.{w}).toEssImage.asEquivalence.trans
    (ObjectProperty.fullSubcategoryCongr <| essImage_uliftYoneda C)

variable (C) in
def yonedaEquivIsRepresentableCompUliftYonedaIso :
    (yonedaEquivIsRepresentable C).inverse ⋙ uliftYoneda.{w} ≅ ObjectProperty.ι _ :=
  sorry

/-- Superseded by `Functor.RepresentableBy.ofIsLimit`. -/
private lemma Functor.RepresentableBy.ofIsLimitAux' {J : Type*} [Category J]
    {F : J ⥤ Cᵒᵖ ⥤ Type (max v w)} {c : Cone F}
    [HasLimitsOfShape J C] (hc : IsLimit c) (h : ∀ j, (F.obj j).IsRepresentable) :
    c.pt.IsRepresentable := by
  have : HasLimitsOfShape J (CategoryTheory.isRepresentable.{max w v} C).FullSubcategory :=
    hasLimitsOfShape_of_hasLimitsOfShape_createsLimitsOfShape
    (yonedaEquivIsRepresentable.{w} C).inverse
  let F' : J ⥤ (CategoryTheory.isRepresentable.{max w v} C).FullSubcategory :=
    ObjectProperty.lift _ F h
  let F'' : J ⥤ C := F' ⋙ (yonedaEquivIsRepresentable C).inverse
  refine ⟨limit F'', ⟨?_⟩⟩
  let e : F'' ⋙ CategoryTheory.uliftYoneda.{w} ≅ F :=
    (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft _
      (yonedaEquivIsRepresentableCompUliftYonedaIso C)
  exact (Functor.RepresentableBy.equivUliftYoneda _ _).symm <|
    (preservesLimitIso CategoryTheory.uliftYoneda.{w, v, u} F'') ≪≫
      (limit.isLimit _).conePointsIsoOfNatIso hc e

/-- Superseded by `Functor.RepresentableBy.ofIsLimit`. -/
private lemma Functor.RepresentableBy.ofIsLimitAux {J : Type*} [Category J]
    {F : J ⥤ Cᵒᵖ ⥤ Type (max v w)} {c : Cone F}
    [HasLimitsOfShape J C] (hc : IsLimit c) (h : ∀ j, (F.obj j).IsRepresentable) :
    c.pt.IsRepresentable := by
  let F' : J ⥤ (CategoryTheory.isRepresentable.{max w v} C).FullSubcategory :=
    ObjectProperty.lift _ F h
  let F'' : J ⥤ C := F' ⋙ (yonedaEquivIsRepresentable C).inverse
  refine ⟨limit F'', ⟨?_⟩⟩
  let e : F'' ⋙ CategoryTheory.uliftYoneda.{w} ≅ F :=
    (Functor.associator _ _ _) ≪≫ Functor.isoWhiskerLeft _
      (yonedaEquivIsRepresentableCompUliftYonedaIso C)
  exact (Functor.RepresentableBy.equivUliftYoneda _ _).symm <|
    (preservesLimitIso CategoryTheory.uliftYoneda.{w, v, u} F'') ≪≫
      (limit.isLimit _).conePointsIsoOfNatIso hc e

/-- The limit of representable functors is representable if `C` has limits. -/
lemma Functor.IsRepresentable.of_isLimit {J : Type*} [Category J]
    (F : J ⥤ Cᵒᵖ ⥤ Type w) (c : Cone F) [HasLimitsOfShape J C] (hc : IsLimit c)
    [∀ j, (F.obj j).IsRepresentable] : c.pt.IsRepresentable := by
  rw [← Functor.isRepresentable_comp_uliftFunctor_iff.{v}]
  let c' := ((whiskeringRight _ _ _).obj uliftFunctor.{v}).mapCone c
  let hc' : IsLimit c' :=
    sorry
  refine Functor.RepresentableBy.ofIsLimitAux hc' fun j ↦ ?_
  dsimp only [comp_obj, whiskeringRight_obj_obj]
  rw [Functor.isRepresentable_comp_uliftFunctor_iff]
  infer_instance

end CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] (J : Precoverage C)
variable [J.IsStableUnderComposition] [J.IsStableUnderBaseChange]
  [J.HasIsos] [J.HasPullbacks]

lemma Precoverage.isSheaf_iff {F : Cᵒᵖ ⥤ Type*} :
    Presheaf.IsSheaf J.toGrothendieck F ↔
      ∀ {X : C} (𝒰 : Precoverage.ZeroHypercover.{max u v} J X),
      Presieve.IsSheafFor F 𝒰.presieve₀ :=
  sorry

lemma Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition
    {X : C} {R : Sieve X} :
    R ∈ J.toGrothendieck X ↔
      ∃ (𝒰 : Precoverage.ZeroHypercover.{max u v} J X), 𝒰.presieve₀ ≤ R.arrows :=
  sorry

lemma Precoverage.generate_mem_toGrothendieck {X : C} {R : Presieve X}
    (hR : R ∈ J X) :
    Sieve.generate R ∈ J.toGrothendieck X := by
  rw [Precoverage.toGrothendieck, Coverage.mem_toGrothendieck]
  exact .of _ _ hR

variable {A : Type u'} [Category.{v'} A] {FA : A → A → Type*} {CA : A → Type w'}
variable [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory.{w'} A FA]

lemma Precoverage.isLocallySurjective_iff {F G : Cᵒᵖ ⥤ A} (f : F ⟶ G) :
    Presheaf.IsLocallySurjective J.toGrothendieck f ↔
      ∀ {X : C} (x : ToType (G.obj (op X))),
        ∃ (E : ZeroHypercover.{max u v} J X), ∀ i : E.I₀,
          ∃ y : ToType (F.obj (op (E.X i))),
            f.app (op <| E.X i) y = G.map (E.f i).op x := by
  refine ⟨fun h X x ↦ ?_, ?_⟩
  · have := Presheaf.imageSieve_mem J.toGrothendieck f x
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at this
    obtain ⟨𝒰, h⟩ := this
    use 𝒰
    intro i
    have hh : (Presheaf.imageSieve f x).arrows (𝒰.f i) :=
      h _ (Presieve.ofArrows.mk i)
    rw [Presheaf.imageSieve_apply] at hh
    exact hh
  · intro h
    constructor
    intro X x
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition]
    obtain ⟨𝒰, h⟩ := h x
    use 𝒰
    rintro - - ⟨i⟩
    change (Presheaf.imageSieve f x).arrows (𝒰.f i)
    rw [Presheaf.imageSieve_apply]
    exact h i

namespace Limits

@[simps!]
def functorCofan {I : Type w} (F : I → C ⥤ Type w) :
    Cofan F := by
  refine Cofan.mk ?_ ?_
  · refine
      { obj X := Σ i : I, (F i).obj X
        map {X Y} f := _root_.Sigma.map id (fun i ↦ (F i).map f) }
  · intro i
    exact ⟨fun X x ↦ ⟨_, x⟩, by cat_disch⟩

def isColimitFunctorCofan {I : Type w} (F : I → C ⥤ Type w) :
    IsColimit (functorCofan F) := by
  refine mkCofanColimit _ ?_ ?_ ?_
  · intro t
    refine ⟨fun X x ↦ (t.inj x.1).app _ x.2, ?_⟩
    intros
    simp
    ext
    simp
    apply FunctorToTypes.naturality
  · cat_disch
  · intro t m hm
    ext X i
    have := hm i.1
    simp at this
    simp
    rw [← this]
    simp
    rfl

end Limits

end CategoryTheory


-- Think `D` is adic spaces over `Spa k`, `C` is schemes over `Spec k` and
-- `B` is locally ringed spaces over `Spec k`
variable {C : Type v₃} {D : Type v₃} {B : Type v₃}
  [Category.{v₃} C] [Category.{v₃} D] [Category.{v₃} B]
variable (L : C ⥤ B) (R : D ⥤ B)

namespace CategoryTheory.Analytification

@[simps! obj map]
def universalProperty : C ⥤ Dᵒᵖ ⥤ Type v₃ :=
  L ⋙ yoneda ⋙ (Functor.whiskeringLeft _ _ _).obj R.op

abbrev HasAnalytification (X : C) : Prop :=
  (universalProperty L R |>.obj X).IsRepresentable

abbrev IsAnalytification {X : C} {Y : D} (f : R.obj Y ⟶ L.obj X) : Prop :=
  (universalProperty L R |>.obj X).IsRepresentedBy f

lemma hasAnalytification_iff_exists_isAnalytification {X : C} :
    HasAnalytification L R X ↔
      ∃ (Y : D) (f : R.obj Y ⟶ L.obj X), IsAnalytification L R f :=
  Functor.IsRepresentable.iff_exists_isRepresentedBy

--def equivRepresentableBy (X : C) (Y : D) :
--    (universalProperty L R |>.obj X).RepresentableBy Y ≃ _ :=
--  sorry

lemma isLimit_iff_isAnalytification_id_overMap
    {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) (c : PullbackCone f g) :
    Nonempty (IsLimit c) ↔
      IsAnalytification (𝟭 _) (Over.map g) (X := Over.mk f) (Y := Over.mk c.snd)
        (Over.homMk c.fst c.condition) := by
  refine ⟨fun ⟨hc⟩ ↦ ?_, fun h ↦ ⟨⟨?_, ?_, ?_⟩⟩⟩
  · rw [IsAnalytification, Functor.isRepresentedBy_iff]
    intro W
    refine ⟨?_, ?_⟩
    · intro u v huv
      dsimp at huv
      ext
      apply PullbackCone.IsLimit.hom_ext hc
      · exact congr($(huv).left)
      · exact (Over.w u).trans (Over.w v).symm
    · intro u
      dsimp at u
      refine ⟨Over.homMk ?_ ?_, ?_⟩
      · exact PullbackCone.IsLimit.lift hc u.left W.hom (Over.w u)
      · simp
      · cat_disch
  · sorry
  · sorry
  · sorry

lemma hasPullback_iff_hasAnalytification {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasPullback f g ↔ HasAnalytification (𝟭 _) (Over.map g) (Over.mk f) := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · refine ⟨Over.mk (pullback.snd f g), ⟨⟨?_, ?_⟩⟩⟩
    · intro W
      dsimp
      sorry
    · sorry
  · sorry

abbrev HasRelativePullback {U X : C} {Y : D} (f : U ⟶ X) (g : R.obj Y ⟶ L.obj X) : Prop :=
  HasAnalytification (Over.post L) (Over.post R ⋙ Over.map g) (Over.mk f)

noncomputable
def analytification [∀ X, HasAnalytification L R X] : C ⥤ D where
  obj X := (universalProperty L R |>.obj X).reprX
  map {X Y} f :=
    (universalProperty L R |>.obj Y).reprW.inv.app (op <| ((universalProperty L R).obj X).reprX) <|
      ((universalProperty L R).map f).app
      (op ((universalProperty L R).obj X).reprX) ((universalProperty L R).obj X).reprx
  map_id X := sorry
  map_comp := sorry

variable [Topological C] [Topological D] [Topological B] [L.Topological] [R.Topological]

open Topological

lemma isOpenImmersion_relativeYonedaPreComp {U X : C} (f : U ⟶ X) [IsOpenImmersion f] :
    (isOpenImmersion D).presheaf ((universalProperty L R).map f) := by
  refine MorphismProperty.relative.of_exists ?_
  intro Z g
  let g' : R.obj Z ⟶ L.obj X := g.app _ (𝟙 Z)
  have heq {S : D} (a : S ⟶ Z) (W : Dᵒᵖ) (h : Opposite.unop W ⟶ S) :
      g.app W (h ≫ a) = R.map h ≫ R.map a ≫ g.app (Opposite.op Z) (𝟙 Z) := by
    have := g.naturality
    dsimp [universalProperty] at this
    -- simp_rw [funext_iff] at this
    specialize this (h ≫ a).op
    rw [funext_iff] at this
    specialize this (𝟙 _)
    simp at this
    exact this
  refine ⟨Functor.relativePullback f g', ?_, Functor.relativePullback.snd _ _, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro W (h : W.unop ⟶ Functor.relativePullback f g')
      exact R.map h ≫ Functor.relativePullback.fst _ _
    · cat_disch
  · refine ⟨⟨⟨?_⟩, ?_⟩, ?_⟩
    · ext W h
      simp [Functor.relativePullback.condition, heq, g']
    · refine ⟨Limits.PullbackCone.IsLimit.mk _ (fun s ↦ ?_) ?_ ?_ ?_⟩
      · refine ⟨fun W x ↦ ?_, ?_⟩
        · refine Functor.relativePullback.lift ?_ ?_ ?_
          · exact s.snd.app W x
          · exact s.fst.app W x
          · simp only [universalProperty_obj, universalProperty_map, g']
            have := congr($(s.condition).app W x)
            dsimp at this
            rw [this]
            have heq' := heq (𝟙 Z)
            simp only [universalProperty_obj, Functor.comp_obj, Functor.op_obj, yoneda_obj_obj,
              Category.comp_id, Functor.map_id, Category.id_comp] at heq'
            rw [← heq']
        · intro W T u
          ext x
          simp
          apply Functor.relativePullback.hom_ext
          · simpa using congr($(s.fst.naturality u) x)
          · simpa using congr($(s.snd.naturality u) x)
      · intro; ext; simp
      · intro; ext; simp
      · intro s m hm heq
        ext
        apply Functor.relativePullback.hom_ext
        · simp [← hm]
        · simp [← heq]
    · infer_instance

open Limits

attribute [local instance] Types.instFunLike Types.instConcreteCategory


variable (C) in
class RepresentabilityIsLocal : Prop where
  isRepresentable_sheaf (G : Cᵒᵖ ⥤ Type v₃)
    (hG : Presheaf.IsSheaf (zariskiTopology C) G)
    {ι : Type v₃} {X : ι → C} {f : ∀ i, yoneda.obj (X i) ⟶ G}
    (hf : ∀ i, (isOpenImmersion C).presheaf (f i))
    [Presheaf.IsLocallySurjective (zariskiTopology C)
      (CategoryTheory.Limits.Sigma.desc f)] :
    G.IsRepresentable

lemma RepresentabilityIsLocal.isRepresentable_sheaf'
    (G : Cᵒᵖ ⥤ Type v₃) (hG : Presheaf.IsSheaf (zariskiTopology C) G)
    {ι : Type v₃} {H : ι → Cᵒᵖ ⥤ Type v₃} {f : ∀ i, H i ⟶ G}
    (hf : ∀ i, (isOpenImmersion C).presheaf (f i))
    [Presheaf.IsLocallySurjective (zariskiTopology C)
      (CategoryTheory.Limits.Sigma.desc f)]
    [∀ i, (H i).IsRepresentable] : G.IsRepresentable :=
  sorry

lemma RepresentabilityIsLocal.isRepresentable_sheaf''
    (G : Cᵒᵖ ⥤ Type v₃) (hG : Presheaf.IsSheaf (zariskiTopology C) G)
    {ι : Type v₃} {H : ι → Cᵒᵖ ⥤ Type v₃} {f : ∀ i, H i ⟶ G}
    (hf : ∀ i, (isOpenImmersion C).presheaf (f i))
    [Presheaf.IsLocallySurjective (zariskiTopology C)
      (Cofan.IsColimit.desc (Limits.isColimitFunctorCofan _) f)]
    [∀ i, (H i).IsRepresentable] : G.IsRepresentable :=
  sorry

open Functor

instance : R.PreservesOneHypercovers (zariskiTopology _) (zariskiTopology _) := by
  intro X 𝒰
  refine ⟨?_, ?_⟩
  · apply Precoverage.generate_mem_toGrothendieck
    refine ⟨?_, ?_⟩
    · simp only [PreOneHypercover.map_I₀, Precoverage.mem_comap_iff, Presieve.map_ofArrows,
        PreOneHypercover.map_X, PreOneHypercover.map_f,
        Types.ofArrows_mem_jointlySurjectivePrecoverage_iff, Set.mem_range]
      intro x
      sorry
    · simp only [PreOneHypercover.map_I₀,
        MorphismProperty.ofArrows_mem_precoverage,
        PreOneHypercover.map_X, PreOneHypercover.map_f]
      intro i
      infer_instance
  · sorry

instance : (zariskiTopology C).IsGeneratedByOneHypercovers := by
  constructor
  intro X S hS
  sorry

lemma isSheaf_universalProperty [(zariskiTopology B).Subcanonical] (X : C) :
    Presheaf.IsSheaf (zariskiTopology D) ((universalProperty L R).obj X) := by
  dsimp
  change Presheaf.IsSheaf _ (_ ⋙ ((zariskiTopology B).yoneda.obj _).val)
  rw [isSheaf_iff_isSheaf_of_type]
  apply IsContinuous.op_comp_isSheaf_of_types

lemma HasAnalytification.of_iso {X Y : C} (e : X ≅ Y)
    [HasAnalytification L R X] :
    HasAnalytification L R Y :=
  IsRepresentable.of_natIso <| (universalProperty L R).mapIso e

lemma HasAnalytification.of_isLimit {J : Type*} [Small.{v₃} J] [Category J]
    [HasLimitsOfShape J D] [PreservesLimitsOfShape J L]
    (X : J ⥤ C) (c : Cone X) (hc : IsLimit c)
    [∀ j, HasAnalytification L R (X.obj j)] :
    HasAnalytification L R c.pt := by
  let F : J ⥤ Dᵒᵖ ⥤ Type _ := X ⋙ universalProperty L R
  let d : Cone F := (universalProperty L R).mapCone c
  have : PreservesLimitsOfShape J (universalProperty L R) := by
    dsimp [universalProperty]
    infer_instance
  let hd : IsLimit d :=
    isLimitOfPreserves _ hc
  have (j : J) : (F.obj j).IsRepresentable := by
    dsimp only [F, comp_obj]
    infer_instance
  apply IsRepresentable.of_isLimit _ d hd

theorem of_exists_locally [(zariskiTopology B).Subcanonical]
    [RepresentabilityIsLocal D]
    {X : C} (𝒰 : Precoverage.ZeroHypercover.{v₃} (zariskiPrecoverage C) X)
    [h : ∀ i, HasAnalytification L R (𝒰.X i)] :
    HasAnalytification L R X := by
  let f (i : 𝒰.I₀) :
      (universalProperty L R).obj (𝒰.X i) ⟶ (universalProperty L R).obj X :=
    Functor.whiskerLeft _ (yoneda.map <| (L.map (𝒰.f i)))
  have : Presheaf.IsLocallySurjective (zariskiTopology D)
      (Cofan.IsColimit.desc (Limits.isColimitFunctorCofan _) f) := by
    rw [zariskiTopology, Precoverage.isLocallySurjective_iff]
    intro Y (g : R.obj Y ⟶ L.obj X)
    use 𝒰.relativePullback g
    intro i
    dsimp
    refine ⟨⟨i, ?_⟩, ?_⟩
    · exact Functor.relativePullback.fst _ _
    · apply relativePullback.condition
  apply RepresentabilityIsLocal.isRepresentable_sheaf'' (f := f)
  · apply isSheaf_universalProperty
  · intro i
    apply isOpenImmersion_relativeYonedaPreComp

end CategoryTheory.Analytification
