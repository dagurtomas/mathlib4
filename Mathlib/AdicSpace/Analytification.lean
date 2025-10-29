import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.MorphismProperty.Representable

/-!

-/

universe v u

open AlgebraicGeometry CategoryTheory Limits

namespace Try1

variable {C : Type*} [Category C] (F : C ⥤ LocallyRingedSpace.{u})
  (J : GrothendieckTopology C)

-- Think `B = Spec k` and `S = Spa(k)`, `f : Spa k ⟶ Spec k`
variable (B : Scheme.{u}) (S : C) (f : F.obj S ⟶ B.toLocallyRingedSpace)

-- `Z ↦ Hom_B(Z, X)`
def foo (X : Scheme) (s : X ⟶ B) : (Over S)ᵒᵖ ⥤ Type _ :=
  (Over.post F ⋙ Over.map f).op ⋙ yoneda.obj (.mk <| s.toLRSHom)

-- think Z = Xᵃⁿ
class IsAnalytification {X : Scheme} (s : X ⟶ B) {Z : C}
    (φ : F.obj Z ⟶ X.toLocallyRingedSpace) (sZ : Z ⟶ S) : Prop where
  exists_unique {R : C} (g : F.obj R ⟶ X.toLocallyRingedSpace) (h : R ⟶ S) :
    g ≫ s.toLRSHom = F.map h ≫ f → ∃! (u : R ⟶ Z), F.map u ≫ φ = g ∧ u ≫ sZ = h

-- add assumptions
theorem of_exists_locally : True := sorry

end Try1

namespace Try2

-- think: `C` is the category of adic spaces over some base `S`
-- (that is `S` is thought of the existing analytification of `B`)
-- for example `B = Spec k` and `S = Spa k`.
variable {B : Scheme.{u}} {C : Type*} [Category C]
    (F : C ⥤ Over B.toLocallyRingedSpace) (J : GrothendieckTopology C)

-- `Z ↦ Hom_B(Z, X)`
def relativeYoneda {X : Scheme} (s : X ⟶ B) : Cᵒᵖ ⥤ Type _ :=
  F.op ⋙ yoneda.obj (.mk <| s.toLRSHom)

def relativeYonedaPreComp {X Y : Scheme} (f : X ⟶ Y) (s : Y ⟶ B) :
    relativeYoneda F (f ≫ s) ⟶ relativeYoneda F s :=
  Functor.whiskerLeft _ (yoneda.map <| Over.homMk f.toLRSHom)

-- think Z = Xᵃⁿ
class IsAnalytification {X : Scheme} (s : X ⟶ B) {Z : C}
    (φ : F.obj Z ⟶ Over.mk s.toLRSHom) : Prop where
  exists_unique {R : C} (g : F.obj R ⟶ Over.mk s.toLRSHom) :
    ∃! (u : R ⟶ Z), F.map u ≫ φ = g

class HasAnalytification {X : Scheme.{u}} (s : X ⟶ B) : Prop where
  exists_isAnalytification (s) : ∃ (Z : C) (φ : F.obj Z ⟶ Over.mk s.toLRSHom),
    IsAnalytification F s φ

variable {X : Scheme} (s : X ⟶ B)

noncomputable def analytification {X : Scheme} (s : X ⟶ B) [HasAnalytification F s] : C :=
  (HasAnalytification.exists_isAnalytification (F := F) s).choose

noncomputable def fromAnalytification {X : Scheme} (s : X ⟶ B) [HasAnalytification F s] :
    F.obj (analytification F s) ⟶ Over.mk s.toLRSHom :=
  (HasAnalytification.exists_isAnalytification (F := F) s).choose_spec.choose

instance isAnalytification_fromAnalytification {X : Scheme} (s : X ⟶ B)
    [HasAnalytification F s] :
    IsAnalytification F s (fromAnalytification F s) :=
  (HasAnalytification.exists_isAnalytification (F := F) s).choose_spec.choose_spec

lemma hasAnalytification_iff_isRepresentable :
    HasAnalytification F s ↔ (relativeYoneda F s).IsRepresentable := by
  refine ⟨?_, ?_⟩
  · intro h
    obtain ⟨Z, φ, h⟩ := h.exists_isAnalytification
    refine ⟨Z, ⟨⟨?_, ?_⟩⟩⟩
    · sorry
    · sorry
  · sorry

end Try2

variable {C : Type u} [Category.{v} C]

open TopologicalSpace

def TopologicalSpace.Opens.subyoneda
    (F : C ⥤ TopCat) (X : C) (U : Opens (F.obj X)) :
    Cᵒᵖ ⥤ Type _ where
  obj Y := { g : Y.unop ⟶ X | Set.range (F.map g) ⊆ U }
  map := sorry

class _root_.CategoryTheory.Functor.Geometric {C : Type*} [Category C]
    (F : C ⥤ LocallyRingedSpace.{u}) : Prop where
  isRepresentable (X : C) (U : Opens (F.obj X)) :
    (U.subyoneda (F ⋙ LocallyRingedSpace.forgetToTop)).IsRepresentable

variable (F : C ⥤ LocallyRingedSpace.{v}) [F.Geometric]

namespace CategoryTheory.Functor.Geometric

attribute [instance] Geometric.isRepresentable

noncomputable def opens (X : C) : Opens (F.obj X) ⥤ Over X where
  obj U := .mk (U.subyoneda (F ⋙ LocallyRingedSpace.forgetToTop)).reprx.1
  map := sorry

def IsOpenImmersion {U X : C} (f : U ⟶ X) : Prop :=
  (opens F X).essImage (Over.mk f)

def isOpenImmersion : MorphismProperty C :=
  fun _ _ f ↦ IsOpenImmersion F f

abbrev LocallyRingedSpace.forget : LocallyRingedSpace.{u} ⥤ Type u :=
  LocallyRingedSpace.forgetToTop ⋙ CategoryTheory.forget TopCat

protected abbrev forget : C ⥤ Type v := F ⋙ LocallyRingedSpace.forget

def zariskiPrecoverage : Precoverage C :=
  Types.jointlySurjectivePrecoverage.comap (Geometric.forget F) ⊓
    (isOpenImmersion F).precoverage

instance : (zariskiPrecoverage F).IsStableUnderComposition :=
  sorry

instance : (zariskiPrecoverage F).IsStableUnderBaseChange :=
  sorry

instance : (zariskiPrecoverage F).HasIsos :=
  sorry

instance : (zariskiPrecoverage F).HasPullbacks :=
  sorry

def zariskiTopology : GrothendieckTopology C :=
  (zariskiPrecoverage F).toGrothendieck

attribute [local instance] Types.instFunLike Types.instConcreteCategory

class RepresentabilityIsLocal : Prop where
  isRepresentable_sheaf (G : Cᵒᵖ ⥤ Type v) (hG : Presheaf.IsSheaf (zariskiTopology F) G)
    {ι : Type v} {X : ι → C} {f : ∀ i, yoneda.obj (X i) ⟶ G}
    (hf : ∀ i, (isOpenImmersion F).presheaf (f i))
    [Presheaf.IsLocallySurjective (zariskiTopology F)
      (CategoryTheory.Limits.Sigma.desc f)] :
    G.IsRepresentable

lemma RepresentabilityIsLocal.isRepresentable_sheaf'
    (G : Cᵒᵖ ⥤ Type v) (hG : Presheaf.IsSheaf (zariskiTopology F) G)
    {ι : Type v} {H : ι → Cᵒᵖ ⥤ Type v} {f : ∀ i, H i ⟶ G}
    (hf : ∀ i, (isOpenImmersion F).presheaf (f i))
    [Presheaf.IsLocallySurjective (zariskiTopology F)
      (CategoryTheory.Limits.Sigma.desc f)]
    [∀ i, (H i).IsRepresentable] : IsRepresentable G :=
  sorry

open Try2

variable {C : Type (u + 1)} [Category.{u} C]
variable {B : Scheme.{u}} (F : C ⥤ Over B.toLocallyRingedSpace)
  [Geometric (F ⋙ Over.forget _)]

theorem foo {C : Type (u + 1)}
  [inst : Category.{u, u + 1} C] {B : Scheme} (F : C ⥤ Over B.toLocallyRingedSpace)
  [inst_1 : (F ⋙ Over.forget B.toLocallyRingedSpace).Geometric]
  {U X : Scheme} (f : U ⟶ X) (s : X ⟶ B)
  [inst_2 : AlgebraicGeometry.IsOpenImmersion f] :
  let F' := F ⋙ Over.forget B.toLocallyRingedSpace;
  ∀ ⦃Z : C⦄ (g : yoneda.obj Z ⟶ relativeYoneda F s),
    let g' := (g.app (Opposite.op Z) (𝟙 Z)).left;
    let V := (opens F' Z).obj ((Opens.map g'.base).obj (Scheme.Hom.opensRange f));
    Set.range ⇑(ConcreteCategory.hom (F'.map V.hom ≫ g').base) ⊆
      Set.range ⇑(ConcreteCategory.hom (Scheme.Hom.toLRSHom f).base) := sorry

lemma isOpenImmersion_relativeYonedaPreComp {U X : Scheme} (f : U ⟶ X) (s : X ⟶ B)
    [AlgebraicGeometry.IsOpenImmersion f] :
    (isOpenImmersion <| F ⋙ Over.forget B.toLocallyRingedSpace).presheaf
      (relativeYonedaPreComp F f s) := by
  let F' := F ⋙ Over.forget B.toLocallyRingedSpace
  refine ⟨?_, ?_⟩
  · intro Z g
    let g' : (F.obj Z).left ⟶ X.toLocallyRingedSpace := (g.app _ (𝟙 Z)).1
    let V : Over Z := (Functor.Geometric.opens F' Z).obj <|
      (Opens.map g'.base).obj <| f.opensRange
    have heq (W : Cᵒᵖ) (h : Opposite.unop W ⟶ V.left) :
        g.app W (h ≫ V.hom) = F.map h ≫ F.map V.hom ≫ g.app (Opposite.op Z) (𝟙 Z) := by
      have := g.naturality
      dsimp [relativeYoneda] at this
      -- simp_rw [funext_iff] at this
      specialize this (h ≫ V.hom).op
      rw [funext_iff] at this
      specialize this (𝟙 _)
      simp only [Opposite.op_unop, const_obj_obj, op_comp, map_comp, yoneda_obj_obj,
        types_comp_apply, yoneda_obj_map, Quiver.Hom.unop_op, Category.comp_id, unop_comp] at this
      exact this
    use V.left, V.hom
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro W h
      dsimp at h
      let u : F'.obj V.left ⟶ U.toLocallyRingedSpace := by
        refine LocallyRingedSpace.IsOpenImmersion.lift f.toLRSHom ?_ ?_
        · exact F'.map V.hom ≫ g'
        · apply foo
      refine Over.homMk (F'.map h ≫ u) ?_
      simp only [op_obj, const_obj_obj, Over.mk_left, comp_obj, Over.forget_obj, comp_map,
        Over.forget_map, Over.mk_hom, Category.assoc, F', u]
      rw [← Over.w (F.map h)]
      have := Over.w (F.map V.hom)
      dsimp at this
      rw [← this]
      change _ ≫ _ ≫ (f.toLRSHom ≫ s.toLRSHom) = _
      rw [LocallyRingedSpace.IsOpenImmersion.lift_fac_assoc]
      simp [g']
      simp_rw [← Over.comp_left_assoc]
      rw [← heq]
      simp only [Over.mk_left]
      apply Over.w
    · cat_disch
    · dsimp
      refine ⟨?_, ?_⟩
      · constructor
        ext W a
        simp [relativeYonedaPreComp]
        apply Comma.hom_ext
        · simp [F', g', heq]
        · simp
      · constructor
        sorry
  · sorry

-- add assumptions
theorem of_exists_locally [Geometric (F ⋙ Over.forget _)]
    [RepresentabilityIsLocal (F ⋙ Over.forget _)]
    {X : Scheme} (s : X ⟶ B) (𝒰 : Scheme.OpenCover.{u} X)
    [h : ∀ i, HasAnalytification F (𝒰.f i ≫ s)] :
    HasAnalytification F s := by
  simp_rw [hasAnalytification_iff_isRepresentable] at h ⊢
  let f (i : 𝒰.I₀) : relativeYoneda F (𝒰.f i ≫ s) ⟶ relativeYoneda F s :=
    Functor.whiskerLeft _ (yoneda.map <| Over.homMk (𝒰.f i).toLRSHom)
  have : Presheaf.IsLocallySurjective
      (zariskiTopology (F ⋙ Over.forget B.toLocallyRingedSpace)) (Sigma.desc f) :=
    sorry
  apply RepresentabilityIsLocal.isRepresentable_sheaf' (F := F ⋙ Over.forget _)
    (f := f)
  · sorry
  · intro i
    apply isOpenImmersion_relativeYonedaPreComp

end Geometric

end CategoryTheory.Functor
