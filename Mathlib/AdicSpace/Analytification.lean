import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.MorphismProperty.Representable

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

open Try2

variable {C : Type (u + 1)} [Category.{u} C]
variable {B : Scheme.{u}} (F : C ⥤ Over B.toLocallyRingedSpace)
  [Geometric (F ⋙ Over.forget _)]

-- add assumptions
theorem of_exists_locally [Geometric (F ⋙ Over.forget _)]
    [RepresentabilityIsLocal (F ⋙ Over.forget _)]
    {X : Scheme} (s : X ⟶ B) (𝒰 : Scheme.OpenCover.{u} X)
    [h : ∀ i, HasAnalytification F (𝒰.f i ≫ s)] :
    HasAnalytification F s := by
  simp_rw [hasAnalytification_iff_isRepresentable] at ⊢
  let f (i : 𝒰.I₀) : yoneda.obj (analytification F (𝒰.f i ≫ s)) ⟶ relativeYoneda F s :=
    sorry
  have : Presheaf.IsLocallySurjective
      (zariskiTopology (F ⋙ Over.forget B.toLocallyRingedSpace)) (Sigma.desc f) :=
    sorry
  apply RepresentabilityIsLocal.isRepresentable_sheaf (F := F ⋙ Over.forget _)
    (f := f)
  · sorry
  · sorry

end Geometric

end CategoryTheory.Functor
