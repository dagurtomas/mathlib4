import Mathlib.AlgebraicGeometry.Sites.Pretopology
import Mathlib.CategoryTheory.MorphismProperty.Representable

universe u

open CategoryTheory Limits

variable {C : Type*} [Category C]

def TopologicalSpace.Opens.factorsThrough
    {F : C ⥤ TopCat.{u}} {X : C} (U : Opens (F.obj X)) :
    Sieve X where
  arrows Y f := Set.range (F.map f) ⊆ U
  downward_closed {Y Z} f hf g := subset_trans (by simp [Set.range_comp_subset_range]) hf

@[simps!]
def TopologicalSpace.Opens.universalProperty {F : C ⥤ TopCat.{u}} {X : C} (U : Opens (F.obj X)) :
    Cᵒᵖ ⥤ Type _ :=
  U.factorsThrough.functor

open TopologicalSpace

namespace CategoryTheory

class Topological (C : Type*) [Category C] where
  toTopCat : C ⥤ TopCat.{u}
  isRepresentable_universalProperty (X : C) (U : Opens (toTopCat.obj X)) :
    U.universalProperty.IsRepresentable
  nonempty_iso_inclusion' (X : C) (U : Opens (toTopCat.obj X)) :
    Nonempty (Over.mk (toTopCat.map U.universalProperty.reprx.val) ≅ Over.mk U.inclusion')

namespace Topological

attribute [instance] isRepresentable_universalProperty

variable [Topological C]

abbrev Opens (X : C) : Type := TopologicalSpace.Opens (toTopCat.obj X)

namespace Opens

noncomputable def toOver {X : C} (U : Opens X) : Over X :=
  .mk U.universalProperty.reprx.1

noncomputable def toObj {X : C} (U : Opens X) : C :=
  U.toOver.left

noncomputable def ι {X : C} (U : Opens X) : U.toObj ⟶ X :=
  U.toOver.hom

noncomputable def mapιIsoInclusion {X : C} (U : Opens X) :
    Over.mk (toTopCat.map U.ι) ≅ .mk U.inclusion' :=
  (nonempty_iso_inclusion' X U).some

@[reassoc (attr := simp)]
lemma mapιIsoInclusion_hom_inclusion' {X : C} (U : Opens X) :
    U.mapιIsoInclusion.hom.left ≫ U.inclusion' = toTopCat.map U.ι :=
  Over.w _

@[simp]
lemma toOver_hom {X : C} (U : Opens X) : U.toOver.hom = U.ι := rfl

@[simp]
lemma toOver_left {X : C} (U : Opens X) : U.toOver.left = U.toObj := rfl

noncomputable
def lift {X Y : C} (f : Y ⟶ X) (U : Opens X) (hf : Set.range (toTopCat.map f) ⊆ U) :
    Y ⟶ U.toObj :=
  U.universalProperty.reprW.inv.app _ ⟨f, hf⟩

@[reassoc (attr := simp)]
lemma lift_fac {X Y : C} (f : Y ⟶ X) (U : Opens X) (hf : Set.range (toTopCat.map f) ⊆ U) :
    U.lift f hf ≫ U.ι = f := by
  simpa [lift] using congr($(U.universalProperty.reprW_hom_app _ (U.lift f hf)).1).symm

instance {X : C} (U : Opens X) : Mono U.ι := by
  refine ⟨fun {Z} g h heq ↦ ?_⟩
  apply (U.universalProperty.reprW.app _).toEquiv.injective
  simp only [Opens.universalProperty_obj, yoneda_obj_obj, Iso.toEquiv_fun, Iso.app_hom,
    U.universalProperty.reprW_hom_app]
  ext
  exact heq

lemma range_subset {X : C} (U : Opens X) : Set.range (toTopCat.map U.ι) ⊆ U :=
  U.universalProperty.reprx.2

@[simp]
lemma map_ι_mem {X : C} (U : Opens X) (x : toTopCat.obj U.toObj) :
    toTopCat.map U.ι x ∈ U :=
  U.range_subset ⟨x, rfl⟩

@[simps hom]
noncomputable def topIso (X : C) : (⊤ : Opens X).toObj ≅ X where
  hom := (⊤ : Opens X).ι
  inv := (⊤ : Opens X).lift (𝟙 X) (by simp)
  hom_inv_id := by rw [← cancel_mono (⊤ : Opens X).ι]; simp

@[simp]
lemma range_ι {X : C} (U : Opens X) : Set.range (toTopCat.map U.ι) = U := by
  simp only [← mapιIsoInclusion_hom_inclusion', Over.mk_left, TopCat.hom_comp,
    ContinuousMap.coe_comp, Opens.coe_inclusion', Set.range_comp]
  rw [Function.Surjective.range_eq]
  · simp only [Set.image_univ]
    apply Subtype.range_coe
  exact ConcreteCategory.surjective_of_epi_of_preservesPushout _

lemma isOpenEmbedding_map {X : C} (U : Opens X) :
    Topology.IsOpenEmbedding (toTopCat.map U.ι) := by
  simp only [← mapιIsoInclusion_hom_inclusion', Over.mk_left, TopCat.hom_comp,
    ContinuousMap.coe_comp, Opens.coe_inclusion']
  refine U.2.isOpenEmbedding_subtypeVal.comp ?_
  exact ((TopCat.isIso_iff_isHomeomorph _).mp inferInstance).isOpenEmbedding

noncomputable
def isoOfEq {X : C} {U V : Opens X} (h : U = V) : U.toObj ≅ V.toObj where
  hom := V.lift U.ι (by simp [← h])
  inv := U.lift V.ι (by simp [h])
  hom_inv_id := by simp [← cancel_mono U.ι]
  inv_hom_id := by simp [← cancel_mono V.ι]

@[reassoc (attr := simp)]
lemma isoOfEq_hom_ι {X : C} {U V : Opens X} (h : U = V) : (isoOfEq h).hom ≫ V.ι = U.ι := by
  simp [isoOfEq]

@[reassoc (attr := simp)]
lemma isoOfEq_inv {X : C} {U V : Opens X} (h : U = V) : (isoOfEq h).inv = (isoOfEq h.symm).hom :=
  rfl

@[reassoc (attr := simp)]
lemma isoOfEq_symm {X : C} {U V : Opens X} (h : U = V) : (isoOfEq h).symm = isoOfEq h.symm :=
  rfl

def preimage {X Y : C} (f : X ⟶ Y) (U : Opens Y) : Opens X :=
  (Opens.map (toTopCat.map f)).obj U

@[simp]
lemma coe_preimage {X Y : C} (f : X ⟶ Y) (U : Opens Y) :
    (U.preimage f : Set _) = toTopCat.map f ⁻¹' U :=
  rfl

noncomputable
def restrict {X Y : C} (f : X ⟶ Y) (U : Opens Y) : (U.preimage f).toObj ⟶ U.toObj :=
  U.lift ((U.preimage f).ι ≫ f) <| by
    rw [Set.range_subset_iff]
    intro y
    simp only [Functor.map_comp, TopCat.hom_comp, ContinuousMap.comp_apply, SetLike.mem_coe]
    apply map_ι_mem _ y

@[reassoc (attr := simp)]
lemma restrict_ι {X Y : C} (f : X ⟶ Y) (U : Opens Y) :
    U.restrict f ≫ U.ι = (U.preimage f).ι ≫ f := by
  simp [restrict]

noncomputable
def isLimitPullbackRestrict {X Y : C} (U : Opens Y) (f : X ⟶ Y) :
    IsLimit (PullbackCone.mk (preimage f U).ι (restrict f U) (U.restrict_ι f).symm) :=
  PullbackCone.IsLimit.mk _
    (fun s ↦ (preimage f U).lift s.fst <| by
      simp only [coe_preimage, Set.range_subset_iff, Set.mem_preimage, SetLike.mem_coe]
      simp_rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, s.condition]
      simp)
    (fun s ↦ by simp)
    (fun s ↦ by simp [← cancel_mono U.ι, s.condition])
    (fun s m hm heq ↦ by simpa [← cancel_mono (U.preimage f).ι])

lemma isPullback {X Y : C} (U : Opens Y) (f : X ⟶ Y) :
    IsPullback (U.preimage f).ι (U.restrict f) f U.ι where
  isLimit' := ⟨isLimitPullbackRestrict _ _⟩

instance {X Y : C} (U : Opens Y) (f : X ⟶ Y) : HasPullback f U.ι :=
  ⟨⟨_, isLimitPullbackRestrict U f⟩⟩

end Opens

@[simps obj]
noncomputable def opens (X : C) : Opens X ⥤ Over X where
  obj U := U.toOver
  map {U V} f := Over.homMk (V.lift U.ι (subset_trans U.universalProperty.reprx.2 f.1.1))
  map_id U := by
    ext
    rw [← cancel_mono U.ι]
    simp
  map_comp {U V W} f g := by
    ext
    rw [← cancel_mono W.ι]
    simp

/-- A morphism in a topological category is an open immersion if it is isomorphic to
the canonical inclusion of an open. -/
class IsOpenImmersion {X Y : C} (f : X ⟶ Y) : Prop where
  mem_essImage (f) : (opens Y).essImage (Over.mk f)

variable (C) in
@[inherit_doc IsOpenImmersion]
abbrev isOpenImmersion : MorphismProperty C := fun _ _ f ↦ IsOpenImmersion f

namespace IsOpenImmersion

lemma iff {X Y : C} (f : X ⟶ Y) :
    IsOpenImmersion f ↔ ∃ (U : Opens Y) (e : X ≅ U.toObj), e.hom ≫ U.ι = f :=
  ⟨fun ⟨⟨U, ⟨e⟩⟩⟩ ↦ ⟨U, (Over.forget _).mapIso e.symm, Over.w e.inv⟩,
    fun ⟨U, e, h⟩ ↦ ⟨U, ⟨Over.isoMk e.symm (by simp [← h])⟩⟩⟩

instance ι {X : C} (U : Opens X) : IsOpenImmersion U.ι := ⟨⟨U, ⟨Iso.refl _⟩⟩⟩

instance {X Y : C} (f : X ⟶ Y) [IsIso f] : IsOpenImmersion f :=
  ⟨⟨⊤, ⟨Over.isoMk (Opens.topIso Y ≪≫ (asIso f).symm) (by simp)⟩⟩⟩

lemma isOpenEmbedding {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] :
    Topology.IsOpenEmbedding (toTopCat.map f) := by
  have : _ ≫ _ = f := Over.w (mem_essImage f).getIso.inv
  rw [← this, Functor.map_comp, TopCat.isOpenEmbedding_iff_isIso_comp]
  exact Opens.isOpenEmbedding_map _

@[simps]
def _root_.CategoryTheory.Topological.Opens.image {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f]
    (U : Opens X) : Opens Y :=
  ⟨toTopCat.map f '' U, (isOpenEmbedding f).isOpenMap _ U.2⟩

lemma range_map_eq_of_iso {X Y : C} (f : X ⟶ Y) (U : Opens Y) (e : Over.mk f ≅ .mk U.ι) :
    Set.range (toTopCat.map f) = U := by
  have : e.hom.left ≫ U.ι = f := Over.w e.hom
  rw [← this, Functor.map_comp, hom_comp, Function.Surjective.range_comp]
  · simp
  · exact ConcreteCategory.surjective_of_epi_of_preservesPushout (toTopCat.map e.hom.left)

@[simps]
noncomputable def opensRange {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] : Opens Y :=
  ⟨Set.range (toTopCat.map f), (isOpenEmbedding f).isOpen_range⟩

noncomputable def isoOpen {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] :
    X ≅ (opensRange f).toObj :=
  ((Over.forget _).mapIso (mem_essImage f).getIso).symm ≪≫
    Opens.isoOfEq (by ext : 1; exact (range_map_eq_of_iso _ _ (mem_essImage f).getIso.symm).symm)

@[reassoc (attr := simp)]
lemma isoOpen_hom_ι {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] :
    (isoOpen f).hom ≫ (opensRange f).ι = f := by
  simpa [isoOpen] using Over.w (mem_essImage f).getIso.inv

@[reassoc (attr := simp)]
lemma isoOpen_inv_comp {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] :
    (isoOpen f).inv ≫ f = (opensRange f).ι := by
  simp_rw [← isoOpen_hom_ι f, Iso.inv_hom_id_assoc]

noncomputable def lift {X U Y : C} (f : Y ⟶ X) (g : U ⟶ X) [IsOpenImmersion g]
    (hf : Set.range (toTopCat.map f) ⊆ Set.range (toTopCat.map g)) :
    Y ⟶ U :=
  (opensRange g).lift f hf ≫ (isoOpen g).inv

instance {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] : Mono f := by
  rw [← isoOpen_hom_ι f]
  infer_instance

instance {X U S : C} (f : X ⟶ S) (g : U ⟶ S) [IsOpenImmersion g] : HasPullback f g := by
  rw [← isoOpen_hom_ι g]
  have : HasPullback (pullback.snd f (opensRange g).ι) (isoOpen g).hom :=
    hasPullback_of_right_iso _ _
  exact hasPullbackVertPaste _ _ _

instance {X U S : C} (f : X ⟶ S) (g : U ⟶ S) [IsOpenImmersion g] : HasPullback g f :=
  hasPullback_symmetry f g

noncomputable def isoImage {X Y : C} (f : X ⟶ Y) (U : Opens X) [IsOpenImmersion f] :
    U.toObj ≅ (U.image f).toObj where
  hom := (Opens.image f U).lift (U.ι ≫ f) (by simp [Set.range_comp])
  inv := U.lift ((opensRange f).lift (Opens.image f U).ι (by simp) ≫
    (isoOpen f).inv) (by simp [Set.range_comp]; sorry)
  hom_inv_id := by simp [← cancel_mono U.ι, ← cancel_mono f]
  inv_hom_id := by simp [← cancel_mono (Opens.image f U).ι]

@[reassoc (attr := simp)]
lemma isoImage_hom_ι {X Y : C} (f : X ⟶ Y) (U : Opens X) [IsOpenImmersion f] :
    (isoImage f U).hom ≫ (U.image f).ι = U.ι ≫ f := by
  simp [isoImage]

@[reassoc (attr := simp)]
lemma isoImage_inv_ι {X Y : C} (f : X ⟶ Y) (U : Opens X) [IsOpenImmersion f] :
    (isoImage f U).inv ≫ U.ι ≫ f = (Opens.image f U).ι := by
  simp [← isoImage_hom_ι]

instance comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) [IsOpenImmersion f] [IsOpenImmersion g] :
    IsOpenImmersion (f ≫ g) := by
  rw [iff]
  use (opensRange f).image g, isoOpen f ≪≫ isoImage g (opensRange f)
  simp

instance {X U S : C} (f : X ⟶ S) (g : U ⟶ S) [IsOpenImmersion g] :
    IsOpenImmersion (pullback.fst f g) :=
  sorry

end IsOpenImmersion

instance : (isOpenImmersion C).IsStableUnderComposition where
  comp_mem _ _ _ _ := inferInstance

instance : (isOpenImmersion C).RespectsIso :=
  sorry

instance : (isOpenImmersion C).IsStableUnderComposition :=
  sorry

instance : (isOpenImmersion C).ContainsIdentities :=
  sorry

variable (C) in
protected def forget : C ⥤ Type u :=
  toTopCat ⋙ CategoryTheory.forget TopCat

variable (C) in
def zariskiPrecoverage : Precoverage C :=
  Types.jointlySurjectivePrecoverage.comap (Topological.forget C) ⊓ (isOpenImmersion C).precoverage

instance : (zariskiPrecoverage C).IsStableUnderComposition := by
  dsimp [zariskiPrecoverage]
  infer_instance

instance : (zariskiPrecoverage C).IsStableUnderBaseChange :=
  sorry

instance : (zariskiPrecoverage C).HasIsos := by
  dsimp [zariskiPrecoverage]
  infer_instance

instance : (zariskiPrecoverage C).HasPullbacks := by
  refine ⟨fun {X Y} R f hR ↦ ⟨fun {Z} h hh ↦ ?_⟩⟩
  have : IsOpenImmersion h := hR.2 hh
  infer_instance

variable (C) in
def zariskiTopology : GrothendieckTopology C :=
  (zariskiPrecoverage C).toGrothendieck

end Topological

protected class Functor.Topological {C D : Type*} [Category C] [Category D] [Topological C]
    [Topological D] (F : C ⥤ D) where
  compIso (F) : F ⋙ Topological.toTopCat ≅ Topological.toTopCat

alias Functor.compToTopCatIso := Functor.Topological.compIso

variable {C D : Type*} [Category C] [Category D] [Topological C] [Topological D]

namespace Functor

open Topological

def opensEquiv (F : C ⥤ D) [F.Topological] (X : C) :
    Opens X ≃o Opens (F.obj X) :=
  (TopCat.homeoOfIso (F.compToTopCatIso.symm.app X)).opensCongr

-- is this true or do we need more assumptions?
noncomputable
def mapIsoOpensEquiv (F : C ⥤ D) [F.Topological] {X : C} (U : Opens X) :
    F.obj U.toObj ≅ (F.opensEquiv X U).toObj where
  hom := (F.opensEquiv X U).lift (F.map U.ι) sorry
  inv := sorry
  hom_inv_id := sorry
  inv_hom_id := sorry

@[reassoc (attr := simp)]
lemma mapIsoOpensEquiv_hom_ι (F : C ⥤ D) [F.Topological] {X : C} (U : Opens X) :
    (F.mapIsoOpensEquiv U).hom ≫ (F.opensEquiv X U).ι = F.map U.ι := by
  simp [mapIsoOpensEquiv]

instance {E : Type*} [Category E] [Topological E] (F : C ⥤ D) (G : D ⥤ E)
    [F.Topological] [G.Topological] :
    (F ⋙ G).Topological where
  compIso := Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft F G.compToTopCatIso ≪≫
    F.compToTopCatIso

instance (F : C ⥤ D) [F.Topological] {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] :
    IsOpenImmersion (F.map f) := by
  rw [IsOpenImmersion.iff]
  refine ⟨F.opensEquiv Y (IsOpenImmersion.opensRange f), ?_, ?_⟩
  · exact F.mapIso (IsOpenImmersion.isoOpen f) ≪≫ F.mapIsoOpensEquiv _
  · simp [← F.map_comp]

variable {C D B : Type*} [Category C] [Category D] [Category B]
  [Topological C] [Topological D] [Topological B]
variable {L : C ⥤ B} {R : D ⥤ B} [L.Topological] [R.Topological]

noncomputable def relativePullback {U X : C} {Y : D} (f : U ⟶ X) [IsOpenImmersion f]
    (g : R.obj Y ⟶ L.obj X) : D :=
  (R.opensEquiv Y).symm ((L.opensEquiv X (IsOpenImmersion.opensRange f)).preimage g) |>.toObj

noncomputable def relativePullback.snd {U X : C} {Y : D} (f : U ⟶ X) [IsOpenImmersion f]
    (g : R.obj Y ⟶ L.obj X) : relativePullback f g ⟶ Y :=
  (R.opensEquiv Y).symm ((L.opensEquiv X (IsOpenImmersion.opensRange f)).preimage g) |>.ι

noncomputable def relativePullback.fst {U X : C} {Y : D} (f : U ⟶ X) [IsOpenImmersion f]
    (g : R.obj Y ⟶ L.obj X) : R.obj (relativePullback f g) ⟶ L.obj U :=
  IsOpenImmersion.lift (R.map (relativePullback.snd f g) ≫ g) (L.map f) sorry

lemma relativePullback.condition {U X : C} {Y : D} (f : U ⟶ X) [IsOpenImmersion f]
    (g : R.obj Y ⟶ L.obj X) :
    fst f g ≫ L.map f = R.map (snd f g) ≫ g :=
  sorry

noncomputable
def relativePullback.lift {U X : C} {Y : D} {f : U ⟶ X} [IsOpenImmersion f]
    {g : R.obj Y ⟶ L.obj X} {Z : D} (a : Z ⟶ Y) (b : R.obj Z ⟶ L.obj U)
    (hab : R.map a ≫ g = b ≫ L.map f) :
    Z ⟶ relativePullback f g :=
  Opens.lift a _ sorry

@[reassoc (attr := simp)]
lemma relativePullback.lift_snd {U X : C} {Y : D} {f : U ⟶ X} [IsOpenImmersion f]
    {g : R.obj Y ⟶ L.obj X} {Z : D} (a : Z ⟶ Y) (b : R.obj Z ⟶ L.obj U)
    (hab : R.map a ≫ g = b ≫ L.map f) :
    lift a b hab ≫ snd f g = a :=
  sorry

@[reassoc (attr := simp)]
lemma relativePullback.lift_fst {U X : C} {Y : D} {f : U ⟶ X} [IsOpenImmersion f]
    {g : R.obj Y ⟶ L.obj X} {Z : D} (a : Z ⟶ Y) (b : R.obj Z ⟶ L.obj U)
    (hab : R.map a ≫ g = b ≫ L.map f) :
    R.map (lift a b hab) ≫ fst f g = b :=
  sorry

lemma relativePullback.hom_ext {U X : C} {Y : D} {f : U ⟶ X} [IsOpenImmersion f]
    {g : R.obj Y ⟶ L.obj X} {Z : D} {u v : Z ⟶ relativePullback f g}
    (h₁ : R.map u ≫ fst f g = R.map v ≫ fst f g) (h₂ : u ≫ snd f g = v ≫ snd f g) :
    u = v :=
  sorry

end Functor

end CategoryTheory
