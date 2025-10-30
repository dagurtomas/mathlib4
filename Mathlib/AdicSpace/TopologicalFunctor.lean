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

@[simp]
lemma toOver_hom {X : C} (U : Opens X) : U.toOver.hom = U.ι := rfl

noncomputable
def lift {Y : C} (f : Y ⟶ X) (U : Opens X) (hf : Set.range (toTopCat.map f) ⊆ U) :
    Y ⟶ U.toObj :=
  U.universalProperty.reprW.inv.app _ ⟨f, hf⟩

@[reassoc (attr := simp)]
lemma lift_fac {Y : C} (f : Y ⟶ X) (U : Opens X) (hf : Set.range (toTopCat.map f) ⊆ U) :
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

-- is this true?
lemma range_ι {X : C} (U : Opens X) : Set.range (toTopCat.map U.ι) = U := by
  have h : Set.range (toTopCat.map U.ι) ⊆ (U : Set _) :=
    U.universalProperty.reprx.2
  -- have : IsOpen (Set.range (toTopCat.map U.ι)) := sorry
  -- let U' : Opens X := ⟨_, this⟩
  let f : U.toObj ⟶ U.toObj :=
    U.lift _ h
  sorry

end Opens

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
def isOpenImmersion : MorphismProperty C := fun _ _ f ↦ IsOpenImmersion f

namespace IsOpenImmersion

instance ι {X : C} (U : Opens X) : IsOpenImmersion U.ι := ⟨⟨U, ⟨Iso.refl _⟩⟩⟩

noncomputable def opensRange {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] : Opens Y :=
  (mem_essImage f).witness

noncomputable def isoOpen {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] :
    X ≅ (opensRange f).toObj :=
  ((Over.forget _).mapIso (mem_essImage f).getIso).symm

@[reassoc (attr := simp)]
lemma isoOpen_hom_ι {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] :
    (isoOpen f).hom ≫ (opensRange f).ι = f :=
  Over.w (mem_essImage f).getIso.inv

lemma range_subset_opensRange {X Y : C} (f : X ⟶ Y) [IsOpenImmersion f] :
    Set.range (toTopCat.map f) ⊆ opensRange f := by
  conv_lhs => simp only [← isoOpen_hom_ι f]
  rw [Functor.map_comp]
  apply subset_trans _ (opensRange f).range_subset
  simp [Set.range_comp_subset_range]

noncomputable def lift {X U Y : C} (f : Y ⟶ X) (g : U ⟶ X) [IsOpenImmersion g]
    (hf : Set.range (toTopCat.map f) ⊆ Set.range (toTopCat.map g)) :
    Y ⟶ U :=
  (opensRange g).lift f (subset_trans hf <| range_subset_opensRange g) ≫ (isoOpen g).inv

--lemma isPullback {X U S : C} (f : X ⟶ S) (g : U ⟶ S) [IsOpenImmersion g] :
--    IsPullback _ _ f g :=
--  sorry

end IsOpenImmersion

end Topological

end CategoryTheory
