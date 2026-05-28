/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Category.AlgCat.Basic
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic

/-!

# Filtered colimits in the category of `R`-algebras

In this file we show that the forgetful functor from `R`-algebras to rings
creates filtered colimits.
-/

public section

universe w v u

open CategoryTheory Limits

variable {R : Type u} [CommRing R] {J : Type*} [Category* J] {F : J ⥤ AlgCat.{v} R}
  [PreservesColimitsOfShape J (forget RingCat.{v})]

-- These scoped unification hints keep the implementation below from relying on
-- `backward.isDefEq.respectTransparency false`.
unif_hint algCat_forget₂_comp_obj_carrier_unif {R : Type u} [CommRing R]
    {J : Type w} [Category* J] (F F' : J ⥤ AlgCat.{v} R) (j j' : J) where
  F ≟ F'
  j ≟ j' ⊢
  (F.obj j).carrier ≟ ((F' ⋙ forget₂ (AlgCat.{v} R) RingCat.{v}).obj j').carrier in
unif_hint const_obj_unif {C : Type u} [Category.{v} C] {J : Type w} [Category* J]
    (X X' : C) (j : J) where
  X ≟ X' ⊢
  X ≟ ((Functor.const J).obj X').obj j in
section

variable {c : Cocone (F ⋙ forget₂ _ RingCat)} [IsFilteredOrEmpty J]

omit [PreservesColimitsOfShape J (forget RingCat)] [IsFilteredOrEmpty J] in
private lemma AlgCat.cocone_ι_app_algebraMap_eq (c : Cocone (F ⋙ forget₂ (AlgCat R) RingCat))
    {j k : J} (f : j ⟶ k) (r : R) :
    (c.ι.app k).hom ((algebraMap R (F.obj k)) r) =
      (c.ι.app j).hom ((algebraMap R (F.obj j)) r) := by
  rw [← AlgHom.commutes (F.map f).hom r]
  exact ConcreteCategory.congr_hom (c.w f) ((algebraMap R (F.obj j)) r)

omit [PreservesColimitsOfShape J (forget RingCat)] [IsFilteredOrEmpty J] in
private lemma AlgCat.cocone_ι_app_algebraMap_comp_eq (c : Cocone (F ⋙ forget₂ (AlgCat R) RingCat))
    {j k : J} (f : j ⟶ k) (r : R) :
    ((c.ι.app j).hom.comp (algebraMap R (F.obj j))) r =
      (c.ι.app k).hom ((algebraMap R (F.obj k)) r) := by
  rw [RingHom.comp_apply]
  exact (AlgCat.cocone_ι_app_algebraMap_eq c f r).symm

omit [PreservesColimitsOfShape J (forget RingCat)] [IsFilteredOrEmpty J] in
private lemma AlgCat.forget₂_map_algebraMap {X Y : AlgCat.{v} R} (f : X ⟶ Y) (r : R) :
    ((forget₂ (AlgCat R) RingCat).map f) ((algebraMap R X) r) = (algebraMap R Y) r :=
  AlgHom.commutes f.hom r

/-- (Implementation): The algebra instance on the cocone point of the underlying diagram of rings
is induced from the `j`-th inclusion map. Any choice of `j` gives a propositionally equal algebra
instance. -/
private abbrev AlgCat.algebraOfIsFiltered (hc : IsColimit c) (j : J) : Algebra R c.pt :=
  (c.ι.app j).hom.comp (algebraMap R (F.obj j)) |>.toAlgebra' <| by
    intro r x
    obtain ⟨k, hjk, y, rfl⟩ := Concrete.exists_hom_ι_eq_of_isColimit _ hc x j
    rw [AlgCat.cocone_ι_app_algebraMap_comp_eq c hjk r]
    have hcomm : (algebraMap R (F.obj k)) r * y =
        y * (algebraMap R (F.obj k)) r := Algebra.commutes _ _
    simpa only [map_mul] using congrArg (c.ι.app k).hom hcomm

/-- The cocone of the underlying diagram of rings lifted to `AlgCat R`. The algebra instance
on the cocone point is induced from the `j`-th inclusion map. -/
private def AlgCat.coconeOfIsFiltered (hc : IsColimit c) (j : J) : Cocone F where
  pt :=
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    AlgCat.of R c.pt
  ι.app k := by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (c.ι.app k).hom, commutes' r := ?_ }
    rw [RingHom.algebraMap_toAlgebra', RingHom.comp_apply]
    exact (AlgCat.cocone_ι_app_algebraMap_eq c (IsFiltered.rightToMax j k) r).symm.trans
      (AlgCat.cocone_ι_app_algebraMap_eq c (IsFiltered.leftToMax j k) r)
  ι.naturality k k' f := by
    ext
    apply elementwise_of% c.ι.naturality

/-- The lifted cocone is colimiting. -/
private def AlgCat.isColimitCoconeOfIsFiltered (hc : IsColimit c) (j : J) :
    IsColimit (AlgCat.coconeOfIsFiltered hc j) where
  desc s := by
    letI : Algebra R c.pt := algebraOfIsFiltered hc j
    refine AlgCat.ofHom { __ := (hc.desc <| Functor.mapCocone _ s).hom, commutes' r := ?_ }
    rw [RingHom.algebraMap_toAlgebra', RingHom.comp_apply]
    exact (IsColimit.fac_apply hc ((forget₂ (AlgCat R) RingCat).mapCocone s) j
      ((algebraMap R (F.obj j)) r)).trans
      (AlgCat.forget₂_map_algebraMap (s.ι.app j) r)
  fac s k := by
    ext
    apply elementwise_of% hc.fac
  uniq s m hm := by
    ext
    refine congr($(hc.uniq (Functor.mapCocone _ s) ((forget₂ _ _).map m) fun j ↦ ?_) _)
    ext
    exact congr($(hm _) _)

end

@[no_expose] noncomputable instance [IsFiltered J] :
    CreatesColimitsOfShape J (forget₂ (AlgCat.{v} R) RingCat.{v}) where
  CreatesColimit := createsColimitOfReflectsIso fun _ hc ↦
    ⟨⟨AlgCat.coconeOfIsFiltered hc IsFiltered.nonempty.some, Iso.refl _⟩,
      AlgCat.isColimitCoconeOfIsFiltered _ _⟩

noncomputable instance [IsFiltered J] [HasColimitsOfShape J RingCat.{v}] :
    HasColimitsOfShape J (AlgCat.{v} R) :=
  hasColimitsOfShape_of_hasColimitsOfShape_createsColimitsOfShape (forget₂ _ RingCat.{v})

instance : PreservesFilteredColimits (forget₂ (AlgCat.{v} R) RingCat.{v}) where
  preserves_filtered_colimits _ := inferInstance

instance : PreservesFilteredColimits (forget (AlgCat.{v} R)) :=
  Limits.comp_preservesFilteredColimits (forget₂ _ _) (forget RingCat.{v})
