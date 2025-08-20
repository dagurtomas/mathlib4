/-
Copyright (c) 2025 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
import Mathlib

/-!

# Condensed Nöbeling's theorem

This file proves the condensed version of Nöbeling's theorem: for every profinite set `S`,
the condensed abelian group of maps of condensed abelian groups `S → ℤ` (i.e. the internal
hom from `ℤ[S]` to `ℤ`) is free as a condensed abelian group, i.e. isomorphic to a direct
sum of copies of `ℤ`.
-/

universe u

open Profinite CategoryTheory Limits Monoidal MonoidalCategory MonoidalClosed

namespace ModuleCat

variable (R : Type*) [Ring R] (M : ModuleCat R) [Module.Free R M]

open scoped Classical in
noncomputable def freeIsoCoprod :
    M ≅ ∐ (fun (_ : Module.Free.ChooseBasisIndex R M) ↦ ModuleCat.of R R) :=
  (Module.Free.chooseBasis R M).repr.toModuleIso ≪≫
    (finsuppLequivDFinsupp (ModuleCat.of R R)).toModuleIso ≪≫
      (ModuleCat.coprodIsoDirectSum
        (fun (_ : Module.Free.ChooseBasisIndex R M) ↦ ModuleCat.of R R)).symm

@[simps!]
noncomputable def freeCofan :
    Cofan (fun (_ : Module.Free.ChooseBasisIndex R M) ↦ ModuleCat.of R R) :=
  Cofan.mk M
    fun i ↦ ModuleCat.ofHom ((Module.Free.chooseBasis R M).repr.symm.comp (Finsupp.lsingle i))

instance : IsIso ((coproductIsCoproduct
    fun (_ : Module.Free.ChooseBasisIndex R M) ↦ ModuleCat.of R R).desc
    (ModuleCat.freeCofan R M)) :=
  sorry

noncomputable def freeCofanIsColimit : IsColimit (freeCofan R M) :=
  (coproductIsCoproduct _).ofPointIso

end ModuleCat

namespace Profinite

variable (S : Profinite.{u})

instance : Module.Free (ULift.{1} ℤ) (ULift (LocallyConstant S ℤ)) := by
  apply (config := {allowSynthFailures := true}) Module.Free.ulift
  let e : ℤ ≃+* (ULift.{1} ℤ) := ULift.ringEquiv.symm
  have := RingHomInvPair.of_ringEquiv e
  have := RingHomInvPair.of_ringEquiv e.symm
  exact Module.Free.of_ringEquiv (M := LocallyConstant S ℤ) e {
    toLinearMap := ⟨⟨id, fun _ _ ↦ rfl⟩, fun _ _ ↦ rfl⟩
    invFun := id
    left_inv := congrFun rfl
    right_inv := congrFun rfl }

end Profinite

namespace CondensedAb

noncomputable def of (X : Type u) [AddCommGroup X] : CondensedAb :=
  (Condensed.discrete _).obj (ModuleCat.of (ULift.{u+1} ℤ) (ULift.{u+1} X))

end CondensedAb

open CondensedAb

namespace Condensed

open scoped MonoidalClosed.FunctorCategory

noncomputable
instance : MonoidalCategory (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat (ULift.{u+1} ℤ))) :=
  Sheaf.monoidalCategory _ _

noncomputable
instance : MonoidalCategory CondensedAb.{u} := Sheaf.monoidalCategory _ _

noncomputable
instance : MonoidalClosed (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat (ULift.{u+1} ℤ))) :=
  Monoidal.Reflective.monoidalClosed (sheafificationAdjunction _ _)

noncomputable
instance : MonoidalClosed CondensedAb.{u} := inferInstanceAs (MonoidalClosed (Sheaf _ _))

instance : ((coherentTopology CompHaus.{u}).W (A := ModuleCat (ULift.{u+1} ℤ))).IsMonoidal :=
  inferInstance

instance : SymmetricCategory (Sheaf (coherentTopology CompHaus.{u}) (ModuleCat (ULift.{u+1} ℤ))) :=
  sorry -- We need to generalize the API for monoidal localizations to the symmetric case

instance : SymmetricCategory CondensedAb.{u} := inferInstanceAs (SymmetricCategory (Sheaf _ _))

variable (S : Profinite.{0})
variable (M : CondensedAb)

namespace NobelingProof

def index : Type 1 := Module.Free.ChooseBasisIndex
  (ULift.{1} ℤ) (ULift.{1} (LocallyConstant S ℤ))

noncomputable def freeCofan : Cofan (fun _ : index S ↦
    ModuleCat.of (ULift.{1} ℤ) (ULift.{1} ℤ)) :=
  ModuleCat.freeCofan (ULift.{1} ℤ) (ModuleCat.of _ (ULift.{1} (LocallyConstant S ℤ)))

noncomputable def freeCofanIsColimit : IsColimit (freeCofan S) :=
  ModuleCat.freeCofanIsColimit _ _

noncomputable def isoCoprod : ModuleCat.of (ULift.{1} ℤ) (ULift.{1} (LocallyConstant S ℤ)) ≅
    ∐ (fun _ : index S ↦ ModuleCat.of (ULift.{1} ℤ) (ULift.{1} ℤ)) :=
  (freeCofanIsColimit S).coconePointUniqueUpToIso (coproductIsCoproduct
    (fun _ : index S ↦ ModuleCat.of (ULift.{1} ℤ) (ULift.{1} ℤ)))

set_option quotPrecheck false
notation3 "ℤ[" S "]" => (profiniteFree (ULift ℤ)).obj S
notation3 "(*)" => Opposite.op (CompHaus.of PUnit)
notation3 "δ" => discrete (ModuleCat (ULift.{1} ℤ))

noncomputable def discreteInternalCocone :
    Cocone (S.diagram.op ⋙ (profiniteFree _).op ⋙ (MonoidalClosed.internalHom.flip.obj M)) :=
  ((profiniteFree _).op ⋙ (MonoidalClosed.internalHom.flip.obj M)).mapCocone S.asLimitCone.op

noncomputable def isColimitDiscreteInternal [M.IsDiscrete] :
    IsColimit (discreteInternalCocone S M) := by
  suffices IsLimit (discreteInternalCocone S M).op by
    exact Limits.isColimitOfOp this
  apply coyonedaJointlyReflectsLimits
  intro X
  sorry
  -- suffices IsLimit ((coyoneda.obj X).op.mapCocone (discreteInternalCocone S M)).op by exact?

instance : ((ihom ℤ[S]).obj (CondensedAb.of ℤ)).IsDiscrete := by sorry

noncomputable def isoUnderlyingOfDiscrete [M.IsDiscrete] :
    M ≅ (δ).obj (M.val.obj (*)) :=
  haveI : IsIso ((discreteUnderlyingAdj _).counit.app M) := by
    rwa [((CondensedMod.isDiscrete_tfae _ M).out 1 0:)]
  (asIso ((discreteUnderlyingAdj _).counit.app _)).symm

noncomputable def isoInternalLocConst :
    ((ihom ℤ[S]).obj (of ℤ)) ≅ of (LocallyConstant S ℤ) :=
  let i : ((ihom ℤ[S]).obj (of ℤ)).val.obj (*) ≅
      ModuleCat.of (ULift ℤ) (ULift (LocallyConstant S ℤ)) := by
    sorry
  (isoUnderlyingOfDiscrete _) ≪≫ (δ).mapIso i

end NobelingProof

open NobelingProof

instance : (δ).IsLeftAdjoint := (discreteUnderlyingAdj _).isLeftAdjoint

lemma nobeling : ∃ I : Type 1, Nonempty ((ihom ℤ[S]).obj (of ℤ) ≅ ∐ (fun (_ : I) ↦ of ℤ)) :=
  ⟨index S, ⟨isoInternalLocConst S ≪≫
    (Condensed.discrete _).mapIso (isoCoprod S) ≪≫ PreservesCoproduct.iso _ _⟩⟩

end Condensed
