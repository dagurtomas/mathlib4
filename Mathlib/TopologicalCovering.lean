import Mathlib.AdicSpace

universe u

open CategoryTheory GrothendieckTopology AlgebraicGeometry

variable {C : Type*} [Category C]

namespace AdicSpace

def zariskiCoverage : Coverage (AdicSpace.{u}) where
  covering X P := (∀ (Y : AdicSpace) (f : Y ⟶ X), P f → IsOpenImmersion f) ∧
    ∀ x : X, ∃ (Y : AdicSpace) (f : Y ⟶ X), P f ∧ x ∈ Set.range f.hom.base
  -- need to show that the category of adic spaces has pullbacks fist
  pullback X Y f R := sorry

class IsLocalIso {X Y : AdicSpace.{u}} (f : X ⟶ Y) : Prop where
  exists_isOpenImmersion :
    ∀ (x : X.1.carrier), ∃ (U : AdicSpace) (i : U ⟶ X),
      x ∈ Set.range i.base ∧ IsOpenImmersion (i ≫ f)

variable {X Y : AdicSpace.{u}}

instance (f : X ⟶ Y) [IsOpenImmersion f] : IsLocalIso f := by
  constructor
  intro x
  refine ⟨X, 𝟙 X, ?_, ?_⟩
  · use x
    rfl
  · rw [Category.id_comp]
    infer_instance

/-- A topological cover is a surjective local isomorphism. -/
class IsTopologicalCover (f : X ⟶ Y) : Prop extends IsLocalIso f where
  surjective : Function.Surjective f.hom.base

variable (P : MorphismProperty AdicSpace.{u})

def sourceLocalClosure : MorphismProperty AdicSpace.{u} :=
  fun X _ f ↦
    ∀ (x : X.1), ∃ (U : AdicSpace) (i : U ⟶ X),
      x ∈ Set.range i.base ∧ P (i ≫ f)

def targetLocalClosure : MorphismProperty AdicSpace.{u} :=
  fun _ Y f ↦ ∀ (y : Y), ∃ (U : Y.Opens), y ∈ U ∧ P (f.restrict U)

/-- An adic space is affinoid if and only if it is isomorphic to the `Spa` of a
Huber pair. -/
class IsAffinoid (X : AdicSpace.{u}) : Prop where
  exists_huberPair_nonempty_iso : ∃ (A : HuberPair.{u}),
    Nonempty ((forgetToPreLVCRS.obj X) ≅ Spa.{u} A)

/-- An morphism of adic spaces is affinoid if the preimage of every
affinoid open is affinoid. -/
class IsAffinoidHom (f : X ⟶ Y) : Prop where
  isAffinoid_preimage (U : Y.Opens) (hU : IsAffinoid U) : IsAffinoid (U.preimage f)

open Opposite

def Hom.appLE (f : X ⟶ Y) (U : Y.Opens) (V : X.Opens) (hUV : V ≤ U.preimage f) :
    Γ(Y, U) ⟶ Γ(X, V) :=
  f.1.1.c.app (op U) ≫ X.presheaf.map (homOfLE hUV).op

/-- A finite étale morphism of adic spaces is an affinoid morphism that
is finite étale on affines. -/
class FiniteEtale (f : X ⟶ Y) : Prop extends IsAffinoidHom f where
  finiteEtale_appLE (U : Y.Opens) (hU : IsAffinoid U) :
    (f.appLE U _ le_rfl).1.1.Etale ∧ (f.appLE U _ le_rfl).1.1.Finite

/-- A morphism of adic spaces is tempered if and only if it is source and target
locally a finite étale morphism. -/
abbrev Tempered (f : X ⟶ Y) : Prop :=
  sourceLocalClosure @FiniteEtale f

end AdicSpace
