import Mathlib.CategoryTheory.Limits.Presheaf

namespace CategoryTheory

open Category Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace Presheaf

variable {C : Type u₁} [Category.{v₁} C]

variable {ℰ : Type u₂} [Category.{v₂} ℰ] (A : C ⥤ ℰ)

/--
The functor taking `(E : ℰ) (c : Cᵒᵖ)` to the homset `(A.obj C ⟶ E)`. It is shown in `L_adjunction`
that this functor has a left adjoint (provided `E` has colimits) given by taking colimits over
categories of elements.
In the case where `ℰ = Cᵒᵖ ⥤ Type u` and `A = yoneda`, this functor is isomorphic to the identity.

Defined as in [MM92], Chapter I, Section 5, Theorem 2.
-/
@[simps!]
def restrictedYoneda' : ℰ ⥤ Cᵒᵖ ⥤ Type (max v₁ v₂) :=
  -- let F := yoneda ⋙ (whiskeringLeft _ _ (Type v₂)).obj (Functor.op A)
  yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor ⋙
    (whiskeringLeft _ _ (Type _)).obj (Functor.op A)

/-- Auxiliary definition for `restrictedYonedaHomEquiv`. -/
def restrictedYoneda'HomEquiv' (P : Cᵒᵖ ⥤ Type (max v₁ v₂)) (E : ℰ) :
    (CostructuredArrow.proj (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor) P ⋙ A ⟶
      (Functor.const (CostructuredArrow
        (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor) P)).obj E) ≃
      (P ⟶ (restrictedYoneda' A).obj E) where
  toFun f :=
    { app := fun _ x => ⟨f.app (CostructuredArrow.mk ((yonedaCompUliftFunctorEquiv _ _).symm x))⟩
      naturality := fun {X₁ X₂} φ => by stop
        ext x
        let ψ : CostructuredArrow.mk (yonedaEquiv.symm (P.toPrefunctor.map φ x)) ⟶
          CostructuredArrow.mk (yonedaEquiv.symm x) := CostructuredArrow.homMk φ.unop (by
            dsimp [yonedaEquiv]
            aesop_cat )
        simpa using (f.naturality ψ).symm }
  invFun g :=
    { app := fun y => (yonedaCompUliftFunctorEquiv _ _ (y.hom ≫ g)).1
      naturality := fun {X₁ X₂} φ => by stop
        dsimp
        rw [← CostructuredArrow.w φ]
        dsimp [yonedaEquiv]
        simp only [comp_id, id_comp]
        refine (congr_fun (g.naturality φ.left.op) (X₂.hom.app (Opposite.op X₂.left)
          (𝟙 _))).symm.trans ?_
        dsimp
        apply congr_arg
        simpa using congr_fun (X₂.hom.naturality φ.left.op).symm (𝟙 _) }
  left_inv f := by stop
    ext ⟨X, ⟨⟨⟩⟩, φ⟩
    suffices yonedaEquiv.symm (φ.app (Opposite.op X) (𝟙 X)) = φ by
      dsimp
      erw [yonedaEquiv_apply]
      dsimp [CostructuredArrow.mk]
      erw [this]
    exact yonedaEquiv.injective (by aesop_cat)
  right_inv g := by stop
    ext X x
    dsimp
    erw [yonedaEquiv_apply]
    dsimp
    rw [yonedaEquiv_symm_app_apply]
    simp

section

example [HasColimitsOfSize.{v₁, max u₁ v₁} ℰ] :
    yoneda.HasPointwiseLeftKanExtension A := inferInstance

variable [(yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂}).HasPointwiseLeftKanExtension A]

variable {A}
variable (L : (Cᵒᵖ ⥤ Type (max v₁ v₂)) ⥤ ℰ)
  (α : A ⟶ (yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{v₂}) ⋙ L)

section

variable [L.IsLeftKanExtension α]

/-- Auxiliary definition for `yonedaAdjunction`. -/
noncomputable def restrictedYoneda'HomEquiv (P : Cᵒᵖ ⥤ Type (max v₁ v₂)) (E : ℰ) :
    (L.obj P ⟶ E) ≃ (P ⟶ (restrictedYoneda' A).obj E) :=
  (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension _ α P).homEquiv.trans
    (restrictedYoneda'HomEquiv' A P E)

/-- If `L : (Cᵒᵖ ⥤ Type v₁) ⥤ ℰ` is a pointwise left Kan extension
of a functor `A : C ⥤ ℰ` along the Yoneda embedding,
then `L` is a left adjoint of `restrictedYoneda A : ℰ ⥤ Cᵒᵖ ⥤ Type v₁` -/
noncomputable def yonedaAdjunction' : L ⊣ restrictedYoneda' A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := restrictedYoneda'HomEquiv L α
      homEquiv_naturality_left_symm := fun {P Q X} f g => by stop
        obtain ⟨g, rfl⟩ := (restrictedYonedaHomEquiv L α Q X).surjective g
        apply (restrictedYonedaHomEquiv L α P X).injective
        simp only [Equiv.apply_symm_apply, Equiv.symm_apply_apply]
        ext Y y
        dsimp [restrictedYonedaHomEquiv, restrictedYonedaHomEquiv', IsColimit.homEquiv]
        rw [assoc, assoc, ← L.map_comp_assoc]
        congr 3
        apply yonedaEquiv.injective
        simp [yonedaEquiv]
      homEquiv_naturality_right := fun {P X Y} f g => by stop
        apply (restrictedYonedaHomEquiv L α P Y).symm.injective
        simp only [Equiv.symm_apply_apply]
        dsimp [restrictedYonedaHomEquiv, restrictedYonedaHomEquiv', IsColimit.homEquiv]
        apply (Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension L α P).hom_ext
        intro p
        rw [IsColimit.fac]
        dsimp [restrictedYoneda, yonedaEquiv]
        simp only [assoc]
        congr 3
        apply yonedaEquiv.injective
        simp [yonedaEquiv] }

end

/-- See Property 2 of https://ncatlab.org/nlab/show/Yoneda+extension#properties. -/
noncomputable instance preservesColimitsOfSize_leftKanExtension' :
    PreservesColimitsOfSize.{v₃, u₃}
      ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor).leftKanExtension A) :=
  (yonedaAdjunction' ((yoneda ⋙ (whiskeringRight _ _ _).obj uliftFunctor).leftKanExtension A)
    ((yoneda ⋙ (whiskeringRight _ _ _).obj
      uliftFunctor).leftKanExtensionUnit A)).leftAdjoint_preservesColimits

end

end CategoryTheory.Presheaf
