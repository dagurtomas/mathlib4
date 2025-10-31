import Mathlib.AdicSpace.TopologicalFunctor

open CategoryTheory Opposite

-- Think `D` is adic spaces over `Spa k`, `C` is schemes over `Spec k` and
-- `B` is locally ringed spaces over `Spec k`
variable {C D B : Type*} [Category C] [Category D] [Category B]
variable (L : C ⥤ B) (R : D ⥤ B)

namespace CategoryTheory.Analytification

@[simps]
def universalProperty : C ⥤ Dᵒᵖ ⥤ Type _ where
  obj X := R.op ⋙ yoneda.obj (L.obj X)
  map f := Functor.whiskerLeft _ (yoneda.map <| L.map f)

abbrev HasAnalytification (X : C) : Prop :=
  (universalProperty L R |>.obj X).IsRepresentable

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

lemma relativelyRepresentable_universalProperty {U X : C} (f : U ⟶ X) [IsOpenImmersion f] :
    yoneda.relativelyRepresentable ((universalProperty L R).map f) := by
  intro Z g
  let g' : R.obj Z ⟶ L.obj X := g.app _ (𝟙 Z)
  use Functor.relativePullback f g', Functor.relativePullback.snd _ _
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
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro W (h : W.unop ⟶ Functor.relativePullback f g')
    exact R.map h ≫ Functor.relativePullback.fst _ _
  · cat_disch
  · refine ⟨⟨?_⟩, ?_⟩
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

lemma isOpenImmersion_relativeYonedaPreComp {U X : C} (f : U ⟶ X) [IsOpenImmersion f] :
    (isOpenImmersion D).presheaf ((universalProperty L R).map f) := by
  refine MorphismProperty.relative.of_exists ?_
  sorry

end CategoryTheory.Analytification
