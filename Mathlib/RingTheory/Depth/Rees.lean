/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!

# The Rees theorem

In this file we prove the Rees theorem for depth, which relates the vanishing of
certain `Ext` groups and the length of a maximal regular sequence in a certain ideal.

## Main results

* `ModuleCat.exists_isRegular_tfae` (Rees theorem) : For any `n : ℕ`, noetherian ring `R`,
  `I : Ideal R`, and finitely generated and nontrivial `R`-module `M` satisfying `IM < M`,
  the following are equivalent:
  · for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
    zero locus of `I`, `∀ i < n, Ext N M i = 0`
  · `∀ i < n, Ext (A⧸I) M i = 0`
  · there exists a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
    zero locus of `I`, `∀ i < n, Ext N M i = 0`
  · there exists a `M`-regular sequence of length `n` with every element in `I`

-/

@[expose] public section

open IsLocalRing LinearMap Module

universe v u

open RingTheory.Sequence Ideal CategoryTheory Abelian Limits

variable {R : Type u} [CommRing R] [Small.{v} R]

open Pointwise ModuleCat IsSMulRegular

namespace Ideal

omit [Small.{v} R] in
lemma smul_top_quotSMulTop_ne_top_of_smul_top_lt_top {M : Type*} [AddCommGroup M]
    [Module R M] {I : Ideal R} {r : R} (hr : r ∈ I)
    (hI : I • (⊤ : Submodule R M) < ⊤) :
    I • (⊤ : Submodule R (QuotSMulTop r M)) ≠ ⊤ := by
  by_contra eq
  absurd congrArg (Submodule.comap (Submodule.mkQ _)) eq
  simpa [Submodule.comap_smul_top_of_surjective I _ (Submodule.mkQ_surjective _),
    Submodule.smul_mono_left ((span_singleton_le_iff_mem I).mpr hr),
    ← Submodule.ideal_span_singleton_smul] using hI.ne

end Ideal

namespace Module

omit [Small.{v} R] in
lemma exists_pow_mem_annihilator_of_mem_of_support_subset_zeroLocus [IsNoetherianRing R]
    {N : Type*} [AddCommGroup N] [Module R N] [Module.Finite R N] {I : Ideal R}
    (h_supp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I) {r : R} (hr : r ∈ I) :
    ∃ k, r ^ k ∈ Module.annihilator R N := by
  have h_rad := h_supp
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at h_rad
  exact h_rad hr

end Module

namespace IsSMulRegular

lemma subsingleton_ext_zero_of_mem_annihilator {M : ModuleCat.{v} R}
    (N : ModuleCat.{v} R) {r : R} (hr : IsSMulRegular M r)
    (h_ann : r ∈ Module.annihilator R N) : Subsingleton (Ext N M 0) := by
  have : Subsingleton (N →ₗ[R] M) := linearMap_subsingleton_of_mem_annihilator hr h_ann
  exact (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton

lemma subsingleton_ext_quotSMulTop_of_subsingleton_ext {M : ModuleCat.{v} R}
    (N : ModuleCat.{v} R) {r : R} (hr : IsSMulRegular M r) (i : ℕ)
    (h₀ : Subsingleton (Ext N M i)) (h₁ : Subsingleton (Ext N M (i + 1))) :
    Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop r M)) i) := by
  have zero₀ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₀
  have zero₁ := AddCommGrpCat.isZero_of_iff_subsingleton.mpr h₁
  exact AddCommGrpCat.subsingleton_of_isZero <| ShortComplex.Exact.isZero_of_both_zeros
    ((Ext.covariant_sequence_exact₃' N hr.smulShortComplex_shortExact) i (i + 1) rfl)
    (zero₀.eq_zero_of_src _) (zero₁.eq_zero_of_tgt _)

lemma subsingleton_ext_succ_of_subsingleton_ext_quotSMulTop_of_pow_mem_annihilator
    {M : ModuleCat.{v} R} (N : ModuleCat.{v} R) {r : R} (hr : IsSMulRegular M r) {k i : ℕ}
    (h_ann : r ^ k ∈ Module.annihilator R N)
    (h_quot : Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop r M)) i)) :
    Subsingleton (Ext N M (i + 1)) := by
  let g := AddCommGrpCat.ofHom ((Ext.mk₀ (M.smulShortComplex r).f).postcomp N
    (add_zero (i + 1)))
  have mono_g : Mono g := by
    apply (Ext.covariant_sequence_exact₁' N hr.smulShortComplex_shortExact i (i + 1) rfl).mono_g
      ((@AddCommGrpCat.isZero_of_subsingleton _ h_quot).eq_zero_of_src _)
  let gk := AddCommGrpCat.ofHom ((Ext.mk₀ (M.smulShortComplex (r ^ k)).f).postcomp N
    (add_zero (i + 1)))
  have mono_gk : Mono gk := by
    simp only [ModuleCat.smulShortComplex_f_eq_smul_id, g, gk] at mono_g ⊢
    exact (Ext.postcomp_smul_id_mono_iff (r ^ k) (i + 1)).mpr <|
      ((Ext.postcomp_smul_id_mono_iff r (i + 1)).mp mono_g).pow k
  have zero_gk : gk = 0 := Ext.postcomp_smul_id_eq_zero_of_mem_annihilator h_ann (i + 1)
  exact AddCommGrpCat.subsingleton_of_isZero (IsZero.of_mono_eq_zero _ zero_gk)

end IsSMulRegular

lemma ModuleCat.exists_mem_isSMulRegular_of_subsingleton_ext_zero_of_support_eq_zeroLocus
    [IsNoetherianRing R] (I : Ideal R) (M : ModuleCat.{v} R) [Module.Finite R M]
    (N : ModuleCat.{v} R) [Module.Finite R N]
    (h_supp : Module.support R N = PrimeSpectrum.zeroLocus I)
    (h_ext : Subsingleton (Ext N M 0)) : ∃ r ∈ I, IsSMulRegular M r := by
  have h_rad := h_supp
  rw [Module.support_eq_zeroLocus, PrimeSpectrum.zeroLocus_eq_iff] at h_rad
  have h_lin : Subsingleton (N →ₗ[R] M) :=
    (Ext.addEquiv₀.trans ModuleCat.homAddEquiv).subsingleton_congr.mp h_ext
  rcases subsingleton_linearMap_iff.mp h_lin with ⟨x, mem_ann, hx⟩
  rcases le_of_le_of_eq Ideal.le_radical h_rad mem_ann with ⟨k, hk⟩
  exact ⟨x ^ k, hk, hx.pow k⟩

lemma ModuleCat.exists_isRegular_of_exists_subsingleton_ext [IsNoetherianRing R] (I : Ideal R)
    (n : ℕ) (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (N : ModuleCat.{v} R) [Nontrivial N] [Module.Finite R N]
    (h_supp : Module.support R N = PrimeSpectrum.zeroLocus I)
    (h_ext : ∀ i < n, Subsingleton (Ext N M i)) :
    ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ IsRegular M rs := by
  induction n generalizing M with
  | zero =>
    have : Nontrivial M := (Submodule.nontrivial_iff R).mp (nontrivial_of_lt _ _ smul_lt)
    use []
    simp [isRegular_iff]
  | succ n ih =>
    -- use `Ext N M 0` vanishing to obtain an `M`-regular element of `I`
    rcases exists_mem_isSMulRegular_of_subsingleton_ext_zero_of_support_eq_zeroLocus I M N
      h_supp (h_ext 0 n.zero_lt_succ) with ⟨x, hxI, hx⟩
    -- prepare to apply induction hypothesis to `M ⧸ xM`
    have ne : I • (⊤ : Submodule R (QuotSMulTop x M)) ≠ ⊤ :=
      Ideal.smul_top_quotSMulTop_ne_top_of_smul_top_lt_top hxI smul_lt
    -- verify that `N` indeed make `M ⧸ xM` satisfy the induction hypothesis
    have h_ext' : ∀ i < n, Subsingleton (Ext N (ModuleCat.of R (QuotSMulTop x M)) i) :=
      fun i hi ↦ hx.subsingleton_ext_quotSMulTop_of_subsingleton_ext N i
        (h_ext i (by omega)) (h_ext (i + 1) (by omega))
    rcases ih (ModuleCat.of R (QuotSMulTop x M)) ne.lt_top h_ext' with ⟨rs, len, mem, reg⟩
    use x :: rs
    simpa [len, hxI] using ⟨mem, hx, reg⟩

lemma ModuleCat.subsingleton_ext_of_exists_isRegular [IsNoetherianRing R] (I : Ideal R)
    (N : ModuleCat.{v} R) [Nfin : Module.Finite R N]
    (Nsupp : Module.support R N ⊆ PrimeSpectrum.zeroLocus I)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤)
    (rs : List R) (mem : ∀ r ∈ rs, r ∈ I) (reg : IsRegular M rs) :
    ∀ i < rs.length, Subsingleton (Ext N M i) := by
  generalize len : rs.length = n
  induction n generalizing M rs with
  | zero => simp
  | succ n ih =>
    rintro i hi
    match rs with
    | [] => simp at len
    | a :: rs' =>
      -- find a positive power of `a` lying in `Ann(N)`
      rcases Module.exists_pow_mem_annihilator_of_mem_of_support_subset_zeroLocus Nsupp
        (mem a List.mem_cons_self) with ⟨k, hk⟩
      simp only [isRegular_cons_iff] at reg
      simp only [List.mem_cons, forall_eq_or_imp] at mem
      simp only [List.length_cons, Nat.add_left_inj] at len
      -- prepare to apply induction hypothesis to `M/aM`
      have ne : I • (⊤ : Submodule R (QuotSMulTop a M)) ≠ ⊤ :=
        Ideal.smul_top_quotSMulTop_ne_top_of_smul_top_lt_top mem.1 smul_lt
      match i with
      | 0 => -- vanishing of `Ext N M 0` follows from `aᵏ ∈ Ann(N)`
        exact (reg.1.pow k).subsingleton_ext_zero_of_mem_annihilator N hk
      | i + 1 =>
        -- scalar multiplication by `a` on `Ext N M (i + 1)` is injective by the long exact
        -- sequence, while scalar multiplication by `aᵏ` is zero because `aᵏ ∈ Ann(N)`.
        exact reg.1.subsingleton_ext_succ_of_subsingleton_ext_quotSMulTop_of_pow_mem_annihilator
          N hk (ih (ModuleCat.of R (QuotSMulTop a M)) ne.lt_top rs' mem.2 reg.2 len i
            (by omega))

/--
**The Rees theorem**
For any `n : ℕ`, Noetherian ring `R`, `I : Ideal R`, and finitely generated and nontrivial
`R`-module `M` satisfying `IM < M`, the following are equivalent:
· for any `N : ModuleCat R` finitely generated and nontrivial with support contained in the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
· `∀ i < n, Ext (A⧸I) M i = 0`
· there exists a `N : ModuleCat R` finitely generated and nontrivial with support equal to the
  zero locus of `I`, `∀ i < n, Ext N M i = 0`
· there exists a `M`-regular sequence of length `n` with every element in `I`
-/
lemma ModuleCat.exists_isRegular_tfae [IsNoetherianRing R] (I : Ideal R) (n : ℕ)
    (M : ModuleCat.{v} R) [Module.Finite R M] (smul_lt : I • (⊤ : Submodule R M) < ⊤) :
    [∀ N : ModuleCat.{v} R, Nontrivial N → Module.Finite R N →
      Module.support R N ⊆ PrimeSpectrum.zeroLocus I → ∀ i < n, Subsingleton (Ext N M i),
      ∀ i < n, Subsingleton (Ext (ModuleCat.of R (Shrink.{v} (R ⧸ I))) M i),
      ∃ N : ModuleCat R, Nontrivial N ∧ Module.Finite R N ∧
      Module.support R N = PrimeSpectrum.zeroLocus I ∧ ∀ i < n, Subsingleton (Ext N M i),
      ∃ rs : List R, rs.length = n ∧ (∀ r ∈ rs, r ∈ I) ∧ RingTheory.Sequence.IsRegular M rs
      ].TFAE := by
  -- two main implications `3 → 4` and `4 → 1` are separated out, the rest are trivial
  have ntrQ : Nontrivial (R ⧸ I) := by
    apply Submodule.Quotient.nontrivial_iff.mpr
    by_contra eq
    simp [eq] at smul_lt
  have suppQ : Module.support R (Shrink.{v} (R ⧸ I)) = PrimeSpectrum.zeroLocus I := by
    rw [(Shrink.linearEquiv R _).support_eq, Module.support_eq_zeroLocus, annihilator_quotient]
  tfae_have 1 → 2 := fun h1 i hi ↦ h1 (ModuleCat.of R (Shrink.{v} (R ⧸ I)))
    inferInstance inferInstance suppQ.subset i hi
  tfae_have 2 → 3 := fun h2 ↦ ⟨(ModuleCat.of R (Shrink.{v} (R ⧸ I))),
    inferInstance, Module.Finite.equiv (Shrink.linearEquiv R (R ⧸ I)).symm, suppQ, h2⟩
  tfae_have 3 → 4 := fun ⟨N, _, _, h_supp, h_ext⟩ ↦
    exists_isRegular_of_exists_subsingleton_ext I n M smul_lt N h_supp h_ext
  tfae_have 4 → 1 := fun ⟨rs, len, mem, reg⟩ N Nntr Nfin Nsupp i hi ↦
    subsingleton_ext_of_exists_isRegular I N Nsupp M smul_lt rs mem reg i (hi.trans_eq len.symm)
  tfae_finish
