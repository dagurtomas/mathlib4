module

public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.FieldDivision
public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Data.Multiset.DershowitzManna
public import Mathlib.Data.Sign.Basic
public import Mathlib.Data.List.OfFn
public import Mathlib.FieldTheory.IsRealClosed.Basic

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Field.Power
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.GroupTheory.Sylow
import Mathlib.RingTheory.Adjoin.PowerBasis
import Mathlib.Tactic.FieldSimp

/-!
# The Tarski--Seidenberg theorem

This file formalizes Theorem 1.4.2 in Chapter 1 of
Bochnak, Coste, and Roy, *Real Algebraic Geometry*.  The theorem eliminates one existentially
quantified variable from a finite system of sign conditions on integer polynomials, uniformly over
all real closed fields.

In `tarski_seidenberg`, the quantifier-free formula is chosen before the real closed field.  Thus
the same formula applies to every real closed field, as required by the theorem in the book.

The proof follows Section 1.4 of the book:

1. `rootSignTable` encodes the signs of a polynomial family at its roots and on the intervening
   intervals (Notation 1.4.3).
2. `hasSolution_iff_accepts_rootSignTable` is Lemma 1.4.4.
3. `reducedFamily` and `exists_reconstruction` isolate Lemma 1.4.5: the sign table of a family is
   reconstructed from derivatives and Euclidean remainders of smaller degree.
4. `signTable_preimage_definable` is Proposition 1.4.6.  Its proof uses well-founded
   induction on `Multiset.IsDershowitzMannaLT` applied to the multiset of degrees.  When a leading
   coefficient vanishes, the corresponding polynomial is truncated.  Otherwise pseudo-division
   (ordinary division followed by an even power of the leading coefficient) produces a smaller
   family without changing signs.

The intermediate-value property needed for the sign-table reconstruction is proved algebraically
for arbitrary real closed fields, without importing analytic continuity or the real-number mean
value theorem.
-/

@[expose] public section

open Polynomial

universe u v

set_option linter.style.longFile 6600

namespace TarskiSeidenberg

variable {n s m : ℕ}

/-- Integer polynomials in `n` variables. -/
abbrev IntPolynomial (n : ℕ) := MvPolynomial (Fin n) ℤ

/-- Integer polynomials in an eliminated variable `X₀` and parameter variables `X₁, ..., Xₙ`.

Under `MvPolynomial.finSuccEquiv`, variable `0` becomes the outer univariate variable and the
remaining variables become coefficients of that univariate polynomial.
-/
abbrev IntPolynomialWithParameter (n : ℕ) := MvPolynomial (Fin (n + 1)) ℤ

/-- Quantifier-free Boolean combinations of sign conditions on integer polynomials. -/
inductive Formula (n : ℕ) where
  | falsum
  | sign (p : IntPolynomial n) (s : SignType)
  | and (left right : Formula n)
  | or (left right : Formula n)
  | not (formula : Formula n)

namespace Formula

/-- Interpretation of a quantifier-free formula in an ordered commutative ring. -/
def Realize {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (y : Fin n → R) : Formula n → Prop
  | .falsum => False
  | .sign p s => SignType.sign (p.eval₂ (Int.castRingHom R) y) = s
  | .and left right => left.Realize y ∧ right.Realize y
  | .or left right => left.Realize y ∨ right.Realize y
  | .not formula => ¬formula.Realize y

end Formula

/-- Specialize the parameter variables of an integer polynomial, leaving variable `0`
univariate. -/
noncomputable def specialize {R : Type u} [CommRing R] (p : IntPolynomialWithParameter n)
    (y : Fin n → R) :
    R[X] :=
  (MvPolynomial.finSuccEquiv ℤ n p).map (MvPolynomial.eval₂Hom (Int.castRingHom R) y)

/-- Specialization followed by univariate evaluation agrees with direct multivariate evaluation. -/
theorem eval_specialize {R : Type u} [CommRing R] (p : IntPolynomialWithParameter n)
    (y : Fin n → R) (x : R) :
    (specialize p y).eval x = p.eval₂ (Int.castRingHom R) (Fin.cons x y) := by
  let lhs : IntPolynomialWithParameter n →+* R :=
    (Polynomial.evalRingHom x).comp
      ((Polynomial.mapRingHom (MvPolynomial.eval₂Hom (Int.castRingHom R) y)).comp
        (MvPolynomial.finSuccEquiv ℤ n).toRingHom)
  let rhs : IntPolynomialWithParameter n →+* R :=
    MvPolynomial.eval₂Hom (Int.castRingHom R) (Fin.cons x y)
  change lhs p = rhs p
  apply MvPolynomial.hom_eq_hom lhs rhs
  · ext a
    simp [lhs, rhs]
  · intro i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [show lhs (MvPolynomial.X 0) =
          (specialize (MvPolynomial.X 0) y).eval x by rfl,
        specialize, MvPolynomial.finSuccEquiv_X_zero]
      simp [rhs]
    · rw [show lhs (MvPolynomial.X j.succ) =
          (specialize (MvPolynomial.X j.succ) y).eval x by rfl,
        specialize, MvPolynomial.finSuccEquiv_X_succ]
      simp [rhs]

/-! ## Algebraic intermediate values -/

/-- The intermediate value property for univariate polynomials over an ordered field.

Unlike the topological intermediate value property, this statement makes sense for an arbitrary
ordered field.  Real closed fields satisfy it even when their order topology is disconnected.
-/
def PolynomialIntermediateValue (R : Type u) [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] : Prop :=
  ∀ (p : R[X]) {a b : R}, a < b → p.eval a * p.eval b < 0 →
    ∃ x ∈ Set.Ioo a b, p.IsRoot x

/-- A polynomial with no root in an interval has the same sign at every two points of that
interval, provided polynomials over the field have the intermediate value property. -/
theorem sign_eval_eq_of_no_root_between {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (intermediateValue : PolynomialIntermediateValue R) (p : R[X])
    {a b x y : R} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (noRoot : ∀ z ∈ Set.Ioo a b, ¬p.IsRoot z) :
    SignType.sign (p.eval x) = SignType.sign (p.eval y) := by
  have eval_ne_zero (z : R) (hz : z ∈ Set.Ioo a b) : p.eval z ≠ 0 := by
    simpa only [Polynomial.IsRoot] using noRoot z hz
  have not_opposite (z w : R) (hz : z ∈ Set.Ioo a b) (hw : w ∈ Set.Ioo a b)
      (hopposite : p.eval z * p.eval w < 0) : False := by
    rcases lt_trichotomy z w with hzw | rfl | hwz
    · obtain ⟨c, hcz, hroot⟩ := intermediateValue p hzw hopposite
      exact noRoot c ⟨hz.1.trans_le hcz.1.le, hcz.2.le.trans_lt hw.2⟩ hroot
    · exact (not_lt_of_ge (mul_self_nonneg _)) hopposite
    · obtain ⟨c, hcw, hroot⟩ := intermediateValue p hwz (by simpa [mul_comm] using hopposite)
      exact noRoot c ⟨hw.1.trans_le hcw.1.le, hcw.2.le.trans_lt hz.2⟩ hroot
  rcases lt_trichotomy (p.eval x) 0 with hxneg | hxzero | hxpos
  · rcases lt_trichotomy (p.eval y) 0 with hyneg | hyzero | hypos
    · rw [sign_neg hxneg, sign_neg hyneg]
    · exact ((eval_ne_zero y hy) hyzero).elim
    · exact (not_opposite x y hx hy (mul_neg_of_neg_of_pos hxneg hypos)).elim
  · exact ((eval_ne_zero x hx) hxzero).elim
  · rcases lt_trichotomy (p.eval y) 0 with hyneg | hyzero | hypos
    · exact (not_opposite x y hx hy (mul_neg_of_pos_of_neg hxpos hyneg)).elim
    · exact ((eval_ne_zero y hy) hyzero).elim
    · rw [sign_pos hxpos, sign_pos hypos]

/-! ### The quadratic extension by a square root of `-1` -/

/-- The algebraic analogue of adjoining `i` to a field. -/
abbrev Complexification (R : Type u) [Neg R] [One R] [Zero R] := QuadraticAlgebra R (-1) 0

/-- In a semireal field, `-1` is not a square. -/
theorem not_isSquare_neg_one {R : Type u} [Field R] [IsSemireal R] :
    ¬IsSquare (-1 : R) :=
  fun h ↦ IsSemireal.not_isSumSq_neg_one R h.isSumSq

/-- The complexification of a semireal field is a field. -/
noncomputable instance complexificationField {R : Type u} [Field R] [IsSemireal R] :
    Field (Complexification R) := by
  letI : Fact (¬IsSquare (-1 : R)) := ⟨not_isSquare_neg_one⟩
  letI : Fact (∀ r : R, r ^ 2 ≠ (-1 : R) + 0 * r) := inferInstance
  exact @QuadraticAlgebra.instField R _ (-1) 0 inferInstance

/-- Every element of the complexification of a real closed field is a square. -/
theorem complexification_isSquare {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] (z : Complexification R) : IsSquare z := by
  suffices ∃ w : Complexification R, w * w = z by
    obtain ⟨w, hw⟩ := this
    exact ⟨w, hw.symm⟩
  by_cases hb : z.im = 0
  · rcases le_total 0 z.re with ha | ha
    · obtain ⟨x, hx⟩ := IsRealClosed.exists_eq_pow_of_nonneg ha (n := 2) (by decide)
      refine ⟨⟨x, 0⟩, ?_⟩
      ext <;> simp [hb]
      nlinarith [hx]
    · have hna : 0 ≤ -z.re := neg_nonneg.mpr ha
      obtain ⟨y, hy⟩ := IsRealClosed.exists_eq_pow_of_nonneg hna (n := 2) (by decide)
      refine ⟨⟨0, y⟩, ?_⟩
      ext <;> simp [hb]
      nlinarith [hy]
  · have hs : 0 ≤ z.re ^ 2 + z.im ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    obtain ⟨r, hr⟩ := IsRealClosed.exists_eq_pow_of_nonneg hs (n := 2) (by decide)
    let r₀ := |r|
    have hr₀ : r₀ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      dsimp [r₀]
      rw [sq_abs, ← hr]
    have hr₀_nonneg : 0 ≤ r₀ := abs_nonneg r
    have hb_sq : 0 < z.im ^ 2 := sq_pos_of_ne_zero hb
    have hsum : 0 < r₀ + z.re := by nlinarith
    have ht : 0 ≤ (r₀ + z.re) / 2 := div_nonneg hsum.le (by norm_num)
    obtain ⟨x, hx⟩ := IsRealClosed.exists_eq_pow_of_nonneg ht (n := 2) (by decide)
    have hx_ne : x ≠ 0 := by
      intro hx0
      subst x
      simp at hx
      nlinarith
    let y := z.im / (2 * x)
    refine ⟨⟨x, y⟩, ?_⟩
    ext
    · simp only [QuadraticAlgebra.re_mul]
      dsimp [y]
      field_simp
      nlinarith [hr₀]
    · simp only [QuadraticAlgebra.im_mul]
      dsimp [y]
      field_simp
      ring

/-- The coefficient expansion of a polynomial of natural degree two. -/
theorem eq_quadratic_of_natDegree_eq_two {R : Type u} [Semiring R] {p : R[X]}
    (hp : p.natDegree = 2) :
    p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by
  ext k
  by_cases hk : k ≤ 2
  · have : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases this with rfl | rfl | rfl <;> simp
  · have hcoeff : p.coeff k = 0 := coeff_eq_zero_of_natDegree_lt (by omega)
    simp only [coeff_add, coeff_C_mul]
    rw [coeff_X_pow, ite_eq_right (by omega), coeff_X_of_ne_one (by omega),
      coeff_C_of_ne_zero (by omega)]
    simp [hcoeff]

/-- An irreducible quadratic over a real closed field has the same nonzero sign at every two
points. -/
theorem irreducible_quadratic_eval_mul_eval_pos {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] {p : R[X]} (hirr : Irreducible p)
    (hdeg : p.natDegree = 2) (x y : R) : 0 < p.eval x * p.eval y := by
  let a := p.coeff 2
  let b := p.coeff 1
  let c := p.coeff 0
  let D := discrim a b c
  have hp : p = C a * X ^ 2 + C b * X + C c := eq_quadratic_of_natDegree_eq_two hdeg
  have ha : a ≠ 0 := by
    rw [show a = p.leadingCoeff by simp [a, leadingCoeff, hdeg]]
    exact leadingCoeff_ne_zero.mpr hirr.ne_zero
  have hD : ¬IsSquare D := by
    rintro ⟨d, hd⟩
    obtain ⟨r, hr⟩ := exists_quadratic_eq_zero ha ⟨d, hd⟩
    apply hirr.not_isRoot_of_natDegree_ne_one (by omega : p.natDegree ≠ 1)
    rw [Polynomial.IsRoot, hp]
    simpa [pow_two] using hr
  have hD0 : D ≠ 0 := by
    intro h
    apply hD
    exact ⟨0, by simp [h]⟩
  obtain hDsq | hnegDsq := IsRealClosed.isSquare_or_isSquare_neg D
  · exact (hD hDsq).elim
  · obtain ⟨d, hd⟩ := hnegDsq
    have hd0 : d ≠ 0 := by
      intro hdzero
      subst d
      exact hD0 (by simpa only [zero_mul, neg_eq_zero] using hd)
    have heval (z : R) : 0 < a * p.eval z := by
      have hid : 4 * a * p.eval z = (2 * a * z + b) ^ 2 - D := by
        rw [hp]
        simp only [eval_add, eval_mul, eval_C, eval_X, eval_pow]
        dsimp [D]
        rw [discrim]
        ring
      nlinarith [sq_nonneg (2 * a * z + b), sq_pos_of_ne_zero hd0]
    have hmul : 0 < (a * a) * (p.eval x * p.eval y) := by
      calc
        0 < (a * p.eval x) * (a * p.eval y) := mul_pos (heval x) (heval y)
        _ = (a * a) * (p.eval x * p.eval y) := by ring
    exact (mul_pos_iff_of_pos_left (mul_self_pos.mpr ha)).mp hmul

/-! ### Algebraic extensions of a real closed field

The following proof is adapted from Artie Khovanov's `real_closed_field` development.  Current
Mathlib's quadratic-algebra API lets us avoid porting its custom primitive-element layer: a
quadratic extension is put directly into the form `R[i]` by completing the square in a minimal
polynomial.
-/

private theorem quadraticExtension_generator_data
    {F K : Type u} [Field F] [Field K] [Algebra F K]
    [Algebra.IsQuadraticExtension F K] :
    ∃ s : K, s ∉ (⊥ : Subalgebra F K) ∧ Algebra.adjoin F {s} = ⊤ ∧
      (minpoly F s).natDegree = 2 := by
  have hbot : (⊥ : Subalgebra F K) ≠ ⊤ := by
    intro h
    have hfinrank := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp h
    rw [Algebra.IsQuadraticExtension.finrank_eq_two F K] at hfinrank
    omega
  obtain ⟨s, hs⟩ := SetLike.exists_not_mem_of_ne_top ⊥ hbot
  have hgen : Algebra.adjoin F {s} = ⊤ := by
    rcases (Subalgebra.isSimpleOrder_of_finrank_prime F K (by
      simpa [Algebra.IsQuadraticExtension.finrank_eq_two F K] using Nat.prime_two)).eq_bot_or_eq_top
        (Algebra.adjoin F {s}) with h | h
    · exact (hs (by rw [← h]; exact Algebra.subset_adjoin (Set.mem_singleton s))).elim
    · exact h
  refine ⟨s, hs, hgen, ?_⟩
  let pb := PowerBasis.ofAdjoinEqTop (IsIntegral.of_finite F s) hgen
  calc
    (minpoly F s).natDegree = pb.dim := rfl
    _ = Module.finrank F K := (PowerBasis.finrank pb).symm
    _ = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F K

private theorem quadraticExtension_discriminant_not_isSquare
    {F K : Type u} [Field F] [CharZero F] [Field K] [Algebra F K]
    [Algebra.IsQuadraticExtension F K] :
    ∃ s : K, ∃ b D : F, Algebra.adjoin F {s} = ⊤ ∧
      (2 * s + algebraMap F K b) ^ 2 = algebraMap F K D ∧ ¬IsSquare D := by
  let : CharZero K := by
    simp [← Algebra.ringChar_eq F K, ← CharP.ringChar_zero_iff_CharZero]
  obtain ⟨s, hs, hgen, hdeg⟩ := quadraticExtension_generator_data (F := F) (K := K)
  let b := (minpoly F s).coeff 1
  let c := (minpoly F s).coeff 0
  let D := b ^ 2 - 4 * c
  have hc2 : (minpoly F s).coeff 2 = 1 := by
    rw [← hdeg]
    exact (minpoly.monic (IsIntegral.of_finite F s)).coeff_natDegree
  have hp : minpoly F s = X ^ 2 + C b * X + C c := by
    rw [eq_quadratic_of_natDegree_eq_two hdeg]
    simp [b, c, hc2]
  have hsroot : s ^ 2 + algebraMap F K b * s + algebraMap F K c = 0 := by
    have := minpoly.aeval F s
    rw [hp] at this
    simpa [pow_two] using this
  have hsquare : (2 * s + algebraMap F K b) ^ 2 = algebraMap F K D := by
    dsimp [D]
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    linear_combination 4 * hsroot
  refine ⟨s, b, D, hgen, hsquare, ?_⟩
  rintro ⟨d, hd⟩
  have hsq : (2 * s + algebraMap F K b) ^ 2 = (algebraMap F K d) ^ 2 := by
    rw [hsquare, hd]
    simp [pow_two]
  rcases eq_or_eq_neg_of_sq_eq_sq _ _ hsq with h | h
  · have hsbase : s = algebraMap F K ((d - b) / 2) := by
      simp only [map_div₀, map_sub, map_ofNat]
      apply (eq_div_iff (show (2 : K) ≠ 0 by norm_num)).2
      linear_combination h
    exact hs (hsbase.symm ▸ (⊥ : Subalgebra F K).algebraMap_mem _)
  · have hsbase : s = algebraMap F K ((-d - b) / 2) := by
      simp only [map_div₀, map_sub, map_neg, map_ofNat]
      apply (eq_div_iff (show (2 : K) ≠ 0 by norm_num)).2
      linear_combination h
    exact hs (hsbase.symm ▸ (⊥ : Subalgebra F K).algebraMap_mem _)

private theorem nonempty_complexificationEquivOfQuadraticExtension
    {R K : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [Algebra R K] [Algebra.IsQuadraticExtension R K] :
    Nonempty (Complexification R ≃ₐ[R] K) := by
  let : CharZero K := by
    simp [← Algebra.ringChar_eq R K, ← CharP.ringChar_zero_iff_CharZero]
  obtain ⟨s, b, D, hgen, hsquare, hD⟩ :=
    quadraticExtension_discriminant_not_isSquare (F := R) (K := K)
  obtain hDsquare | hnegDsquare := IsRealClosed.isSquare_or_isSquare_neg D
  · exact (hD hDsquare).elim
  obtain ⟨r, hr⟩ := hnegDsquare
  have hr0 : r ≠ 0 := by
    intro hrzero
    subst r
    simp only [mul_zero, neg_eq_zero] at hr
    exact hD ⟨0, by simp [hr]⟩
  let u : K := (2 * s + algebraMap R K b) / algebraMap R K r
  have hu : u * u = algebraMap R K (-1 : R) := by
    have hrmap := congrArg (algebraMap R K) hr
    dsimp [u]
    field_simp [hr0]
    rw [hsquare]
    simp only [map_neg, map_mul, map_one, pow_two] at hrmap ⊢
    linear_combination -hrmap
  have hu' : u * u = (-1 : R) • (1 : K) + (0 : R) • u := by
    simpa [Algebra.algebraMap_eq_smul_one] using hu
  let f : Complexification R →ₐ[R] K := QuadraticAlgebra.lift ⟨u, hu'⟩
  have hs_u : s = (algebraMap R K r * u - algebraMap R K b) / 2 := by
    dsimp [u]
    field_simp [hr0]
    ring
  have hu_gen : Algebra.adjoin R {u} = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen]
    apply Algebra.adjoin_le
    rw [Set.singleton_subset_iff]
    rw [hs_u]
    rw [div_eq_mul_inv,
      show (2 : K)⁻¹ = algebraMap R K (2 : R)⁻¹ by rw [map_inv₀, map_ofNat]]
    exact (Algebra.adjoin R {u}).mul_mem
      ((Algebra.adjoin R {u}).sub_mem
        ((Algebra.adjoin R {u}).mul_mem
          ((Algebra.adjoin R {u}).algebraMap_mem r)
          (Algebra.subset_adjoin (Set.mem_singleton u)))
        ((Algebra.adjoin R {u}).algebraMap_mem b))
      ((Algebra.adjoin R {u}).algebraMap_mem (2 : R)⁻¹)
  refine ⟨AlgEquiv.ofBijective f ⟨f.injective, ?_⟩⟩
  exact (QuadraticAlgebra.lift_surjective_iff hu').2 hu_gen

private noncomputable def complexificationEquivOfQuadraticExtension
    {R K : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [Algebra R K] [Algebra.IsQuadraticExtension R K] :
    Complexification R ≃ₐ[R] K :=
  Classical.choice (nonempty_complexificationEquivOfQuadraticExtension (R := R) (K := K))

private theorem quadraticExtension_isSquare
    {R K : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [Algebra R K] [Algebra.IsQuadraticExtension R K] (z : K) : IsSquare z := by
  let e := complexificationEquivOfQuadraticExtension (R := R) (K := K)
  obtain ⟨w, hw⟩ := complexification_isSquare (e.symm z)
  refine ⟨e w, ?_⟩
  rw [← map_mul]
  exact (e.apply_symm_apply z).symm.trans (congrArg e hw)

private theorem finrank_div_finrank
    (F K A : Type*) [Semiring F] [Ring K] [AddCommGroup A]
    [Module F K] [Module K A] [Module F A] [IsScalarTower F K A] [Nontrivial A]
    [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]
    [Module.Finite K A] [NoZeroSMulDivisors K A] :
    Module.finrank F K = Module.finrank F A / Module.finrank K A :=
  Nat.eq_div_of_mul_eq_left ((Module.finrank_pos_iff_of_free ..).mpr inferInstance).ne'
    (Module.finrank_mul_finrank ..)

private theorem finrank_div_finrank_left
    (F K A : Type*) [Ring F] [Ring K] [AddCommMonoid A]
    [Module F K] [Module K A] [Module F A] [IsScalarTower F K A] [Nontrivial K]
    [StrongRankCondition F] [StrongRankCondition K] [Module.Free F K] [Module.Free K A]
    [Module.Finite F K] [NoZeroSMulDivisors F K] :
    Module.finrank K A = Module.finrank F A / Module.finrank F K :=
  Nat.eq_div_of_mul_eq_right ((Module.finrank_pos_iff_of_free ..).mpr inferInstance).ne'
    (Module.finrank_mul_finrank ..)

private theorem exists_intermediateField_of_pow_prime_dvd
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p n : ℕ} (hp : Nat.Prime p) (hn : p ^ n ∣ Module.finrank K L) :
    ∃ M : IntermediateField K L, Module.finrank M L = p ^ n := by
  let := Fact.mk hp
  rw [← IsGalois.card_aut_eq_finrank K L] at hn
  obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime p hn
  exact ⟨IntermediateField.fixedField H, by
    simpa [IntermediateField.finrank_fixedField_eq_card] using hH⟩

private theorem exists_intermediateField_of_card_pow_prime_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p n a : ℕ} (hp : Nat.Prime p) (hn : Module.finrank K L = p ^ n * a)
    {m : ℕ} (hm : m ≤ n) :
    ∃ M : IntermediateField K L, Module.finrank K M = p ^ m * a := by
  obtain ⟨M, hM⟩ := exists_intermediateField_of_pow_prime_dvd hp
    (by rw [hn]; exact Nat.pow_dvd_of_le_of_pow_dvd (by omega : n - m ≤ n) (by simp))
  refine ⟨M, ?_⟩
  have hdiv := finrank_div_finrank K M L
  rw [hn, hM, ← Nat.pow_sub_mul_pow _ hm, mul_assoc,
    Nat.mul_div_right _ (by positivity [hp.pos])] at hdiv
  exact hdiv

private theorem exists_subgroup_le_card_pow_prime_of_card_pow_prime
    {G : Type*} [Group G] {m n p : ℕ} (hp : Nat.Prime p)
    {H : Subgroup G} (hH : Nat.card H = p ^ n) (hm : m ≤ n) :
    ∃ H' ≤ H, Nat.card H' = p ^ m := by
  have hle : p ^ m ≤ Nat.card H := by
    rw [hH]
    gcongr
    exact Nat.Prime.one_le hp
  obtain ⟨H', hH'⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card hp (IsPGroup.of_card hH) hle
  refine ⟨H'.map H.subtype, Subgroup.map_subtype_le .., ?_⟩
  rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective H)]
  exact hH'

private theorem exists_intermediateField_ge_card_pow_prime_of_card_pow_prime
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {m n p : ℕ} (hp : Nat.Prime p) {M : IntermediateField K L}
    (hM : Module.finrank M L = p ^ n) (hm : m ≤ n) :
    ∃ N ≥ M, Module.finrank N L = p ^ m := by
  obtain ⟨H', hH'le, hH'card⟩ := exists_subgroup_le_card_pow_prime_of_card_pow_prime
    (H := M.fixingSubgroup) hp
    (by rw [IsGalois.card_fixingSubgroup_eq_finrank, hM]) hm
  exact ⟨IntermediateField.fixedField H',
    by simpa [IntermediateField.le_iff_le] using hH'le,
    by simpa [IntermediateField.finrank_fixedField_eq_card] using hH'card⟩

private theorem exists_intermediateField_ge_card_pow_prime_mul_of_card_pow_prime_mul
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {p n a : ℕ} (hp : Nat.Prime p) (hL : Module.finrank K L = p ^ n * a)
    {m m' : ℕ} {M : IntermediateField K L} (hM : Module.finrank K M = p ^ m * a)
    (hm'le : m ≤ m') (hm' : m' ≤ n) :
    ∃ N ≥ M, Module.finrank K N = p ^ m' * a := by
  by_cases ha : a = 0
  · exact ⟨M, le_rfl, by simpa [ha] using hM⟩
  have hML : Module.finrank M L = p ^ (n - m) := by
    have hdiv := finrank_div_finrank_left K M L
    rw [hM, hL, ← Nat.pow_sub_mul_pow _ (by omega : m ≤ n), mul_assoc,
      Nat.mul_div_left _ (by positivity [hp.pos])] at hdiv
    exact hdiv
  obtain ⟨N, hMN, hNrank⟩ := exists_intermediateField_ge_card_pow_prime_of_card_pow_prime
    hp (M := M) (n := n - m) (m := n - m') hML (by omega)
  refine ⟨N, hMN, ?_⟩
  have hdiv := finrank_div_finrank K N L
  rw [hL, hNrank, ← Nat.pow_sub_mul_pow _ hm', mul_assoc,
    Nat.mul_div_right _ (by positivity [hp.pos])] at hdiv
  exact hdiv

private theorem odd_finrank_extension
    {R K : Type u} [Field R] [IsRealClosed R] [Field K] [Algebra R K]
    [FiniteDimensional R K] (hodd : Odd (Module.finrank R K)) :
    Module.finrank R K = 1 := by
  let : Algebra.IsSeparable R K := inferInstance
  obtain ⟨a, ha⟩ := Field.exists_primitive_element R K
  have hdeg : (minpoly R a).natDegree = Module.finrank R K :=
    (Field.primitive_element_iff_minpoly_natDegree_eq R a).mp ha
  obtain ⟨r, hr⟩ := IsRealClosed.exists_isRoot_of_odd_natDegree
    (f := minpoly R a) (hdeg.symm ▸ hodd)
  have hdegree : (minpoly R a).degree = 1 :=
    degree_eq_one_of_irreducible_of_root
      (minpoly.irreducible (IsIntegral.of_finite R a)) hr
  have hnatDegree : (minpoly R a).natDegree = 1 :=
    natDegree_eq_of_degree_eq_some hdegree
  exact hdeg.symm.trans hnatDegree

private theorem finite_extension_rank_le
    (R K : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    [Field K] [Algebra R K] [FiniteDimensional R K] : Module.finrank R K ≤ 2 := by
  wlog hGalois : IsGalois R K generalizing K
  · have hclosure :=
      this (IntermediateField.normalClosure R K (AlgebraicClosure K)) inferInstance
    have hrank := Module.finrank_bot_le_finrank_of_isScalarTower
      R K (IntermediateField.normalClosure R K (AlgebraicClosure K))
    have hpos := Module.finrank_pos (R := R) (M := K)
    omega
  obtain ⟨k, a, ha, hka⟩ :=
    Nat.exists_eq_two_pow_mul_odd (n := Module.finrank R K) Module.finrank_pos.ne'
  have ha_one : a = 1 := by
    obtain ⟨M, hM⟩ := exists_intermediateField_of_card_pow_prime_mul
      Nat.prime_two hka (by simp : 0 ≤ k)
    have hoddM : Odd (Module.finrank R M) := by simpa [hM] using ha
    have := odd_finrank_extension (R := R) (K := M) hoddM
    simpa [hM] using this
  suffices k ≤ 1 by
    interval_cases k <;> simp_all
  by_contra! hk
  obtain ⟨M, hM⟩ := exists_intermediateField_of_card_pow_prime_mul
    Nat.prime_two hka (by omega : 1 ≤ k)
  obtain ⟨N, hMN, hN⟩ :=
    exists_intermediateField_ge_card_pow_prime_mul_of_card_pow_prime_mul
      Nat.prime_two hka hM (by omega : 1 ≤ 2) (by omega)
  rw [ge_iff_le] at hMN
  let : Algebra.IsQuadraticExtension R M := ⟨by omega⟩
  algebraize [(IntermediateField.inclusion hMN).toRingHom]
  let := IsScalarTower.of_algebraMap_eq'
    (IntermediateField.inclusion hMN).comp_algebraMap.symm
  let := Module.Finite.of_restrictScalars_finite R M N
  have hMNrank : Module.finrank M N = 2 := by
    rw [finrank_div_finrank_left R M N, hM, hN, ha_one]
    norm_num
  let : Algebra.IsQuadraticExtension M N := ⟨hMNrank⟩
  let : CharZero M := by
    simp [← Algebra.ringChar_eq R M, ← CharP.ringChar_zero_iff_CharZero]
  obtain ⟨_, _, D, _, _, hD⟩ :=
    quadraticExtension_discriminant_not_isSquare (F := M) (K := N)
  exact hD (quadraticExtension_isSquare (R := R) (K := M) D)

private theorem irreducible_natDegree_le_two
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {p : R[X]} (hp : Irreducible p) : p.natDegree ≤ 2 := by
  let q := normalize p
  have hq0 : q ≠ 0 := by simp [q, hp.ne_zero]
  have hqmonic : q.Monic := by simpa [q] using Polynomial.monic_normalize hp.ne_zero
  have hqirreducible : Irreducible q := by
    exact (Associated.irreducible_iff (normalize_associated p)).mpr hp
  let : Fact (Irreducible q) := ⟨hqirreducible⟩
  let : Module.Finite R (AdjoinRoot q) := hqmonic.finite_adjoinRoot
  have hle := finite_extension_rank_le R (AdjoinRoot q)
  rw [PowerBasis.finrank (AdjoinRoot.powerBasis' hqmonic)] at hle
  simpa [q] using hle

/-- The intermediate value theorem for polynomials over an arbitrary real closed field. -/
theorem intermediate_value_property
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {f : R[X]} {x y : R} (hle : x ≤ y) (hx : 0 ≤ f.eval x) (hy : f.eval y ≤ 0) :
    ∃ z ∈ Set.Icc x y, f.eval z = 0 := by
  induction hdegree : f.natDegree using Nat.strong_induction_on generalizing f with
  | h n ih =>
    subst hdegree
    by_cases hzero : f.natDegree = 0
    · rw [f.eq_C_of_natDegree_eq_zero hzero] at hx hy ⊢
      refine ⟨x, ⟨le_rfl, hle⟩, ?_⟩
      have hc : f.coeff 0 = 0 :=
        le_antisymm (by simpa only [eval_C] using hy) (by simpa only [eval_C] using hx)
      simp only [eval_C, hc]
    have hpos := Nat.pos_of_ne_zero hzero
    by_cases hdiv : ∃ g : R[X], g.natDegree > 0 ∧ g ∣ f ∧ 0 < g.eval y ∧ 0 < g.eval x
    · obtain ⟨g, hgdegree, ⟨k, rfl⟩, hgy, hgx⟩ := hdiv
      rw [Polynomial.natDegree_mul
        (show g ≠ 0 from fun hg ↦ by simp_all)
        (show k ≠ 0 from fun hk ↦ by simp_all)] at ih
      rw [eval_mul] at hx hy
      obtain ⟨z, hzmem, hzeval⟩ :=
        ih k.natDegree (by simp_all) (by nlinarith) (by nlinarith) rfl
      exact ⟨z, hzmem, Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero (by simp) hzeval⟩
    · push Not at hdiv
      obtain ⟨g, hgmonic, hgirreducible, hgdvd⟩ :=
        Polynomial.exists_monic_irreducible_factor f (f.not_isUnit_of_natDegree_pos hpos)
      have hgdegree_le := irreducible_natDegree_le_two hgirreducible
      have hgdegree_pos := hgirreducible.natDegree_pos
      have hgdegree : g.natDegree = 1 ∨ g.natDegree = 2 := by omega
      rcases hgdegree with hglinear | hgquadratic
      · rw [hgmonic.eq_X_add_C hglinear] at hgirreducible hgdvd hgmonic
        by_cases hroot_lt_y : -g.coeff 0 < y
        · have hnot := hdiv _ (by simp) hgdvd
          simp only [eval_add, eval_C, eval_X] at hnot
          have := hnot (by linarith)
          refine ⟨-g.coeff 0, ?_, ?_⟩
          · exact ⟨by linarith, by linarith⟩
          · exact Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hgdvd (by simp)
        · by_cases hy_lt_root : y < -g.coeff 0
          · have hnot := hdiv (-(X + C (g.coeff 0)))
              (by rw [Polynomial.natDegree_neg]; simp)
              hgdvd.neg_left
            simp only [eval_add, eval_neg, eval_C, eval_X] at hnot
            linarith [hnot (by linarith)]
          · have hyroot : y = -g.coeff 0 := by linarith
            subst y
            exact ⟨-g.coeff 0, by simp [hle],
              Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hgdvd (by simp)⟩
      · have hsame := irreducible_quadratic_eval_mul_eval_pos
            hgirreducible hgquadratic x y
        rcases (mul_pos_iff.mp hsame) with ⟨hxpos, hypos⟩ | ⟨hxneg, hyneg⟩
        · have hnot := hdiv g hgdegree_pos hgdvd hypos
          linarith
        · have hnot := hdiv (-g) (by simpa) (by simpa [neg_dvd] using hgdvd)
          simp only [eval_neg, neg_pos] at hnot
          linarith [hnot hyneg]

/-- The open-interval form of polynomial IVT used by the sign-table construction. -/
theorem polynomialIntermediateValue
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    PolynomialIntermediateValue R := by
  intro p a b hab hsign
  rcases (mul_neg_iff.mp hsign) with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · obtain ⟨z, hz, hroot⟩ := intermediate_value_property
      (f := p) hab.le ha.le hb.le
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · exact lt_of_le_of_ne hz.1 (by rintro rfl; simp_all)
    · exact lt_of_le_of_ne hz.2 (by rintro rfl; simp_all)
    · simpa [Polynomial.IsRoot] using hroot
  · obtain ⟨z, hz, hroot⟩ := intermediate_value_property
      (f := -p) hab.le (by simpa using ha.le) (by simpa using hb.le)
    refine ⟨z, ⟨?_, ?_⟩, ?_⟩
    · exact lt_of_le_of_ne hz.1 (by rintro rfl; simp_all)
    · exact lt_of_le_of_ne hz.2 (by rintro rfl; simp_all)
    · simpa [Polynomial.IsRoot] using hroot

private lemma derivative_two_root_factors
    {R : Type u} [Field R] (a b : R) (Q : R[X]) (m n : ℕ) :
    derivative ((X - C a) ^ (m + 1) * ((X - C b) ^ (n + 1) * Q)) =
      (X - C a) ^ m * (X - C b) ^ n *
        (C ((n + 1 : ℕ) : R) * (X - C a) * Q +
          C ((m + 1 : ℕ) : R) * (X - C b) * Q +
          (X - C a) * (X - C b) * derivative Q) := by
  simp only [derivative_mul, derivative_pow, derivative_X_sub_C, mul_one,
    Nat.add_sub_cancel]
  have hpa : (X - C a) ^ (m + 1) = (X - C a) ^ m * (X - C a) := pow_succ _ _
  have hpb : (X - C b) ^ (n + 1) = (X - C b) ^ n * (X - C b) := pow_succ _ _
  rw [hpa, hpb]
  simp only [Nat.cast_add, Nat.cast_one, C_add, C_1]
  ring

private lemma polynomialRolle_weak
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R} (hab : a < b) {P : R[X]}
    (hP : ∀ x ∈ Set.Ioo a b, P.eval x ≠ 0) (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Set.Ioo a b, P.derivative.eval c = 0 := by
  have hPnz : P ≠ 0 := by
    intro h
    obtain ⟨x, hx⟩ := exists_between hab
    exact hP x hx (by simp [h])
  obtain ⟨Q', hQ'1, hQ'2⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd P hPnz a
  have hQnz : Q' ≠ 0 := by
    intro h
    rw [h, mul_zero] at hQ'1
    exact hPnz hQ'1
  obtain ⟨Q, hQ1, hQ2⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd Q' hQnz b
  have ham : P.rootMultiplicity a ≠ 0 := by
    rw [← pos_iff_ne_zero]
    exact (Polynomial.rootMultiplicity_pos hPnz).2 hPa
  have hbm : Q'.rootMultiplicity b ≠ 0 := by
    rw [← pos_iff_ne_zero]
    refine (Polynomial.rootMultiplicity_pos hQnz).2 ?_
    rw [hQ'1, eval_mul] at hPb
    have hfactor : ((X - C a) ^ P.rootMultiplicity a).eval b ≠ 0 := by
      simpa only [eval_pow, eval_sub, eval_X, eval_C] using
        pow_ne_zero (P.rootMultiplicity a) (sub_ne_zero.mpr (ne_of_gt hab))
    exact (mul_eq_zero.mp hPb).resolve_left
      hfactor
  rw [hQ1] at hQ'1
  obtain ⟨ma, hma⟩ := Nat.exists_eq_succ_of_ne_zero ham
  obtain ⟨mb, hmb⟩ := Nat.exists_eq_succ_of_ne_zero hbm
  have hQr : Q.eval a ≠ 0 ∧ Q.eval b ≠ 0 := by
    constructor
    · intro h
      apply hQ'2
      rw [Polynomial.dvd_iff_isRoot, hQ1]
      simp [h]
    · rwa [Polynomial.dvd_iff_isRoot] at hQ2
  set Q1 : R[X] :=
    C (Q'.rootMultiplicity b : R) * (X - C a) * Q +
      C (P.rootMultiplicity a : R) * (X - C b) * Q +
        (X - C a) * (X - C b) * Q.derivative with hQd
  have hderiv : P.derivative =
      ((X - C a) ^ (P.rootMultiplicity a).pred) *
        ((X - C b) ^ (Q'.rootMultiplicity b).pred) * Q1 := by
    rw [hma, hmb] at hQ'1 hQd ⊢
    simp only [Nat.pred_succ]
    rw [hQ'1, derivative_two_root_factors, hQd]
  have hQ1a : Q1.eval a = -(P.rootMultiplicity a : R) * (b - a) * Q.eval a := by
    rw [hQd]
    simp
    ring
  have hQ1b : Q1.eval b = (Q'.rootMultiplicity b : R) * (b - a) * Q.eval b := by
    rw [hQd]
    simp
  have hQIoo : ∀ x ∈ Set.Ioo a b, Q.eval x ≠ 0 := by
    intro x hx hQx
    apply hP x hx
    rw [hQ'1]
    simp [hQx]
  have hQprod : 0 < Q.eval a * Q.eval b := by
    have hne : Q.eval a * Q.eval b ≠ 0 := mul_ne_zero hQr.1 hQr.2
    refine lt_of_le_of_ne ?_ (Ne.symm hne)
    by_contra! hneg
    obtain ⟨c, hc, hroot⟩ := polynomialIntermediateValue Q hab hneg
    exact hQIoo c hc (by simpa [Polynomial.IsRoot] using hroot)
  have hQ1prod : Q1.eval a * Q1.eval b < 0 := by
    rw [hQ1a, hQ1b]
    have hma : (0 : R) < P.rootMultiplicity a := by exact_mod_cast Nat.pos_of_ne_zero ham
    have hmb : (0 : R) < Q'.rootMultiplicity b := by exact_mod_cast Nat.pos_of_ne_zero hbm
    have hba : 0 < b - a := sub_pos.mpr hab
    calc
      -(P.rootMultiplicity a : R) * (b - a) * Q.eval a *
          ((Q'.rootMultiplicity b : R) * (b - a) * Q.eval b) =
        -((P.rootMultiplicity a : R) * (Q'.rootMultiplicity b : R) *
          (b - a) * (b - a) * (Q.eval a * Q.eval b)) := by ring
      _ < 0 := neg_lt_zero.mpr (by positivity)
  obtain ⟨c, hc, hQ1c⟩ := polynomialIntermediateValue Q1 hab hQ1prod
  refine ⟨c, hc, ?_⟩
  rw [hderiv]
  have hQ1eval : Q1.eval c = 0 := by simpa [Polynomial.IsRoot] using hQ1c
  simp [hQ1eval]

private lemma polynomialRolle_weak'
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R} (hab : a < b) {P : R[X]} (hPa : P.eval a = 0) (hPb : P.eval b = 0) :
    ∃ c ∈ Set.Ioo a b, P.derivative.eval c = 0 ∨ P.eval c = 0 := by
  by_contra! hcc
  have hP : ∀ x ∈ Set.Ioo a b, P.eval x ≠ 0 := fun x hx => (hcc x hx).2
  obtain ⟨c, hc, hcd⟩ := polynomialRolle_weak hab hP hPa hPb
  exact (hcc c hc).1 hcd

private lemma polynomialRolle_induction
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (n : ℕ) {a b : R} {P : R[X]} (hab : a < b) (hPa : P.eval a = 0)
    (hPb : P.eval b = 0)
    (hcard : (P.roots.toFinset.filter fun x => x ∈ Set.Ioo a b).card < n) :
    ∃ c ∈ Set.Ioo a b, P.derivative.eval c = 0 := by
  revert P a b
  induction n with
  | zero => simp
  | succ n ih =>
      intro a b P hab hPa hPb hcard
      obtain ⟨c, hc, hcd | hPc⟩ := polynomialRolle_weak' hab hPa hPb
      · exact ⟨c, hc, hcd⟩
      · have hsubset : P ≠ 0 →
            (P.roots.toFinset.filter fun x => x ∈ Set.Ioo a c) ⊂
              (P.roots.toFinset.filter fun x => x ∈ Set.Ioo a b) := by
          intro hPz
          rw [Finset.ssubset_def, Finset.not_subset]
          constructor
          · intro r hr
            simp only [Finset.mem_filter] at hr ⊢
            exact ⟨hr.1, hr.2.1, hr.2.2.trans hc.2⟩
          · refine ⟨c, ?_, ?_⟩
            · simp only [Finset.mem_filter]
              exact ⟨by simpa using (Polynomial.mem_roots hPz).2 hPc, hc⟩
            · simp
        by_cases hPz : P = 0
        · exact ⟨(a + b) / 2, by constructor <;> linarith, by simp [hPz]⟩
        · obtain ⟨r, hr, hrd⟩ := ih hc.1 hPa hPc
            (lt_of_lt_of_le (Finset.card_lt_card (hsubset hPz))
              (Nat.lt_succ_iff.mp hcard))
          exact ⟨r, ⟨hr.1, hr.2.trans hc.2⟩, hrd⟩

/-- Rolle's theorem for polynomials over an arbitrary real closed field. -/
theorem polynomialRolle
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R} {P : R[X]} (hab : a < b) (hPab : P.eval a = P.eval b) :
    ∃ c ∈ Set.Ioo a b, P.derivative.eval c = 0 := by
  by_cases hzero : P.eval a = 0
  · exact polynomialRolle_induction
      ((P.roots.toFinset.filter fun x => x ∈ Set.Ioo a b).card + 1)
      hab hzero (hPab ▸ hzero) (Nat.lt_succ_self _)
  · let Q := P - C (P.eval a)
    obtain ⟨c, hc, hQc⟩ := polynomialRolle_induction
      ((Q.roots.toFinset.filter fun x => x ∈ Set.Ioo a b).card + 1)
      hab (by simp [Q]) (by simp [Q, hPab]) (Nat.lt_succ_self _)
    exact ⟨c, hc, by simpa [Q] using hQc⟩

/-- The mean value theorem for polynomials over an arbitrary real closed field. -/
theorem polynomialMeanValue
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R} {P : R[X]} (hab : a < b) :
    ∃ c ∈ Set.Ioo a b,
      P.eval b - P.eval a = P.derivative.eval c * (b - a) := by
  let Q : R[X] :=
    (C (P.eval b) - C (P.eval a)) * (X - C a) -
      (C b - C a) * (P - C (P.eval a))
  have hQderiv : Q.derivative =
      (C (P.eval b) - C (P.eval a)) - (C b - C a) * P.derivative := by
    simp [Q]
  have hQa : Q.eval a = 0 := by simp [Q]
  have hQb : Q.eval b = 0 := by simp [Q]; ring
  obtain ⟨c, hc, hQc⟩ := polynomialRolle (P := Q) hab (hQa.trans hQb.symm)
  refine ⟨c, hc, ?_⟩
  rw [hQderiv] at hQc
  simp only [eval_sub, eval_C, eval_mul] at hQc
  linarith

/-- A polynomial is strictly increasing on an interval where its derivative is positive. -/
theorem eval_lt_eval_of_derivative_pos_on
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b x y : R} {P : R[X]} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hxy : x < y) (hderiv : ∀ z ∈ Set.Ioo a b, 0 < P.derivative.eval z) :
    P.eval x < P.eval y := by
  obtain ⟨c, hc, hmean⟩ := polynomialMeanValue (P := P) hxy
  have hc' : c ∈ Set.Ioo a b := ⟨hx.1.trans_lt hc.1, hc.2.trans_le hy.2⟩
  have hpos : 0 < P.derivative.eval c * (y - x) :=
    mul_pos (hderiv c hc') (sub_pos.mpr hxy)
  linarith

/-- A polynomial is strictly decreasing on an interval where its derivative is negative. -/
theorem eval_lt_eval_of_derivative_neg_on
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b x y : R} {P : R[X]} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b)
    (hxy : x < y) (hderiv : ∀ z ∈ Set.Ioo a b, P.derivative.eval z < 0) :
    P.eval y < P.eval x := by
  obtain ⟨c, hc, hmean⟩ := polynomialMeanValue (P := P) hxy
  have hc' : c ∈ Set.Ioo a b := ⟨hx.1.trans_lt hc.1, hc.2.trans_le hy.2⟩
  have hneg : P.derivative.eval c * (y - x) < 0 :=
    mul_neg_of_neg_of_pos (hderiv c hc') (sub_pos.mpr hxy)
  linarith

/-- Between two distinct roots of a polynomial lies a root of its derivative. -/
theorem exists_derivative_root_between_roots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {x y : R} {P : R[X]} (hxy : x < y) (hx : P.IsRoot x) (hy : P.IsRoot y) :
    ∃ z ∈ Set.Ioo x y, P.derivative.IsRoot z := by
  obtain ⟨z, hz, hroot⟩ := polynomialRolle hxy (hx.trans hy.symm)
  exact ⟨z, hz, hroot⟩

/-- A polynomial has at most one root in an interval containing no root of its derivative. -/
theorem isRoot_injective_on_of_derivative_noRoot
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b x y : R} {P : R[X]}
    (hderiv : ∀ z ∈ Set.Ioo a b, ¬P.derivative.IsRoot z)
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hPx : P.IsRoot x) (hPy : P.IsRoot y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · obtain ⟨z, hz, hroot⟩ := exists_derivative_root_between_roots hxy hPx hPy
    exact (hderiv z ⟨hx.1.trans_le hz.1.le, hz.2.le.trans_lt hy.2⟩ hroot).elim
  · exact hxy
  · obtain ⟨z, hz, hroot⟩ := exists_derivative_root_between_roots hyx hPy hPx
    exact (hderiv z ⟨hy.1.trans_le hz.1.le, hz.2.le.trans_lt hx.2⟩ hroot).elim

/-- A simultaneous prescribed-sign system has a solution in the eliminated variable. -/
noncomputable def HasSolution {R : Type u} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : Fin s → IntPolynomialWithParameter n) (requiredSign : Fin s → SignType)
    (y : Fin n → R) : Prop :=
  ∃ x : R, ∀ i, SignType.sign ((specialize (p i) y).eval x) = requiredSign i

/-! ## Sign tables: Notation 1.4.3 and Lemma 1.4.4 -/

/-- A finite encoding of a sign matrix with `s` rows and at most `2 * s * m + 1` columns.

The first component is the number of distinct roots.  The second component has one column for each
root and one for each complementary interval.  This sigma type is finite, which is what the
uniform induction in Proposition 1.4.6 needs.
-/
def SignTable (s m : ℕ) :=
  Σ rootCount : Fin (s * m + 1), Fin s → Fin (2 * (rootCount : ℕ) + 1) → SignType

namespace SignTable

/-- A sign table accepts a sign vector when that vector occurs as one of its columns. -/
def Accepts (table : SignTable s m) (requiredSign : Fin s → SignType) : Prop :=
  ∃ column, ∀ row, table.2 row column = requiredSign row

end SignTable

/-- The distinct roots in `R` of all nonzero members of a polynomial family. -/
noncomputable def familyRoots {R : Type u} [Field R] [LinearOrder R]
    (p : Fin s → R[X]) : Finset R :=
  Finset.univ.biUnion fun i ↦ (p i).roots.toFinset

/-- The number of distinct roots of a family is at most the sum of its degree bounds. -/
theorem familyRoots_card_le {R : Type u} [Field R] [LinearOrder R]
    (p : Fin s → R[X]) (m : ℕ) (degree_le : ∀ i, (p i).natDegree ≤ m) :
    (familyRoots p).card ≤ s * m := by
  calc
    (familyRoots p).card ≤ ∑ i : Fin s, (p i).roots.toFinset.card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i : Fin s, m := Finset.sum_le_sum fun i _ ↦
      (Multiset.toFinset_card_le _).trans ((p i).card_roots'.trans (degree_le i))
    _ = s * m := by simp

/-- Samples beginning immediately to the right of `a`: one in each interval and at each listed
point, followed by one point to the right of the final listed point. -/
noncomputable def samplesFrom {R : Type u} [Field R] (a : R) : List R → List R
  | [] => [a + 1]
  | b :: roots => (a + b) / 2 :: b :: samplesFrom b roots

/-- `samplesFrom` contributes two samples per subsequent root and one final interval sample. -/
theorem samplesFrom_length {R : Type u} [Field R] (a : R) (roots : List R) :
    (samplesFrom a roots).length = 2 * roots.length + 1 := by
  induction roots generalizing a with
  | nil => simp [samplesFrom]
  | cons b roots ih => simp [samplesFrom, ih, Nat.mul_add]

/-- One sample at every listed point and one sample in each complementary interval. -/
noncomputable def cellSamples {R : Type u} [Field R] : List R → List R
  | [] => [0]
  | a :: roots => (a - 1) :: a :: samplesFrom a roots

/-- A list of `k` roots gives `2 * k + 1` point and interval samples. -/
theorem cellSamples_length {R : Type u} [Field R] (roots : List R) :
    (cellSamples roots).length = 2 * roots.length + 1 := by
  cases roots with
  | nil => simp [cellSamples]
  | cons a roots => simp [cellSamples, samplesFrom_length, Nat.mul_add]

/-- The sign table obtained by sorting all distinct roots of the nonzero polynomials and sampling
each intervening interval.

An implementation can use `Polynomial.roots.toFinset` and the linear order on `R`.  The bound on
the number of roots follows from `Polynomial.card_roots'`.
-/
noncomputable def rootSignTable {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : Fin s → R[X]) (m : ℕ) (degree_le : ∀ i, (p i).natDegree ≤ m) : SignTable s m := by
  let roots := familyRoots p
  let orderedRoots := roots.sort (· ≤ ·)
  let rootCount : Fin (s * m + 1) :=
    ⟨roots.card, Nat.lt_succ_of_le (familyRoots_card_le p m degree_le)⟩
  refine ⟨rootCount, fun row column ↦ SignType.sign ((p row).eval ?_)⟩
  exact (cellSamples orderedRoots).get
    (Fin.cast (by simp [rootCount, orderedRoots, Finset.length_sort, cellSamples_length]) column)

private def NoListPointBetween {R : Type u} [LT R]
    (roots : List R) (x y : R) : Prop :=
  ∀ z ∈ roots, ¬(x < z ∧ z < y) ∧ ¬(y < z ∧ z < x)

private theorem exists_mem_samplesFrom_sameCell
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {a x : R} {roots : List R} (hax : a < x) (hsorted : (a :: roots).SortedLT) :
    ∃ y ∈ samplesFrom a roots, a < y ∧
      (x = y ∨
        (x ∉ a :: roots ∧ y ∉ a :: roots ∧ NoListPointBetween (a :: roots) x y)) := by
  induction roots generalizing a x with
  | nil =>
      refine ⟨a + 1, by simp [samplesFrom], by linarith, ?_⟩
      by_cases hxy : x = a + 1
      · exact Or.inl hxy
      · right
        refine ⟨by simp [ne_of_gt hax], by simp, ?_⟩
        intro z hz
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
        subst z
        constructor <;> intro h <;> linarith
  | cons b roots ih =>
      have hpair : (a :: b :: roots).Pairwise (· < ·) := hsorted.pairwise
      have ha_all : ∀ z ∈ b :: roots, a < z := (List.pairwise_cons.mp hpair).1
      have htail : (b :: roots).SortedLT := (List.pairwise_cons.mp hpair).2.sortedLT
      have hab : a < b := ha_all b (by simp)
      rcases lt_trichotomy x b with hxb | hxb | hbx
      · let y := (a + b) / 2
        have hay : a < y := by dsimp [y]; linarith
        have hyb : y < b := by dsimp [y]; linarith
        refine ⟨y, by dsimp [y]; simp [samplesFrom], hay, ?_⟩
        by_cases hxy : x = y
        · exact Or.inl hxy
        · right
          refine ⟨?_, ?_, ?_⟩
          · simp only [List.mem_cons, not_or]
            refine ⟨ne_of_gt hax, ne_of_lt hxb, ?_⟩
            intro hxroots
            have := (List.pairwise_cons.mp htail.pairwise).1 x hxroots
            linarith
          · simp only [List.mem_cons, not_or]
            refine ⟨ne_of_gt hay, ne_of_lt hyb, ?_⟩
            intro hyroots
            have := (List.pairwise_cons.mp htail.pairwise).1 y hyroots
            linarith
          · intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | rfl | hz
            · constructor <;> intro h <;> linarith
            · constructor <;> intro h <;> linarith
            · have hbz := (List.pairwise_cons.mp htail.pairwise).1 z hz
              constructor <;> intro h <;> linarith
      · refine ⟨b, by simp [samplesFrom], hab, Or.inl hxb⟩
      · obtain ⟨y, hy, hby, hsame⟩ := ih hbx htail
        refine ⟨y, by simp [samplesFrom, hy], hab.trans hby, ?_⟩
        rcases hsame with rfl | ⟨hxmem, hymem, hbetween⟩
        · exact Or.inl rfl
        · right
          refine ⟨?_, ?_, ?_⟩
          · simp only [List.mem_cons, not_or]
            refine ⟨ne_of_gt hax, ?_⟩
            simpa only [List.mem_cons, not_or] using hxmem
          · simp only [List.mem_cons, not_or]
            refine ⟨ne_of_gt (hab.trans hby), ?_⟩
            simpa only [List.mem_cons, not_or] using hymem
          · intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | hz
            · constructor <;> intro h <;> linarith
            · exact hbetween z (by simp [hz])

private theorem exists_mem_cellSamples_sameCell
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (roots : List R) (hsorted : roots.SortedLT) (x : R) :
    ∃ y ∈ cellSamples roots,
      x = y ∨ (x ∉ roots ∧ y ∉ roots ∧ NoListPointBetween roots x y) := by
  cases roots with
  | nil =>
      refine ⟨0, by simp [cellSamples], ?_⟩
      by_cases hx : x = 0
      · exact Or.inl hx
      · exact Or.inr ⟨by simp, by simp, by simp [NoListPointBetween]⟩
  | cons a roots =>
      have hpair : (a :: roots).Pairwise (· < ·) := hsorted.pairwise
      have ha_all : ∀ z ∈ roots, a < z := (List.pairwise_cons.mp hpair).1
      rcases lt_trichotomy x a with hxa | hxa | hax
      · let y := a - 1
        have hya : y < a := by dsimp [y]; linarith
        refine ⟨y, by dsimp [y]; simp [cellSamples], ?_⟩
        by_cases hxy : x = y
        · exact Or.inl hxy
        · right
          refine ⟨?_, ?_, ?_⟩
          · simp only [List.mem_cons, not_or]
            refine ⟨ne_of_lt hxa, ?_⟩
            intro hxroots
            have := ha_all x hxroots
            linarith
          · simp only [List.mem_cons, not_or]
            refine ⟨ne_of_lt hya, ?_⟩
            intro hyroots
            have := ha_all y hyroots
            linarith
          · intro z hz
            simp only [List.mem_cons] at hz
            rcases hz with rfl | hz
            · constructor <;> intro h <;> linarith
            · have haz := ha_all z hz
              constructor <;> intro h <;> linarith
      · exact ⟨a, by simp [cellSamples], Or.inl hxa⟩
      · obtain ⟨y, hy, _hay, hsame⟩ :=
          exists_mem_samplesFrom_sameCell hax hsorted
        refine ⟨y, by simp [cellSamples, hy], hsame⟩

private theorem sign_eval_eq_of_no_root_between_points
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (intermediateValue : PolynomialIntermediateValue R) (p : R[X]) {x y : R}
    (hx : ¬p.IsRoot x) (hy : ¬p.IsRoot y)
    (noRoot : ∀ z, p.IsRoot z →
      ¬(x < z ∧ z < y) ∧ ¬(y < z ∧ z < x)) :
    SignType.sign (p.eval x) = SignType.sign (p.eval y) := by
  have hx0 : p.eval x ≠ 0 := by simpa only [Polynomial.IsRoot] using hx
  have hy0 : p.eval y ≠ 0 := by simpa only [Polynomial.IsRoot] using hy
  have not_opposite (hopposite : p.eval x * p.eval y < 0) : False := by
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · obtain ⟨z, hz, hroot⟩ := intermediateValue p hxy hopposite
      exact (noRoot z hroot).1 hz
    · exact (not_lt_of_ge (mul_self_nonneg _)) hopposite
    · obtain ⟨z, hz, hroot⟩ := intermediateValue p hyx (by simpa [mul_comm] using hopposite)
      exact (noRoot z hroot).2 hz
  rcases lt_trichotomy (p.eval x) 0 with hxneg | hxzero | hxpos
  · rcases lt_trichotomy (p.eval y) 0 with hyneg | hyzero | hypos
    · rw [sign_neg hxneg, sign_neg hyneg]
    · exact (hy0 hyzero).elim
    · exact (not_opposite (mul_neg_of_neg_of_pos hxneg hypos)).elim
  · exact (hx0 hxzero).elim
  · rcases lt_trichotomy (p.eval y) 0 with hyneg | hyzero | hypos
    · exact (not_opposite (mul_neg_of_pos_of_neg hxpos hyneg)).elim
    · exact (hy0 hyzero).elim
    · rw [sign_pos hxpos, sign_pos hypos]

private theorem isRoot_mem_familyRoots
    {R : Type u} [Field R] [LinearOrder R] (p : Fin s → R[X])
    {i : Fin s} {x : R} (hpne : p i ≠ 0) (hroot : (p i).IsRoot x) :
    x ∈ familyRoots p := by
  simp only [familyRoots, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, by simpa using (Polynomial.mem_roots hpne).2 hroot⟩

/-- Book Lemma 1.4.4.  Its proof needs the polynomial intermediate value property for ordered real
closed fields: a polynomial has constant sign on an interval containing no root. -/
theorem hasSolution_iff_accepts_rootSignTable {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] [IsRealClosed R] (p : Fin s → R[X])
    (requiredSign : Fin s → SignType) (m : ℕ) (degree_le : ∀ i, (p i).natDegree ≤ m) :
    (∃ x : R, ∀ i, SignType.sign ((p i).eval x) = requiredSign i) ↔
      (rootSignTable p m degree_le).Accepts requiredSign := by
  constructor
  · rintro ⟨x, hx⟩
    let roots := familyRoots p
    let orderedRoots := roots.sort (· ≤ ·)
    have hsorted : orderedRoots.SortedLT := by
      simpa [orderedRoots] using roots.sortedLT_sort
    obtain ⟨y, hy, hsame⟩ := exists_mem_cellSamples_sameCell orderedRoots hsorted x
    have hsigns : ∀ i, SignType.sign ((p i).eval y) = requiredSign i := by
      intro i
      rw [← hx i]
      rcases hsame with hxy | ⟨hxmem, hymem, hbetween⟩
      · rw [hxy]
      · by_cases hpzero : p i = 0
        · simp [hpzero]
        · exact (sign_eval_eq_of_no_root_between_points polynomialIntermediateValue (p i)
              (x := x) (y := y)
              (fun hroot ↦ hxmem ((Finset.mem_sort (· ≤ ·)).2
                (isRoot_mem_familyRoots p hpzero hroot)))
              (fun hroot ↦ hymem ((Finset.mem_sort (· ≤ ·)).2
                (isRoot_mem_familyRoots p hpzero hroot)))
              (fun z hroot ↦ hbetween z ((Finset.mem_sort (· ≤ ·)).2
                (isRoot_mem_familyRoots p hpzero hroot)))).symm
    obtain ⟨column, hcolumn⟩ := List.mem_iff_get.mp hy
    let rootCount : Fin (s * m + 1) :=
      ⟨roots.card, Nat.lt_succ_of_le (familyRoots_card_le p m degree_le)⟩
    let tableColumn : Fin (2 * (rootCount : ℕ) + 1) :=
      Fin.cast (by simp [rootCount, roots, orderedRoots, cellSamples_length]) column
    refine ⟨tableColumn, ?_⟩
    intro row
    change SignType.sign ((p row).eval ((cellSamples orderedRoots).get
      (Fin.cast _ tableColumn))) = requiredSign row
    have hindex : Fin.cast (by simp [rootCount, roots, orderedRoots, cellSamples_length])
        tableColumn = column := by
      apply Fin.ext
      rfl
    rw [hindex, hcolumn]
    exact hsigns row
  · rintro ⟨column, hcolumn⟩
    let x := (cellSamples ((familyRoots p).sort (· ≤ ·))).get
      (Fin.cast (by simp [rootSignTable, cellSamples_length]) column)
    refine ⟨x, ?_⟩
    intro i
    exact hcolumn i

/-! ## Degree reduction: Lemma 1.4.5 -/

/-- The multiset of degrees is the induction measure used in Proposition 1.4.6. -/
def degreeProfile {R : Type*} [Semiring R] (p : Fin s → R[X]) : Multiset ℕ :=
  List.ofFn fun i ↦ (p i).natDegree

/-- The first `s` polynomials followed by the derivative of the last polynomial. -/
noncomputable def reductionDivisor {R : Type u} [Field R]
    (p : Fin (s + 1) → R[X]) :
    Fin (s + 1) → R[X] :=
  Fin.lastCases (p (Fin.last s)).derivative fun i ↦ p i.castSucc

/-- The family
`f₁, ..., fₛ₋₁, fₛ', g₁, ..., gₛ`, where each `gᵢ` is the remainder of `fₛ` by the
corresponding member of `f₁, ..., fₛ₋₁, fₛ'`. -/
noncomputable def reducedFamily {R : Type u} [Field R] (p : Fin (s + 1) → R[X]) :
    Fin (2 * (s + 1)) → R[X] :=
  let q := reductionDivisor p
  fun i ↦
    Fin.append q (fun j ↦ p (Fin.last s) % q j)
      (Fin.cast (by omega : 2 * (s + 1) = (s + 1) + (s + 1)) i)

private theorem reductionDivisor_degree_le {R : Type u} [Field R]
    (p : Fin (s + 1) → R[X]) (m : ℕ) (degree_le : ∀ i, (p i).natDegree ≤ m) :
    ∀ i, (reductionDivisor p i).natDegree ≤ m := by
  intro i
  cases i using Fin.lastCases with
  | last =>
      simpa [reductionDivisor] using (Polynomial.natDegree_derivative_le _).trans
        ((Nat.sub_le _ _).trans (degree_le (Fin.last s)))
  | cast i => simpa [reductionDivisor] using degree_le i.castSucc

/-- Every polynomial in the reduced family has degree bounded by the original maximum. -/
theorem reducedFamily_degree_le {R : Type u} [Field R] (p : Fin (s + 1) → R[X]) (m : ℕ)
    (degree_le : ∀ i, (p i).natDegree ≤ m) :
    ∀ i, (reducedFamily p i).natDegree ≤ m := by
  intro i
  unfold reducedFamily
  generalize Fin.cast (by omega : 2 * (s + 1) = (s + 1) + (s + 1)) i = j
  cases j using Fin.addCases with
  | left j => simpa using reductionDivisor_degree_le p m degree_le j
  | right j =>
      simp only [Fin.append_right, Polynomial.mod_def]
      exact Polynomial.natDegree_modByMonic_le_left.trans (degree_le (Fin.last s))

private theorem degreeProfile_last {R : Type u} [Semiring R] (p : Fin (s + 1) → R[X]) :
    degreeProfile p = degreeProfile (fun i : Fin s ↦ p i.castSucc) +
      {(p (Fin.last s)).natDegree} := by
  unfold degreeProfile
  rw [List.ofFn_succ']
  rw [List.concat_eq_append, ← Multiset.coe_add, Multiset.coe_singleton]

private theorem degreeProfile_reducedFamily {R : Type u} [Field R]
    (p : Fin (s + 1) → R[X]) :
    degreeProfile (reducedFamily p) = degreeProfile (reductionDivisor p) +
      degreeProfile (fun i ↦ p (Fin.last s) % reductionDivisor p i) := by
  simp only [degreeProfile]
  rw [List.ofFn_congr (by omega : 2 * (s + 1) = (s + 1) + (s + 1))]
  simp only [reducedFamily, Fin.cast_cast, Fin.cast_eq_self]
  rw [List.ofFn_comp', List.ofFn_fin_append, List.map_append]
  simp [List.ofFn_comp']

private theorem degreeProfile_reductionDivisor {R : Type u} [Field R]
    (p : Fin (s + 1) → R[X]) :
    degreeProfile (reductionDivisor p) = degreeProfile (fun i : Fin s ↦ p i.castSucc) +
      {(p (Fin.last s)).derivative.natDegree} := by
  simpa [reductionDivisor] using degreeProfile_last (reductionDivisor p)

private theorem reductionDivisor_ne_zero {R : Type u} [Field R] [CharZero R]
    (p : Fin (s + 1) → R[X]) (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    ∀ i, reductionDivisor p i ≠ 0 := by
  intro i
  cases i using Fin.lastCases with
  | last => simpa [reductionDivisor] using Polynomial.derivative_ne_zero.mpr last_nonconstant
  | cast i => simpa [reductionDivisor] using first_ne_zero i

private theorem remainder_natDegree_lt_last {R : Type u} [Field R] [CharZero R]
    (p : Fin (s + 1) → R[X]) (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (last_maximal : ∀ i, (p i).natDegree ≤ (p (Fin.last s)).natDegree) (i : Fin (s + 1)) :
    (p (Fin.last s) % reductionDivisor p i).natDegree < (p (Fin.last s)).natDegree := by
  have divisor_ne_zero := reductionDivisor_ne_zero p first_ne_zero last_nonconstant i
  by_cases divisor_constant : (reductionDivisor p i).natDegree = 0
  · have divisor_degree : (reductionDivisor p i).degree = 0 := by
      rw [Polynomial.degree_eq_natDegree divisor_ne_zero, divisor_constant]
      simp
    have divisor_unit : IsUnit (reductionDivisor p i) :=
      Polynomial.isUnit_iff_degree_eq_zero.mpr divisor_degree
    rw [EuclideanDomain.mod_eq_zero.mpr divisor_unit.dvd, Polynomial.natDegree_zero]
    exact Nat.pos_of_ne_zero last_nonconstant
  · exact (Polynomial.natDegree_mod_lt _ divisor_constant).trans_le
      (reductionDivisor_degree_le p _ last_maximal i)

/-- Replacing a maximal-degree last polynomial by its derivative and remainders strictly lowers
the Dershowitz--Manna multiset extension of the degree order. -/
theorem reducedFamily_profile_lt {R : Type u} [Field R] [CharZero R]
    (p : Fin (s + 1) → R[X])
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (last_maximal : ∀ i, (p i).natDegree ≤ (p (Fin.last s)).natDegree) :
    Multiset.IsDershowitzMannaLT (degreeProfile (reducedFamily p)) (degreeProfile p) := by
  let initialProfile := degreeProfile (fun i : Fin s ↦ p i.castSucc)
  let remainderProfile := degreeProfile (fun i ↦ p (Fin.last s) % reductionDivisor p i)
  refine ⟨initialProfile,
    {(p (Fin.last s)).derivative.natDegree} + remainderProfile,
    {(p (Fin.last s)).natDegree}, by simp, ?_, ?_, ?_⟩
  · rw [degreeProfile_reducedFamily, degreeProfile_reductionDivisor]
    simp only [initialProfile, remainderProfile, Multiset.add_assoc]
  · exact degreeProfile_last p
  · intro degree degree_mem
    rw [Multiset.mem_add] at degree_mem
    rcases degree_mem with derivative_degree | remainder_degree
    · rw [Multiset.mem_singleton] at derivative_degree
      subst degree
      exact ⟨(p (Fin.last s)).natDegree, by simp,
        Polynomial.natDegree_derivative_lt last_nonconstant⟩
    · dsimp [remainderProfile] at remainder_degree
      rw [degreeProfile, Multiset.mem_coe, List.mem_ofFn', Set.mem_range] at remainder_degree
      obtain ⟨i, rfl⟩ := remainder_degree
      exact ⟨(p (Fin.last s)).natDegree, by simp,
        remainder_natDegree_lt_last p first_ne_zero last_nonconstant last_maximal i⟩


private theorem List.get_mem_take {α : Type u} (l : List α) (j : Fin l.length)
    (n : ℕ) (hjn : (j : ℕ) < n) : l.get j ∈ l.take n := by
  apply List.mem_iff_get.mpr
  let j' : Fin (l.take n).length := ⟨j, by simp; omega⟩
  refine ⟨j', ?_⟩
  simp [j']

private theorem List.get_mem_drop {α : Type u} (l : List α) (j : Fin l.length)
    (n : ℕ) (hnj : n ≤ (j : ℕ)) : l.get j ∈ l.drop n := by
  apply List.mem_iff_get.mpr
  let j' : Fin (l.drop n).length := ⟨j - n, by simp; omega⟩
  refine ⟨j', ?_⟩
  simp [j']
  congr
  omega

private theorem List.not_lt_head_of_sortedLT
    {R : Type u} [LinearOrder R] {a x : R} {l : List R}
    (hsorted : (a :: l).SortedLT) (hx : x ∈ a :: l) : ¬x < a := by
  have hx' : x = a ∨ x ∈ l := by simpa using hx
  rcases hx' with rfl | hx
  · exact lt_irrefl _
  · exact not_lt_of_ge ((List.pairwise_cons.mp hsorted.pairwise).1 x hx).le

private theorem List.not_between_adjacent_of_sortedLT
    {R : Type u} [LinearOrder R] {a b x : R} {pre suffix : List R}
    (hsorted : (pre ++ a :: b :: suffix).SortedLT)
    (hx : x ∈ pre ++ a :: b :: suffix) : ¬(a < x ∧ x < b) := by
  have happend := List.pairwise_append.mp hsorted.pairwise
  rw [List.mem_append] at hx
  rcases hx with hxprefix | hxrest
  · have hxa : x < a := happend.2.2 x hxprefix a (by simp)
    exact fun h ↦ (lt_asymm hxa h.1).elim
  · have hrest : (a :: b :: suffix).Pairwise (· < ·) := happend.2.1
    have hxrest' : x = a ∨ x = b ∨ x ∈ suffix := by simpa using hxrest
    rcases hxrest' with rfl | rfl | hxrest
    · exact fun h ↦ (lt_irrefl _ h.1).elim
    · exact fun h ↦ (lt_irrefl _ h.2).elim
    · have hbx : b < x :=
        (List.pairwise_cons.mp (List.pairwise_cons.mp hrest).2).1 x hxrest
      exact fun h ↦ (lt_asymm h.2 hbx).elim

private theorem List.not_gt_last_of_sortedLT
    {R : Type u} [LinearOrder R] {a x : R} {pre : List R}
    (hsorted : (pre ++ [a]).SortedLT) (hx : x ∈ pre ++ [a]) : ¬a < x := by
  have happend := List.pairwise_append.mp hsorted.pairwise
  rw [List.mem_append] at hx
  rcases hx with hxprefix | hxlast
  · have hxa : x < a := happend.2.2 x hxprefix a (by simp)
    exact fun h ↦ (lt_asymm h hxa).elim
  · simp only [List.mem_singleton] at hxlast
    subst x
    exact lt_irrefl _

private def firstReducedRow {s : ℕ} (i : Fin (s + 1)) : Fin (2 * (s + 1)) :=
  ⟨i, by omega⟩

private def remainderReducedRow {s : ℕ} (i : Fin (s + 1)) : Fin (2 * (s + 1)) :=
  ⟨s + 1 + i, by omega⟩

private def SignTable.rootColumn {s m : ℕ} (w : SignTable s m)
    (k : Fin (w.1 : ℕ)) : Fin (2 * (w.1 : ℕ) + 1) :=
  ⟨2 * k + 1, by omega⟩

private def SignTable.intervalColumn {s m : ℕ} (w : SignTable s m)
    (k : Fin ((w.1 : ℕ) + 1)) : Fin (2 * (w.1 : ℕ) + 1) :=
  ⟨2 * k, by omega⟩

private def samplesFromRootIndex {R : Type u} [Field R] (a : R) (roots : List R)
    (k : Fin roots.length) : Fin (samplesFrom a roots).length :=
  ⟨2 * k + 1, by rw [samplesFrom_length]; omega⟩

private theorem samplesFrom_get_root {R : Type u} [Field R] (a : R) (roots : List R)
    (k : Fin roots.length) :
    (samplesFrom a roots).get (samplesFromRootIndex a roots k) = roots.get k := by
  induction roots generalizing a with
  | nil => exact Fin.elim0 k
  | cons b roots ih =>
      cases k using Fin.cases with
      | zero => simp [samplesFrom, samplesFromRootIndex]
      | succ k =>
          have hindex : samplesFromRootIndex a (b :: roots) k.succ =
              Fin.succ (Fin.succ (samplesFromRootIndex b roots k)) := by
            apply Fin.ext
            simp [samplesFromRootIndex]
            omega
          rw [hindex]
          simpa [samplesFrom] using ih b k

private def samplesFromIntervalIndex {R : Type u} [Field R] (a : R) (roots : List R)
    (k : Fin (roots.length + 1)) : Fin (samplesFrom a roots).length :=
  ⟨2 * k, by rw [samplesFrom_length]; omega⟩

private theorem samplesFrom_get_interval_spec
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a : R) (roots : List R) (hsorted : (a :: roots).SortedLT)
    (k : Fin (roots.length + 1)) :
    let y := (samplesFrom a roots).get (samplesFromIntervalIndex a roots k)
    a < y ∧
      (∀ x ∈ roots.take k, x < y) ∧
      (∀ x ∈ roots.drop k, y < x) := by
  induction roots generalizing a with
  | nil =>
      have hk : k = 0 := Fin.eq_zero k
      subst k
      simp [samplesFrom, samplesFromIntervalIndex]
  | cons b roots ih =>
      have hpair : (a :: b :: roots).Pairwise (· < ·) := hsorted.pairwise
      have hab : a < b := (List.pairwise_cons.mp hpair).1 b (by simp)
      have htail : (b :: roots).SortedLT := (List.pairwise_cons.mp hpair).2.sortedLT
      cases k using Fin.cases with
      | zero =>
          have hb_all : ∀ x ∈ roots, b < x :=
            (List.pairwise_cons.mp htail.pairwise).1
          refine ⟨by simp [samplesFrom, samplesFromIntervalIndex]; linarith, by simp, ?_⟩
          intro x hx
          have hx' : x = b ∨ x ∈ roots := by simpa using hx
          rcases hx' with rfl | hx
          · simp [samplesFrom, samplesFromIntervalIndex]
            linarith
          · have hbx := hb_all x hx
            simp [samplesFrom, samplesFromIntervalIndex]
            linarith
      | succ k =>
          have hindex : samplesFromIntervalIndex a (b :: roots) k.succ =
              Fin.succ (Fin.succ (samplesFromIntervalIndex b roots k)) := by
            apply Fin.ext
            simp [samplesFromIntervalIndex]
            omega
          rw [hindex]
          simp only [samplesFrom, List.get_eq_getElem]
          have hspec := ih b htail k
          dsimp only at hspec
          refine ⟨hab.trans hspec.1, ?_, hspec.2.2⟩
          intro x hx
          have hx' : x = b ∨ x ∈ roots.take k := by simpa using hx
          rcases hx' with rfl | hx
          · exact hspec.1
          · exact hspec.2.1 x hx

private def cellSamplesRootIndex {R : Type u} [Field R] (roots : List R)
    (k : Fin roots.length) : Fin (cellSamples roots).length :=
  ⟨2 * k + 1, by rw [cellSamples_length]; omega⟩

private theorem cellSamples_get_root {R : Type u} [Field R] (roots : List R)
    (k : Fin roots.length) :
    (cellSamples roots).get (cellSamplesRootIndex roots k) = roots.get k := by
  cases roots with
  | nil => exact Fin.elim0 k
  | cons a roots =>
      cases k using Fin.cases with
      | zero => simp [cellSamples, cellSamplesRootIndex]
      | succ k =>
          have hindex : cellSamplesRootIndex (a :: roots) k.succ =
              Fin.succ (Fin.succ (samplesFromRootIndex a roots k)) := by
            apply Fin.ext
            simp [cellSamplesRootIndex, samplesFromRootIndex]
            omega
          rw [hindex]
          simpa [cellSamples] using samplesFrom_get_root a roots k

private def cellSamplesIntervalIndex {R : Type u} [Field R] (roots : List R)
    (k : Fin (roots.length + 1)) : Fin (cellSamples roots).length :=
  ⟨2 * k, by rw [cellSamples_length]; omega⟩

private theorem cellSamples_get_interval_spec
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (roots : List R) (hsorted : roots.SortedLT) (k : Fin (roots.length + 1)) :
    let y := (cellSamples roots).get (cellSamplesIntervalIndex roots k)
    (∀ x ∈ roots.take k, x < y) ∧
      (∀ x ∈ roots.drop k, y < x) := by
  cases roots with
  | nil => simp [cellSamples, cellSamplesIntervalIndex]
  | cons a roots =>
      cases k using Fin.cases with
      | zero =>
          have ha_all : ∀ x ∈ roots, a < x :=
            (List.pairwise_cons.mp hsorted.pairwise).1
          refine ⟨by simp, ?_⟩
          intro x hx
          have hx' : x = a ∨ x ∈ roots := by simpa using hx
          rcases hx' with rfl | hx
          · simp [cellSamples, cellSamplesIntervalIndex]
          · have hax := ha_all x hx
            simp [cellSamples, cellSamplesIntervalIndex]
            linarith
      | succ k =>
          have hindex : cellSamplesIntervalIndex (a :: roots) k.succ =
              Fin.succ (Fin.succ (samplesFromIntervalIndex a roots k)) := by
            apply Fin.ext
            simp [cellSamplesIntervalIndex, samplesFromIntervalIndex]
            omega
          rw [hindex]
          have hspec := samplesFrom_get_interval_spec a roots hsorted k
          dsimp only at hspec
          simpa [cellSamples] using ⟨⟨hspec.1, hspec.2.1⟩, hspec.2.2⟩

private def polynomialSignAtTop {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (p : R[X]) : SignType :=
  SignType.sign p.leadingCoeff

private noncomputable def polynomialSignAtBot {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (p : R[X]) : SignType :=
  polynomialSignAtTop (p.comp (-X))

private lemma sign_add_eq_sign_of_abs_lt_half
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (a b : R) (h : |b| < |a| / 2) :
    SignType.sign (a + b) = SignType.sign a := by
  rcases lt_trichotomy a 0 with ha | rfl | ha
  · have habs : |a| = -a := abs_of_neg ha
    have hbge : -|b| ≤ b := neg_abs_le b
    have hab : a + b < 0 := by
      rw [habs] at h
      linarith [le_abs_self b]
    rw [sign_neg hab, sign_neg ha]
  · have h' : |b| < 0 := by simpa only [abs_zero, zero_div] using h
    exact (not_lt_of_ge (abs_nonneg b) h').elim
  · have habs : |a| = a := abs_of_pos ha
    have hble : b ≤ |b| := le_abs_self b
    have hab : 0 < a + b := by
      rw [habs] at h
      linarith [neg_abs_le b]
    rw [sign_pos hab, sign_pos ha]

private lemma factorize_by {R : Type u} [Field R] (a x : R) (ha : a ≠ 0) :
    x = a * (x / a) := by
  field_simp

private lemma add_div {R : Type u} [Field R] (a b d : R) (hd : d ≠ 0) :
    (a + b) / d = a / d + b / d := by
  field_simp

private lemma bound_polynomialSignAtTop
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : R[X]) (hp : p ≠ 0) :
    ∃ upper : R, ∀ x, upper ≤ x → SignType.sign (p.eval x) = polynomialSignAtTop p := by
  let n := p.natDegree
  let M := ∑ i ∈ Finset.range n, |p.coeff i|
  let upper := (2 * M) / |p.leadingCoeff| + 1
  refine ⟨upper, ?_⟩
  intro x hx
  have hM : 0 ≤ M := by positivity
  have hquot : 0 ≤ (2 * M) / |p.leadingCoeff| := by positivity
  have hone : 1 ≤ upper := by dsimp [upper]; linarith
  have hxone : 1 ≤ x := hone.trans hx
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hxone
  have hxpow : 0 < x ^ p.natDegree := by positivity
  have hxpow_ne : x ^ p.natDegree ≠ 0 := ne_of_gt hxpow
  have hxne : x ≠ 0 := ne_of_gt hxpos
  rw [eval_eq_sum_range, Finset.sum_range_succ_comm, coeff_natDegree]
  have hfactor :
      p.leadingCoeff * x ^ p.natDegree +
          ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i =
        x ^ p.natDegree *
          (p.leadingCoeff + ∑ i ∈ Finset.range p.natDegree,
            p.coeff i * x ^ ((i : ℤ) - n)) := by
    rw [factorize_by _ (p.leadingCoeff * x ^ p.natDegree +
      ∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ i) hxpow_ne]
    simp only [mul_eq_mul_left_iff]
    left
    rw [add_div _ _ _ hxpow_ne]
    have hlead : p.leadingCoeff * x ^ p.natDegree / x ^ p.natDegree =
        p.leadingCoeff := by field_simp
    rw [hlead]
    · simp only [add_right_inj]
      rw [Finset.sum_div]
      congr
      ext i
      field_simp
      dsimp [n]
      rw [mul_assoc]
      have hpow : x ^ (p.natDegree : ℤ) * x ^ ((i : ℤ) - p.natDegree) = x ^ i := by
        rw [← zpow_add₀ hxne]
        norm_num
      have hpow' : x ^ p.natDegree * x ^ ((i : ℤ) - p.natDegree) = x ^ i := by
        simpa using hpow
      rw [hpow']
  rw [hfactor, sign_mul, sign_pos hxpow, one_mul]
  have htail :
      |∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ ((i : ℤ) - n)| ≤ M / x := by
    dsimp [M]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    have habsx : |x| = x := abs_of_pos hxpos
    rw [abs_mul, abs_zpow, habsx]
    field_simp
    rw [mul_assoc, show x ^ ((i : ℤ) - n) * x = x ^ ((i : ℤ) - n + 1) by
      exact (zpow_add_one₀ hxne _).symm]
    have hexp : (i : ℤ) - n + 1 ≤ 0 := by
      simp only [Finset.mem_range] at hi
      dsimp [n]
      omega
    exact mul_le_of_le_one_right (abs_nonneg _) (zpow_le_one_of_nonpos₀ hxone hexp)
  have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp
  have hupper : M / upper < |p.leadingCoeff| / 2 := by
    dsimp [upper]
    field_simp
    simp_all only [ne_eq, pow_pos, pow_eq_zero_iff',
      false_and, not_false_eq_true, leadingCoeff_eq_zero, lt_add_iff_pos_right, abs_pos]
  have hdiv : M / x ≤ M / upper := by
    gcongr
  have hsmall :
      |∑ i ∈ Finset.range p.natDegree, p.coeff i * x ^ ((i : ℤ) - n)| <
        |p.leadingCoeff| / 2 := htail.trans_lt (hdiv.trans_lt hupper)
  exact sign_add_eq_sign_of_abs_lt_half _ _ hsmall

private lemma bound_polynomialSignAtBot
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : R[X]) (hp : p ≠ 0) :
    ∃ lower : R, ∀ x, x ≤ lower → SignType.sign (p.eval x) = polynomialSignAtBot p := by
  have hcomp : p.comp (-X) ≠ 0 := by
    exact Polynomial.comp_neg_X_eq_zero_iff.not.mpr hp
  obtain ⟨upper, hupper⟩ := bound_polynomialSignAtTop (p.comp (-X)) hcomp
  refine ⟨-upper, ?_⟩
  intro x hx
  have := hupper (-x) (by linarith)
  simpa [polynomialSignAtBot] using this

private lemma polynomialSignAtTop_derivative
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : R[X]) (hdegree : p.natDegree ≠ 0) :
    polynomialSignAtTop p.derivative = polynomialSignAtTop p := by
  have hpos : (0 : R) < p.natDegree := by exact_mod_cast Nat.pos_of_ne_zero hdegree
  simp [polynomialSignAtTop, sign_mul, sign_pos hpos]

private lemma polynomialSignAtBot_derivative
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : R[X]) (hdegree : p.natDegree ≠ 0) :
    polynomialSignAtBot p.derivative = -polynomialSignAtBot p := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hdegree
  simp only [polynomialSignAtBot, polynomialSignAtTop,
    Polynomial.comp_neg_X_leadingCoeff_eq]
  rw [Polynomial.natDegree_derivative, Polynomial.leadingCoeff_derivative, hk]
  simp only [Nat.succ_sub_one]
  have hkpos : (0 : R) < (k.succ : ℕ) := by exact_mod_cast Nat.succ_pos k
  rw [sign_mul, sign_mul, sign_mul, sign_pos hkpos, mul_one]
  simp only [pow_succ]
  rw [sign_mul]
  simp

private noncomputable def qRootIndices {s m : ℕ} (w : SignTable (2 * (s + 1)) m) :
    List (Fin (w.1 : ℕ)) :=
  (List.finRange (w.1 : ℕ)).filter fun k ↦
    ∃ i : Fin (s + 1), w.2 (firstReducedRow i) (w.rootColumn k) = 0

private noncomputable def qRootWitness {s m : ℕ} (w : SignTable (2 * (s + 1)) m)
    (k : Fin (w.1 : ℕ)) : Fin (s + 1) :=
  if h : ∃ i : Fin (s + 1), w.2 (firstReducedRow i) (w.rootColumn k) = 0 then
    Classical.choose h
  else
    Fin.last s

private noncomputable def lastSignAtQRoot {s m : ℕ}
    (w : SignTable (2 * (s + 1)) m) (k : Fin (w.1 : ℕ)) : SignType :=
  w.2 (remainderReducedRow (qRootWitness w k)) (w.rootColumn k)

private def qCellAfterRoot {s m : ℕ} (w : SignTable (2 * (s + 1)) m)
    (k : Fin (w.1 : ℕ)) : Fin ((w.1 : ℕ) + 1) :=
  ⟨k + 1, by omega⟩

private def derivativeSignInCell {s m : ℕ} (w : SignTable (2 * (s + 1)) m)
    (cell : Fin ((w.1 : ℕ) + 1)) : SignType :=
  w.2 (firstReducedRow (Fin.last s)) (w.intervalColumn cell)

private noncomputable def keepQRoot {s m : ℕ} (w : SignTable (2 * (s + 1)) m)
    (k : Fin (w.1 : ℕ)) : Bool :=
  decide ((∃ i : Fin s, w.2 (firstReducedRow i.castSucc) (w.rootColumn k) = 0) ∨
    lastSignAtQRoot w k = 0)

private structure ReconstructedRoot {s m : ℕ} (w : SignTable (2 * (s + 1)) m) where
  sourceColumn : Fin (2 * (w.1 : ℕ) + 1)
  rightCell : Fin ((w.1 : ℕ) + 1)
  lastSign : SignType

private noncomputable def reconstructedRootAtQRoot {s m : ℕ}
    (w : SignTable (2 * (s + 1)) m)
    (k : Fin (w.1 : ℕ)) : ReconstructedRoot w where
  sourceColumn := w.rootColumn k
  rightCell := qCellAfterRoot w k
  lastSign := lastSignAtQRoot w k

private def reconstructedRootInCell {s m : ℕ} (w : SignTable (2 * (s + 1)) m)
    (cell : Fin ((w.1 : ℕ) + 1)) : ReconstructedRoot w where
  sourceColumn := w.intervalColumn cell
  rightCell := cell
  lastSign := 0

private noncomputable def optionalQRoot {s m : ℕ} (w : SignTable (2 * (s + 1)) m)
    (k : Fin (w.1 : ℕ)) : List (ReconstructedRoot w) :=
  if keepQRoot w k then [reconstructedRootAtQRoot w k] else []

private noncomputable def reconstructionRootsAfter {s m : ℕ}
    (w : SignTable (2 * (s + 1)) m) (previous : Fin (w.1 : ℕ)) :
    List (Fin (w.1 : ℕ)) → List (ReconstructedRoot w)
  | [] =>
      let cell := qCellAfterRoot w previous
      (if derivativeSignInCell w cell * lastSignAtQRoot w previous = -1 then
        [reconstructedRootInCell w cell]
      else [])
  | next :: rest =>
      let cell := qCellAfterRoot w previous
      (if lastSignAtQRoot w previous * lastSignAtQRoot w next = -1 then
        [reconstructedRootInCell w cell]
      else []) ++ optionalQRoot w next ++ reconstructionRootsAfter w next rest

private noncomputable def reconstructionRoots {s m : ℕ}
    (w : SignTable (2 * (s + 1)) m) : List (ReconstructedRoot w) :=
  match qRootIndices w with
  | [] => [reconstructedRootInCell w 0]
  | first :: rest =>
      (if derivativeSignInCell w 0 * lastSignAtQRoot w first = 1 then
        [reconstructedRootInCell w 0]
      else []) ++ optionalQRoot w first ++ reconstructionRootsAfter w first rest

private def reconstructedRootSigns {s m : ℕ} (w : SignTable (2 * (s + 1)) m)
    (root : ReconstructedRoot w) : Fin (s + 1) → SignType :=
  Fin.lastCases root.lastSign fun i ↦ w.2 (firstReducedRow i.castSucc) root.sourceColumn

private def reconstructedInitialIntervalSigns {s m : ℕ}
    (w : SignTable (2 * (s + 1)) m) : Fin (s + 1) → SignType :=
  Fin.lastCases (-derivativeSignInCell w 0) fun i ↦
    w.2 (firstReducedRow i.castSucc) (w.intervalColumn 0)

private def reconstructedRightIntervalSigns {s m : ℕ}
    (w : SignTable (2 * (s + 1)) m) (root : ReconstructedRoot w) :
    Fin (s + 1) → SignType :=
  Fin.lastCases
    (if root.lastSign = 0 then derivativeSignInCell w root.rightCell else root.lastSign)
    fun i ↦ w.2 (firstReducedRow i.castSucc) (w.intervalColumn root.rightCell)

private noncomputable def reconstructedColumns {s m : ℕ}
    (w : SignTable (2 * (s + 1)) m) : List (Fin (s + 1) → SignType) :=
  reconstructedInitialIntervalSigns w ::
    (reconstructionRoots w).flatMap fun root ↦
      [reconstructedRootSigns w root, reconstructedRightIntervalSigns w root]

private theorem reconstructedColumns_length {s m : ℕ}
  (w : SignTable (2 * (s + 1)) m) :
    (reconstructedColumns w).length = 2 * (reconstructionRoots w).length + 1 := by
  simp [reconstructedColumns, Nat.mul_comm]

private noncomputable def reconstructSignTable (s m : ℕ) :
    SignTable (2 * (s + 1)) m → SignTable (s + 1) m := fun w ↦
  if h : (reconstructionRoots w).length < (s + 1) * m + 1 then
    ⟨⟨(reconstructionRoots w).length, h⟩, fun row column ↦
      (reconstructedColumns w).get
        (Fin.cast (by simp [reconstructedColumns_length]) column) row⟩
  else
    ⟨0, fun _ _ ↦ 0⟩

private theorem rootColumn_sign
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (r : Fin t → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (i : Fin t) (k : Fin ((rootSignTable r m degree_le).1 : ℕ)) :
    (rootSignTable r m degree_le).2 i
        ((rootSignTable r m degree_le).rootColumn k) =
      SignType.sign ((r i).eval (((familyRoots r).sort (· ≤ ·)).get
        (Fin.cast (by simp [rootSignTable]) k))) := by
  unfold rootSignTable at k
  unfold SignTable.rootColumn rootSignTable
  let roots := familyRoots r
  let orderedRoots := roots.sort (· ≤ ·)
  change SignType.sign ((r i).eval ((cellSamples orderedRoots).get _)) = _
  let k' : Fin orderedRoots.length := Fin.cast (by simp [orderedRoots, roots]) k
  have hget := congrArg (fun x ↦ SignType.sign ((r i).eval x))
    (cellSamples_get_root orderedRoots k')
  convert hget using 1
  · congr 3

private noncomputable def intervalSample
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (r : Fin t → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (cell : Fin (((rootSignTable r m degree_le).1 : ℕ) + 1)) : R :=
  let orderedRoots := (familyRoots r).sort (· ≤ ·)
  (cellSamples orderedRoots).get (cellSamplesIntervalIndex orderedRoots
    (Fin.cast (by simp [rootSignTable, orderedRoots]) cell))

private noncomputable def sourceRootValue
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (r : Fin t → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ)) : R :=
  ((familyRoots r).sort (· ≤ ·)).get (Fin.cast (by simp [rootSignTable]) k)

private theorem intervalColumn_sign
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (r : Fin t → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (i : Fin t) (cell : Fin (((rootSignTable r m degree_le).1 : ℕ) + 1)) :
    (rootSignTable r m degree_le).2 i
        ((rootSignTable r m degree_le).intervalColumn cell) =
      SignType.sign ((r i).eval (intervalSample r degree_le cell)) := by
  unfold SignTable.intervalColumn intervalSample rootSignTable
  rfl

private theorem intervalSample_spec
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (r : Fin t → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (cell : Fin (((rootSignTable r m degree_le).1 : ℕ) + 1)) :
    let orderedRoots := (familyRoots r).sort (· ≤ ·)
    let k : Fin (orderedRoots.length + 1) :=
      Fin.cast (by simp [rootSignTable, orderedRoots]) cell
    (∀ x ∈ orderedRoots.take k, x < intervalSample r degree_le cell) ∧
      (∀ x ∈ orderedRoots.drop k, intervalSample r degree_le cell < x) := by
  dsimp only
  exact cellSamples_get_interval_spec _
    (by simpa using (familyRoots r).sortedLT_sort) _

private theorem sourceRootValue_lt_intervalSample
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (r : Fin t → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ))
    (cell : Fin (((rootSignTable r m degree_le).1 : ℕ) + 1))
    (hkc : (k : ℕ) < cell) :
    sourceRootValue r degree_le k < intervalSample r degree_le cell := by
  let orderedRoots := (familyRoots r).sort (· ≤ ·)
  let k' : Fin orderedRoots.length := Fin.cast (by simp [orderedRoots, rootSignTable]) k
  have hmem : orderedRoots.get k' ∈ orderedRoots.take (cell : ℕ) :=
    List.get_mem_take orderedRoots k' cell hkc
  exact (intervalSample_spec r degree_le cell).1 _ hmem

private theorem intervalSample_lt_sourceRootValue
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (r : Fin t → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (cell : Fin (((rootSignTable r m degree_le).1 : ℕ) + 1))
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ))
    (hck : (cell : ℕ) ≤ k) :
    intervalSample r degree_le cell < sourceRootValue r degree_le k := by
  let orderedRoots := (familyRoots r).sort (· ≤ ·)
  let k' : Fin orderedRoots.length := Fin.cast (by simp [orderedRoots, rootSignTable]) k
  have hmem : orderedRoots.get k' ∈ orderedRoots.drop (cell : ℕ) :=
    List.get_mem_drop orderedRoots k' cell hck
  exact (intervalSample_spec r degree_le cell).2 _ hmem

private theorem sourceRootValue_lt_sourceRootValue_iff
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (r : Fin t → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k l : Fin ((rootSignTable r m degree_le).1 : ℕ)) :
    sourceRootValue r degree_le k < sourceRootValue r degree_le l ↔ (k : ℕ) < l := by
  let orderedRoots := (familyRoots r).sort (· ≤ ·)
  have hsorted : orderedRoots.SortedLT := by
    simpa [orderedRoots] using (familyRoots r).sortedLT_sort
  let k' : Fin orderedRoots.length := Fin.cast (by simp [rootSignTable, orderedRoots]) k
  let l' : Fin orderedRoots.length := Fin.cast (by simp [rootSignTable, orderedRoots]) l
  change orderedRoots.get k' < orderedRoots.get l' ↔ (k : ℕ) < l
  constructor
  · intro hvalue
    by_contra hindex
    have hlk : (l : ℕ) ≤ k := Nat.le_of_not_gt hindex
    rcases hlk.eq_or_lt with hlk | hlk
    · have hkl : k = l := Fin.ext hlk.symm
      subst l
      exact (lt_irrefl _ hvalue).elim
    · have hlk' : l' < k' := by exact hlk
      exact (lt_asymm (hsorted.strictMono_get hlk') hvalue).elim
  · intro hindex
    apply hsorted.strictMono_get
    exact hindex

private theorem qRootIndices_sorted {s m : ℕ} (w : SignTable (2 * (s + 1)) m) :
    (qRootIndices w).SortedLT := by
  unfold qRootIndices
  have hsorted : (List.finRange (w.1 : ℕ)).Pairwise (· < ·) := by
    rw [List.pairwise_iff_get]
    intro i j hij
    simpa using hij
  exact (hsorted.filter _).sortedLT

private theorem reducedRootColumn_sign
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (q : Fin (s + 1) → R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (hfirst : ∀ i, r (firstReducedRow i) = q i)
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (i : Fin (s + 1))
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ)) :
    (rootSignTable r m degree_le).2 (firstReducedRow i)
        ((rootSignTable r m degree_le).rootColumn k) =
      SignType.sign ((q i).eval (((familyRoots r).sort (· ≤ ·)).get
        (Fin.cast (by simp [rootSignTable]) k))) := by
  rw [rootColumn_sign, hfirst]

private theorem reducedIntervalColumn_sign
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (q : Fin (s + 1) → R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (hfirst : ∀ i, r (firstReducedRow i) = q i)
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (i : Fin (s + 1))
    (cell : Fin (((rootSignTable r m degree_le).1 : ℕ) + 1)) :
    (rootSignTable r m degree_le).2 (firstReducedRow i)
        ((rootSignTable r m degree_le).intervalColumn cell) =
      SignType.sign ((q i).eval (intervalSample r degree_le cell)) := by
  rw [intervalColumn_sign, hfirst]

private theorem derivativeSignInCell_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (q : Fin (s + 1) → R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (hfirst : ∀ i, r (firstReducedRow i) = q i)
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (cell : Fin (((rootSignTable r m degree_le).1 : ℕ) + 1)) :
    derivativeSignInCell (rootSignTable r m degree_le) cell =
      SignType.sign ((q (Fin.last s)).eval (intervalSample r degree_le cell)) := by
  exact reducedIntervalColumn_sign q r hfirst degree_le (Fin.last s) cell

private theorem reducedRootPredicate_iff
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (q : Fin (s + 1) → R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (hfirst : ∀ i, r (firstReducedRow i) = q i) (hqne : ∀ i, q i ≠ 0)
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ)) :
    (∃ i : Fin (s + 1),
        (rootSignTable r m degree_le).2 (firstReducedRow i)
          ((rootSignTable r m degree_le).rootColumn k) = 0) ↔
      ((familyRoots r).sort (· ≤ ·)).get (Fin.cast (by simp [rootSignTable]) k) ∈
        familyRoots q := by
  let x := ((familyRoots r).sort (· ≤ ·)).get (Fin.cast (by simp [rootSignTable]) k)
  constructor
  · rintro ⟨i, hi⟩
    rw [reducedRootColumn_sign q r hfirst degree_le] at hi
    have hroot : (q i).IsRoot x := by
      change SignType.sign ((q i).eval x) = 0 at hi
      exact sign_eq_zero_iff.mp hi
    change x ∈ familyRoots q
    simp only [familyRoots, Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, by simpa using (Polynomial.mem_roots (hqne i)).2 hroot⟩
  · intro hx
    change x ∈ familyRoots q at hx
    simp only [familyRoots, Finset.mem_biUnion] at hx
    obtain ⟨i, _hi, hroot⟩ := hx
    refine ⟨i, ?_⟩
    rw [reducedRootColumn_sign q r hfirst degree_le]
    change SignType.sign ((q i).eval x) = 0
    apply sign_eq_zero_iff.mpr
    exact (Polynomial.mem_roots (hqne i)).1 (by simpa using hroot)

private theorem map_get_filter_finRange {α : Type u} (l : List α) (p : α → Prop)
    [DecidablePred p] (hn : l.Nodup) :
    ((List.finRange l.length).filter fun k ↦ p (l.get k)).map l.get = l.filter p := by
  classical
  rw [List.map_filter (p := fun k ↦ p (l.get k)) hn.injective_get]
  rw [← List.ofFn_eq_map, List.ofFn_get]
  apply List.filter_congr
  intro x hx
  apply Bool.decide_congr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact hk
  · intro hpx
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hx
    exact ⟨k, hk.symm ▸ hpx, hk⟩

private theorem map_get_cast_filter_finRange {α : Type u} (l : List α) (p : α → Prop)
    [DecidablePred p] (hn : l.Nodup) {n : ℕ} (hnl : n = l.length) :
    ((List.finRange n).filter fun k ↦ p (l.get (Fin.cast hnl k))).map
        (fun k ↦ l.get (Fin.cast hnl k)) = l.filter p := by
  subst n
  change ((List.finRange l.length).filter fun k ↦ p (l.get k)).map l.get = l.filter p
  exact map_get_filter_finRange l p hn

private theorem qRootValues_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (q : Fin (s + 1) → R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (hfirst : ∀ i, r (firstReducedRow i) = q i) (hqne : ∀ i, q i ≠ 0)
    (degree_le : ∀ i, (r i).natDegree ≤ m) :
    let w := rootSignTable r m degree_le
    (qRootIndices w).map (fun k ↦
      ((familyRoots r).sort (· ≤ ·)).get (Fin.cast (by simp [w, rootSignTable]) k)) =
        (familyRoots q).sort (· ≤ ·) := by
  classical
  let w := rootSignTable r m degree_le
  let redRoots := familyRoots r
  let orderedRed := redRoots.sort (· ≤ ·)
  let qRoots := familyRoots q
  let orderedQ := qRoots.sort (· ≤ ·)
  have hfilter : qRootIndices w =
      (List.finRange (w.1 : ℕ)).filter fun k ↦
        orderedRed.get
          (Fin.cast (by simp [w, orderedRed, redRoots, rootSignTable]) k) ∈ qRoots := by
    unfold qRootIndices
    apply List.filter_congr
    intro k _hk
    apply Bool.decide_congr
    exact reducedRootPredicate_iff q r hfirst hqne degree_le k
  have hsubset : qRoots ⊆ redRoots := by
    intro x hx
    dsimp [qRoots, redRoots] at hx ⊢
    simp only [familyRoots, Finset.mem_biUnion] at hx ⊢
    obtain ⟨i, _hi, hroot⟩ := hx
    refine ⟨firstReducedRow i, Finset.mem_univ _, ?_⟩
    rw [hfirst]
    exact hroot
  change (qRootIndices w).map (fun k ↦
    orderedRed.get (Fin.cast (by simp [w, orderedRed, redRoots, rootSignTable]) k)) = orderedQ
  rw [hfilter]
  have hfiltered :
      ((List.finRange (w.1 : ℕ)).filter fun k ↦
        orderedRed.get
          (Fin.cast (by simp [w, orderedRed, redRoots, rootSignTable]) k) ∈ qRoots).map
          (fun k ↦ orderedRed.get
            (Fin.cast (by simp [w, orderedRed, redRoots, rootSignTable]) k)) =
        orderedRed.filter (· ∈ qRoots) := by
    apply map_get_cast_filter_finRange orderedRed (· ∈ qRoots)
      (by
        change (redRoots.sort (· ≤ ·)).Nodup
        exact redRoots.sort_nodup (· ≤ ·))
  rw [hfiltered]
  have hsortedRed : orderedRed.SortedLT := by
    simpa [orderedRed] using redRoots.sortedLT_sort
  have hsortedQ : orderedQ.SortedLT := by
    simpa [orderedQ] using qRoots.sortedLT_sort
  have hsortedFiltered : (orderedRed.filter (· ∈ qRoots)).SortedLT :=
    (hsortedRed.pairwise.filter _).sortedLT
  apply hsortedFiltered.eq_of_mem_iff hsortedQ
  intro x
  simp only [List.mem_filter, decide_eq_true_eq]
  rw [show x ∈ orderedRed ↔ x ∈ redRoots by simp [orderedRed],
    show x ∈ orderedQ ↔ x ∈ qRoots by simp [orderedQ]]
  exact ⟨fun h ↦ h.2, fun hx ↦ ⟨hsubset hx, hx⟩⟩

private theorem reducedFamily_firstRow
    {R : Type u} [Field R] {s : ℕ} (p : Fin (s + 1) → R[X])
    (i : Fin (s + 1)) :
    reducedFamily p (firstReducedRow i) = reductionDivisor p i := by
  unfold reducedFamily
  rw [show Fin.cast (by omega : 2 * (s + 1) = (s + 1) + (s + 1))
      (firstReducedRow i) = Fin.castLE (by omega) i by rfl]
  exact Fin.append_left' _ _ i

private theorem reducedFamily_remainderRow
    {R : Type u} [Field R] {s : ℕ} (p : Fin (s + 1) → R[X])
    (i : Fin (s + 1)) :
    reducedFamily p (remainderReducedRow i) =
      p (Fin.last s) % reductionDivisor p i := by
  unfold reducedFamily
  rw [show Fin.cast (by omega : 2 * (s + 1) = (s + 1) + (s + 1))
      (remainderReducedRow i) = Fin.natAdd (s + 1) i by rfl]
  exact Fin.append_right _ _ i

private theorem eval_mod_at_root {R : Type u} [Field R]
    (p q : R[X]) (x : R) (hqx : q.eval x = 0) :
    (p % q).eval x = p.eval x := by
  have h := congrArg (Polynomial.eval x) (EuclideanDomain.div_add_mod' p q)
  simpa [hqx] using h

private theorem sign_eval_eq_of_no_root_between'
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (intermediateValue : PolynomialIntermediateValue R) (p : R[X]) {x y : R}
    (hx : ¬p.IsRoot x) (hy : ¬p.IsRoot y)
    (noRoot : ∀ z, p.IsRoot z →
      ¬(x < z ∧ z < y) ∧ ¬(y < z ∧ z < x)) :
    SignType.sign (p.eval x) = SignType.sign (p.eval y) := by
  have hx0 : p.eval x ≠ 0 := by simpa only [Polynomial.IsRoot] using hx
  have hy0 : p.eval y ≠ 0 := by simpa only [Polynomial.IsRoot] using hy
  have not_opposite (hopposite : p.eval x * p.eval y < 0) : False := by
    rcases lt_trichotomy x y with hxy | rfl | hyx
    · obtain ⟨z, hz, hroot⟩ := intermediateValue p hxy hopposite
      exact (noRoot z hroot).1 hz
    · exact (not_lt_of_ge (mul_self_nonneg _)) hopposite
    · obtain ⟨z, hz, hroot⟩ := intermediateValue p hyx (by simpa [mul_comm] using hopposite)
      exact (noRoot z hroot).2 hz
  rcases lt_trichotomy (p.eval x) 0 with hxneg | hxzero | hxpos
  · rcases lt_trichotomy (p.eval y) 0 with hyneg | hyzero | hypos
    · rw [sign_neg hxneg, sign_neg hyneg]
    · exact (hy0 hyzero).elim
    · exact (not_opposite (mul_neg_of_neg_of_pos hxneg hypos)).elim
  · exact (hx0 hxzero).elim
  · rcases lt_trichotomy (p.eval y) 0 with hyneg | hyzero | hypos
    · exact (not_opposite (mul_neg_of_pos_of_neg hxpos hyneg)).elim
    · exact (hy0 hyzero).elim
    · rw [sign_pos hxpos, sign_pos hypos]

private theorem derivative_pos_or_neg_on_Ioo
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R} {f : R[X]} (hab : a < b)
    (hderiv : ∀ z ∈ Set.Ioo a b, ¬f.derivative.IsRoot z) :
    (∀ z ∈ Set.Ioo a b, 0 < f.derivative.eval z) ∨
      (∀ z ∈ Set.Ioo a b, f.derivative.eval z < 0) := by
  let c := (a + b) / 2
  have hc : c ∈ Set.Ioo a b := by dsimp [c]; constructor <;> linarith
  have hc0 : f.derivative.eval c ≠ 0 := by
    simpa only [Polynomial.IsRoot] using hderiv c hc
  rcases lt_or_gt_of_ne hc0 with hcneg | hcpos
  · right
    intro z hz
    have hsign := sign_eval_eq_of_no_root_between' polynomialIntermediateValue
      f.derivative (hderiv z hz) (hderiv c hc) (x := z) (y := c) ?_
    · rw [sign_neg hcneg] at hsign
      exact sign_eq_neg_one_iff.mp hsign
    · intro x hx
      constructor
      · rintro ⟨hzx, hxc⟩
        exact hderiv x ⟨lt_trans hz.1 hzx, lt_trans hxc hc.2⟩ hx
      · rintro ⟨hcx, hxz⟩
        exact hderiv x ⟨lt_trans hc.1 hcx, lt_trans hxz hz.2⟩ hx
  · left
    intro z hz
    have hsign := sign_eval_eq_of_no_root_between' polynomialIntermediateValue
      f.derivative (hderiv z hz) (hderiv c hc) (x := z) (y := c) ?_
    · rw [sign_pos hcpos] at hsign
      exact sign_eq_one_iff.mp hsign
    · intro x hx
      constructor
      · rintro ⟨hzx, hxc⟩
        exact hderiv x ⟨lt_trans hz.1 hzx, lt_trans hxc hc.2⟩ hx
      · rintro ⟨hcx, hxz⟩
        exact hderiv x ⟨lt_trans hc.1 hcx, lt_trans hxz hz.2⟩ hx

private theorem exists_root_Ioo_iff_sign_mul_eq_neg_one
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a b : R} {f : R[X]} (hab : a < b)
    (hderiv : ∀ z ∈ Set.Ioo a b, ¬f.derivative.IsRoot z) :
    (∃ x ∈ Set.Ioo a b, f.IsRoot x) ↔
      SignType.sign (f.eval a) * SignType.sign (f.eval b) = -1 := by
  rw [← sign_mul, sign_eq_neg_one_iff]
  constructor
  · rintro ⟨x, hx, hfx⟩
    rcases derivative_pos_or_neg_on_Ioo hab hderiv with hpos | hneg
    · have hax := eval_lt_eval_of_derivative_pos_on
        (P := f) (a := a) (b := b) ⟨le_rfl, hab.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1 hpos
      have hxb := eval_lt_eval_of_derivative_pos_on
        (P := f) (a := a) (b := b) ⟨hx.1.le, hx.2.le⟩ ⟨hab.le, le_rfl⟩ hx.2 hpos
      change f.eval x = 0 at hfx
      rw [hfx] at hax hxb
      exact mul_neg_of_neg_of_pos hax hxb
    · have hax := eval_lt_eval_of_derivative_neg_on
        (P := f) (a := a) (b := b) ⟨le_rfl, hab.le⟩ ⟨hx.1.le, hx.2.le⟩ hx.1 hneg
      have hxb := eval_lt_eval_of_derivative_neg_on
        (P := f) (a := a) (b := b) ⟨hx.1.le, hx.2.le⟩ ⟨hab.le, le_rfl⟩ hx.2 hneg
      change f.eval x = 0 at hfx
      rw [hfx] at hax hxb
      exact mul_neg_of_pos_of_neg hax hxb
  · intro hsign
    obtain ⟨x, hx, hroot⟩ := polynomialIntermediateValue f hab hsign
    exact ⟨x, hx, hroot⟩

private theorem polynomialSignAtBot_eq_sign_eval_of_no_roots_Iio
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a c : R} {f : R[X]} (hc : c < a) (hf : f ≠ 0)
    (hno : ∀ z, z < a → ¬f.IsRoot z) :
    polynomialSignAtBot f = SignType.sign (f.eval c) := by
  obtain ⟨lower, hlower⟩ := bound_polynomialSignAtBot f hf
  let z := min lower c - 1
  have hzl : z ≤ lower := by dsimp [z]; linarith [min_le_left lower c]
  have hzc : z < c := by dsimp [z]; linarith [min_le_right lower c]
  have hza : z < a := hzc.trans hc
  have hsame := sign_eval_eq_of_no_root_between' polynomialIntermediateValue f
    (hno z hza) (hno c hc) (x := z) (y := c) ?_
  · exact (hlower z hzl).symm.trans hsame
  · intro x hx
    constructor
    · rintro ⟨_hzx, hxc⟩
      exact hno x (hxc.trans hc) hx
    · rintro ⟨hcx, hxz⟩
      exact (lt_asymm (hzc.trans hcx) hxz).elim

private theorem polynomialSignAtTop_eq_sign_eval_of_no_roots_Ioi
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a c : R} {f : R[X]} (hc : a < c) (hf : f ≠ 0)
    (hno : ∀ z, a < z → ¬f.IsRoot z) :
    polynomialSignAtTop f = SignType.sign (f.eval c) := by
  obtain ⟨upper, hupper⟩ := bound_polynomialSignAtTop f hf
  let z := max upper c + 1
  have huz : upper ≤ z := by dsimp [z]; linarith [le_max_left upper c]
  have hcz : c < z := by dsimp [z]; linarith [le_max_right upper c]
  have haz : a < z := hc.trans hcz
  have hsame := sign_eval_eq_of_no_root_between' polynomialIntermediateValue f
    (hno z haz) (hno c hc) (x := z) (y := c) ?_
  · exact (hupper z huz).symm.trans hsame
  · intro x hx
    constructor
    · rintro ⟨hzx, hxc⟩
      exact (not_lt_of_ge (hcz.le.trans (le_of_lt hzx))) hxc
    · rintro ⟨hcx, _hxz⟩
      exact hno x (hc.trans hcx) hx

private theorem exists_root_Iio_iff_derivative_sign_mul_eq_one
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a c : R} {f : R[X]} (hc : c < a)
    (hderiv : ∀ z, z < a → ¬f.derivative.IsRoot z) :
    (∃ x, x < a ∧ f.IsRoot x) ↔
      SignType.sign (f.derivative.eval c) * SignType.sign (f.eval a) = 1 := by
  have hdc0 : f.derivative.eval c ≠ 0 := by
    simpa only [Polynomial.IsRoot] using hderiv c hc
  have hdne : f.derivative ≠ 0 := fun h ↦ hdc0 (by simp [h])
  have hdegree : f.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hdne
  have hfne : f ≠ 0 := fun h ↦ hdegree (by simp [h])
  have hbotDeriv : polynomialSignAtBot f.derivative =
      SignType.sign (f.derivative.eval c) :=
    polynomialSignAtBot_eq_sign_eval_of_no_roots_Iio hc hdne hderiv
  have hbotF : polynomialSignAtBot f = -SignType.sign (f.derivative.eval c) := by
    rw [polynomialSignAtBot_derivative f hdegree] at hbotDeriv
    simpa using congrArg Neg.neg hbotDeriv
  constructor
  · rintro ⟨x, hxa, hfx⟩
    rcases lt_or_gt_of_ne hdc0 with hdcneg | hdcpos
    · have hneg : ∀ z ∈ Set.Ioo x a, f.derivative.eval z < 0 := by
        intro z hz
        have hs := sign_eval_eq_of_no_root_between' polynomialIntermediateValue f.derivative
          (hderiv z hz.2) (hderiv c hc) (x := z) (y := c) ?_
        · rw [sign_neg hdcneg] at hs
          exact sign_eq_neg_one_iff.mp hs
        · intro y hy
          constructor <;> rintro ⟨h₁, h₂⟩
          · exact hderiv y (h₂.trans hc) hy
          · exact hderiv y (h₂.trans hz.2) hy
      have hfa := eval_lt_eval_of_derivative_neg_on (P := f)
        (a := x) (b := a) ⟨le_rfl, hxa.le⟩ ⟨hxa.le, le_rfl⟩ hxa hneg
      change f.eval x = 0 at hfx
      rw [hfx] at hfa
      rw [sign_neg hdcneg, sign_neg hfa]
      simp
    · have hpos : ∀ z ∈ Set.Ioo x a, 0 < f.derivative.eval z := by
        intro z hz
        have hs := sign_eval_eq_of_no_root_between' polynomialIntermediateValue f.derivative
          (hderiv z hz.2) (hderiv c hc) (x := z) (y := c) ?_
        · rw [sign_pos hdcpos] at hs
          exact sign_eq_one_iff.mp hs
        · intro y hy
          constructor <;> rintro ⟨h₁, h₂⟩
          · exact hderiv y (h₂.trans hc) hy
          · exact hderiv y (h₂.trans hz.2) hy
      have hfa := eval_lt_eval_of_derivative_pos_on (P := f)
        (a := x) (b := a) ⟨le_rfl, hxa.le⟩ ⟨hxa.le, le_rfl⟩ hxa hpos
      change f.eval x = 0 at hfx
      rw [hfx] at hfa
      rw [sign_pos hdcpos, sign_pos hfa]
      simp
  · intro hsign
    obtain ⟨lower, hlower⟩ := bound_polynomialSignAtBot f hfne
    let x := min lower a - 1
    have hxl : x ≤ lower := by dsimp [x]; linarith [min_le_left lower a]
    have hxa : x < a := by dsimp [x]; linarith [min_le_right lower a]
    have hxsign : SignType.sign (f.eval x) =
        -SignType.sign (f.derivative.eval c) := (hlower x hxl).trans hbotF
    have hopposite : f.eval x * f.eval a < 0 := by
      rw [← sign_eq_neg_one_iff, sign_mul, hxsign]
      rcases lt_or_gt_of_ne hdc0 with hdcneg | hdcpos
      · rw [sign_neg hdcneg] at hsign ⊢
        simpa using congrArg Neg.neg hsign
      · rw [sign_pos hdcpos] at hsign ⊢
        simpa using hsign
    obtain ⟨z, hz, hroot⟩ := polynomialIntermediateValue f hxa hopposite
    exact ⟨z, hz.2, hroot⟩

private theorem exists_root_Ioi_iff_derivative_sign_mul_eq_neg_one
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a c : R} {f : R[X]} (hc : a < c)
    (hderiv : ∀ z, a < z → ¬f.derivative.IsRoot z) :
    (∃ x, a < x ∧ f.IsRoot x) ↔
      SignType.sign (f.derivative.eval c) * SignType.sign (f.eval a) = -1 := by
  have hdc0 : f.derivative.eval c ≠ 0 := by
    simpa only [Polynomial.IsRoot] using hderiv c hc
  have hdne : f.derivative ≠ 0 := fun h ↦ hdc0 (by simp [h])
  have hdegree : f.natDegree ≠ 0 := Polynomial.derivative_ne_zero.mp hdne
  have hfne : f ≠ 0 := fun h ↦ hdegree (by simp [h])
  have htopDeriv : polynomialSignAtTop f.derivative =
      SignType.sign (f.derivative.eval c) :=
    polynomialSignAtTop_eq_sign_eval_of_no_roots_Ioi hc hdne hderiv
  have htopF : polynomialSignAtTop f = SignType.sign (f.derivative.eval c) := by
    rwa [polynomialSignAtTop_derivative f hdegree] at htopDeriv
  constructor
  · rintro ⟨x, hax, hfx⟩
    rcases lt_or_gt_of_ne hdc0 with hdcneg | hdcpos
    · have hneg : ∀ z ∈ Set.Ioo a x, f.derivative.eval z < 0 := by
        intro z hz
        have hs := sign_eval_eq_of_no_root_between' polynomialIntermediateValue f.derivative
          (hderiv z hz.1) (hderiv c hc) (x := z) (y := c) ?_
        · rw [sign_neg hdcneg] at hs
          exact sign_eq_neg_one_iff.mp hs
        · intro y hy
          constructor <;> rintro ⟨h₁, h₂⟩
          · exact hderiv y (hz.1.trans h₁) hy
          · exact hderiv y (hc.trans h₁) hy
      have hfa := eval_lt_eval_of_derivative_neg_on (P := f)
        (a := a) (b := x) ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax hneg
      change f.eval x = 0 at hfx
      rw [hfx] at hfa
      rw [sign_neg hdcneg, sign_pos hfa]
      simp
    · have hpos : ∀ z ∈ Set.Ioo a x, 0 < f.derivative.eval z := by
        intro z hz
        have hs := sign_eval_eq_of_no_root_between' polynomialIntermediateValue f.derivative
          (hderiv z hz.1) (hderiv c hc) (x := z) (y := c) ?_
        · rw [sign_pos hdcpos] at hs
          exact sign_eq_one_iff.mp hs
        · intro y hy
          constructor <;> rintro ⟨h₁, h₂⟩
          · exact hderiv y (hz.1.trans h₁) hy
          · exact hderiv y (hc.trans h₁) hy
      have hfa := eval_lt_eval_of_derivative_pos_on (P := f)
        (a := a) (b := x) ⟨le_rfl, hax.le⟩ ⟨hax.le, le_rfl⟩ hax hpos
      change f.eval x = 0 at hfx
      rw [hfx] at hfa
      rw [sign_pos hdcpos, sign_neg hfa]
      simp
  · intro hsign
    obtain ⟨upper, hupper⟩ := bound_polynomialSignAtTop f hfne
    let x := max upper a + 1
    have hux : upper ≤ x := by dsimp [x]; linarith [le_max_left upper a]
    have hax : a < x := by dsimp [x]; linarith [le_max_right upper a]
    have hxsign : SignType.sign (f.eval x) =
        SignType.sign (f.derivative.eval c) := (hupper x hux).trans htopF
    have hopposite : f.eval a * f.eval x < 0 := by
      rw [← sign_eq_neg_one_iff, sign_mul, hxsign]
      rw [mul_comm]
      exact hsign
    obtain ⟨z, hz, hroot⟩ := polynomialIntermediateValue f hax hopposite
    exact ⟨z, hz.1, hroot⟩

private theorem isRoot_mem_familyRoots'
    {R : Type u} [Field R] [LinearOrder R] {t : ℕ}
    (q : Fin t → R[X]) (hqne : ∀ i, q i ≠ 0)
    {i : Fin t} {x : R} (hroot : (q i).IsRoot x) :
    x ∈ familyRoots q := by
  simp only [familyRoots, Finset.mem_biUnion]
  exact ⟨i, Finset.mem_univ i, by simpa using (Polynomial.mem_roots (hqne i)).2 hroot⟩

private theorem derivative_noRoot_Iio_of_ordered_qRoots_cons
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s : ℕ} (f : R[X]) (q : Fin (s + 1) → R[X])
    (hqne : ∀ i, q i ≠ 0) (hlast : q (Fin.last s) = f.derivative)
    {first : R} {rest : List R}
    (horder : (familyRoots q).sort (· ≤ ·) = first :: rest) :
    ∀ z, z < first → ¬f.derivative.IsRoot z := by
  intro z hz hroot
  have hzmem : z ∈ (familyRoots q).sort (· ≤ ·) :=
    (Finset.mem_sort (· ≤ ·)).2
      (isRoot_mem_familyRoots' q hqne (i := Fin.last s) (by simpa [hlast] using hroot))
  have hsorted : (first :: rest).SortedLT := by
    rw [← horder]
    exact (familyRoots q).sortedLT_sort
  rw [horder] at hzmem
  exact List.not_lt_head_of_sortedLT hsorted hzmem hz

private theorem derivative_noRoot_Ioo_of_ordered_qRoots_adjacent
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s : ℕ} (f : R[X]) (q : Fin (s + 1) → R[X])
    (hqne : ∀ i, q i ≠ 0) (hlast : q (Fin.last s) = f.derivative)
    {a b : R} {pre suffix : List R}
    (horder : (familyRoots q).sort (· ≤ ·) = pre ++ a :: b :: suffix) :
    ∀ z ∈ Set.Ioo a b, ¬f.derivative.IsRoot z := by
  intro z hz hroot
  have hzmem : z ∈ (familyRoots q).sort (· ≤ ·) :=
    (Finset.mem_sort (· ≤ ·)).2
      (isRoot_mem_familyRoots' q hqne (i := Fin.last s) (by simpa [hlast] using hroot))
  have hsorted : (pre ++ a :: b :: suffix).SortedLT := by
    rw [← horder]
    exact (familyRoots q).sortedLT_sort
  rw [horder] at hzmem
  exact List.not_between_adjacent_of_sortedLT hsorted hzmem hz

private theorem derivative_noRoot_Ioi_of_ordered_qRoots_last
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s : ℕ} (f : R[X]) (q : Fin (s + 1) → R[X])
    (hqne : ∀ i, q i ≠ 0) (hlast : q (Fin.last s) = f.derivative)
    {last : R} {pre : List R}
    (horder : (familyRoots q).sort (· ≤ ·) = pre ++ [last]) :
    ∀ z, last < z → ¬f.derivative.IsRoot z := by
  intro z hz hroot
  have hzmem : z ∈ (familyRoots q).sort (· ≤ ·) :=
    (Finset.mem_sort (· ≤ ·)).2
      (isRoot_mem_familyRoots' q hqne (i := Fin.last s) (by simpa [hlast] using hroot))
  have hsorted : (pre ++ [last]).SortedLT := by
    rw [← horder]
    exact (familyRoots q).sortedLT_sort
  rw [horder] at hzmem
  exact List.not_gt_last_of_sortedLT hsorted hzmem hz

private theorem lastSignAtQRoot_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (f : R[X]) (q : Fin (s + 1) → R[X])
    (r : Fin (2 * (s + 1)) → R[X])
    (hfirst : ∀ i, r (firstReducedRow i) = q i)
    (hremainder : ∀ i, r (remainderReducedRow i) = f % q i)
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ))
    (hk : k ∈ qRootIndices (rootSignTable r m degree_le)) :
    lastSignAtQRoot (rootSignTable r m degree_le) k =
      SignType.sign (f.eval (((familyRoots r).sort (· ≤ ·)).get
        (Fin.cast (by simp [rootSignTable]) k))) := by
  let w := rootSignTable r m degree_le
  have hex : ∃ i : Fin (s + 1),
      w.2 (firstReducedRow i) (w.rootColumn k) = 0 := by
    unfold qRootIndices at hk
    exact of_decide_eq_true (List.mem_filter.mp hk).2
  have hwitness :
      w.2 (firstReducedRow (qRootWitness w k)) (w.rootColumn k) = 0 := by
    rw [qRootWitness, dite_eq_left hex]
    exact Classical.choose_spec hex
  have hqeval :
      (q (qRootWitness w k)).eval (((familyRoots r).sort (· ≤ ·)).get
        (Fin.cast (by simp [rootSignTable]) k)) = 0 := by
    rw [reducedRootColumn_sign q r hfirst degree_le] at hwitness
    exact sign_eq_zero_iff.mp hwitness
  unfold lastSignAtQRoot
  rw [rootColumn_sign, hremainder, eval_mod_at_root _ _ _ hqeval]

private theorem keepQRoot_eq_true_iff
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (f : R[X]) (g : Fin s → R[X])
    (q : Fin (s + 1) → R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (hcast : ∀ i, q i.castSucc = g i)
    (hfirst : ∀ i, r (firstReducedRow i) = q i)
    (hremainder : ∀ i, r (remainderReducedRow i) = f % q i)
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ))
    (hk : k ∈ qRootIndices (rootSignTable r m degree_le)) :
    keepQRoot (rootSignTable r m degree_le) k = true ↔
      (∃ i : Fin s, (g i).IsRoot (sourceRootValue r degree_le k)) ∨
        f.IsRoot (sourceRootValue r degree_le k) := by
  rw [keepQRoot, decide_eq_true_eq]
  rw [lastSignAtQRoot_eq f q r hfirst hremainder degree_le k hk]
  simp only [sign_eq_zero_iff, sourceRootValue]
  constructor
  · rintro (⟨i, hi⟩ | hf)
    · left
      refine ⟨i, ?_⟩
      rw [reducedRootColumn_sign q r hfirst degree_le] at hi
      rw [hcast] at hi
      simpa only [Polynomial.IsRoot, sign_eq_zero_iff] using hi
    · exact Or.inr hf
  · rintro (⟨i, hi⟩ | hf)
    · left
      refine ⟨i, ?_⟩
      rw [reducedRootColumn_sign q r hfirst degree_le]
      rw [hcast]
      exact sign_eq_zero_iff.mpr hi
    · exact Or.inr hf

private noncomputable def chooseRootBelow
    {R : Type u} [Field R] [LinearOrder R] (f : R[X]) (a : R) : R := by
  classical
  exact if h : ∃ x, x < a ∧ f.IsRoot x then Classical.choose h else 0

private noncomputable def chooseRootBetween
    {R : Type u} [Field R] [LinearOrder R] (f : R[X]) (a b : R) : R := by
  classical
  exact if h : ∃ x ∈ Set.Ioo a b, f.IsRoot x then Classical.choose h else 0

private noncomputable def chooseRootAbove
    {R : Type u} [Field R] [LinearOrder R] (f : R[X]) (a : R) : R := by
  classical
  exact if h : ∃ x, a < x ∧ f.IsRoot x then Classical.choose h else 0

private noncomputable def chooseRoot
    {R : Type u} [Field R] (f : R[X]) : R := by
  classical
  exact if h : ∃ x, f.IsRoot x then Classical.choose h else 0

private theorem chooseRootBelow_spec
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a : R}
    (h : ∃ x, x < a ∧ f.IsRoot x) :
    chooseRootBelow f a < a ∧ f.IsRoot (chooseRootBelow f a) := by
  rw [chooseRootBelow, dite_eq_left h]
  exact Classical.choose_spec h

private theorem chooseRootBetween_spec
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a b : R}
    (h : ∃ x ∈ Set.Ioo a b, f.IsRoot x) :
    chooseRootBetween f a b ∈ Set.Ioo a b ∧ f.IsRoot (chooseRootBetween f a b) := by
  rw [chooseRootBetween, dite_eq_left h]
  exact Classical.choose_spec h

private theorem chooseRootAbove_spec
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a : R}
    (h : ∃ x, a < x ∧ f.IsRoot x) :
    a < chooseRootAbove f a ∧ f.IsRoot (chooseRootAbove f a) := by
  rw [chooseRootAbove, dite_eq_left h]
  exact Classical.choose_spec h

private theorem chooseRoot_spec
    {R : Type u} [Field R] {f : R[X]} (h : ∃ x, f.IsRoot x) :
    f.IsRoot (chooseRoot f) := by
  rw [chooseRoot, dite_eq_left h]
  exact Classical.choose_spec h

private theorem exists_unique_root_of_derivative_no_roots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {f : R[X]} (hderiv : ∀ x, ¬f.derivative.IsRoot x) :
    ∃! x, f.IsRoot x := by
  have hdm : f.derivative.eval (-1) ≠ 0 := by
    simpa only [Polynomial.IsRoot] using hderiv (-1)
  have hdp : f.derivative.eval 1 ≠ 0 := by
    simpa only [Polynomial.IsRoot] using hderiv 1
  have hdsign : SignType.sign (f.derivative.eval 1) =
      SignType.sign (f.derivative.eval (-1)) := by
    exact sign_eval_eq_of_no_root_between' polynomialIntermediateValue f.derivative
      (hderiv 1) (hderiv (-1)) (x := 1) (y := -1) (by
        intro z hz
        exact ⟨fun _ ↦ hderiv z hz, fun _ ↦ hderiv z hz⟩)
  have hex : ∃ x, f.IsRoot x := by
    by_cases hf0 : f.IsRoot 0
    · exact ⟨0, hf0⟩
    · have hf0' : f.eval 0 ≠ 0 := by simpa only [Polynomial.IsRoot] using hf0
      by_cases hleft :
          SignType.sign (f.derivative.eval (-1)) * SignType.sign (f.eval 0) = 1
      · obtain ⟨x, _hx, hroot⟩ :=
          (exists_root_Iio_iff_derivative_sign_mul_eq_one
            (f := f) (a := 0) (c := -1) (by norm_num)
            (fun z _hz ↦ hderiv z)).2 hleft
        exact ⟨x, hroot⟩
      · have hright :
            SignType.sign (f.derivative.eval 1) * SignType.sign (f.eval 0) = -1 := by
          rw [hdsign]
          rcases lt_or_gt_of_ne hdm with hdmneg | hdmpos
          · rcases lt_or_gt_of_ne hf0' with hfneg | hfpos
            · exfalso
              exact hleft (by simp [sign_neg hdmneg, sign_neg hfneg])
            · simp [sign_neg hdmneg, sign_pos hfpos] at hleft ⊢
          · rcases lt_or_gt_of_ne hf0' with hfneg | hfpos
            · simp [sign_pos hdmpos, sign_neg hfneg]
            · exfalso
              exact hleft (by simp [sign_pos hdmpos, sign_pos hfpos])
        obtain ⟨x, _hx, hroot⟩ :=
          (exists_root_Ioi_iff_derivative_sign_mul_eq_neg_one
            (f := f) (a := 0) (c := 1) (by norm_num)
            (fun z _hz ↦ hderiv z)).2 hright
        exact ⟨x, hroot⟩
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, hx, ?_⟩
  intro y hy
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · obtain ⟨z, _hz, hroot⟩ := exists_derivative_root_between_roots hxy hx hy
    exact (hderiv z hroot).elim
  · exact hxy.symm
  · obtain ⟨z, _hz, hroot⟩ := exists_derivative_root_between_roots hyx hy hx
    exact (hderiv z hroot).elim

private structure MatchedRoot
    {R : Type u} {s m : ℕ} (w : SignTable (2 * (s + 1)) m) where
  descriptor : ReconstructedRoot w
  value : R

private noncomputable def matchedOptionalQRoot
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (r : Fin (2 * (s + 1)) → R[X])
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ)) :
    List (MatchedRoot (R := R) (rootSignTable r m degree_le)) :=
  if keepQRoot (rootSignTable r m degree_le) k then
    [⟨reconstructedRootAtQRoot (rootSignTable r m degree_le) k,
      sourceRootValue r degree_le k⟩]
  else []

private noncomputable def matchedRootsAfter
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (f : R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (previous : Fin ((rootSignTable r m degree_le).1 : ℕ)) :
    List (Fin ((rootSignTable r m degree_le).1 : ℕ)) →
      List (MatchedRoot (R := R) (rootSignTable r m degree_le))
  | [] =>
      let w := rootSignTable r m degree_le
      let cell := qCellAfterRoot w previous
      (if derivativeSignInCell w cell * lastSignAtQRoot w previous = -1 then
        [⟨reconstructedRootInCell w cell,
          chooseRootAbove f (sourceRootValue r degree_le previous)⟩]
      else [])
  | next :: rest =>
      let w := rootSignTable r m degree_le
      let cell := qCellAfterRoot w previous
      (if lastSignAtQRoot w previous * lastSignAtQRoot w next = -1 then
        [⟨reconstructedRootInCell w cell,
          chooseRootBetween f (sourceRootValue r degree_le previous)
            (sourceRootValue r degree_le next)⟩]
      else []) ++ matchedOptionalQRoot r degree_le next ++
        matchedRootsAfter f r degree_le next rest

private noncomputable def matchedRoots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (f : R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (degree_le : ∀ i, (r i).natDegree ≤ m) :
    List (MatchedRoot (R := R) (rootSignTable r m degree_le)) :=
  let w := rootSignTable r m degree_le
  match qRootIndices w with
  | [] => [⟨reconstructedRootInCell w 0, chooseRoot f⟩]
  | first :: rest =>
      (if derivativeSignInCell w 0 * lastSignAtQRoot w first = 1 then
        [⟨reconstructedRootInCell w 0,
          chooseRootBelow f (sourceRootValue r degree_le first)⟩]
      else []) ++ matchedOptionalQRoot r degree_le first ++
        matchedRootsAfter f r degree_le first rest

private theorem matchedOptionalQRoot_descriptors
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (r : Fin (2 * (s + 1)) → R[X])
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ)) :
    (matchedOptionalQRoot r degree_le k).map MatchedRoot.descriptor =
      optionalQRoot (rootSignTable r m degree_le) k := by
  unfold matchedOptionalQRoot optionalQRoot
  split <;> simp

private theorem matchedRootsAfter_descriptors
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (f : R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (degree_le : ∀ i, (r i).natDegree ≤ m)
    (previous : Fin ((rootSignTable r m degree_le).1 : ℕ))
    (rest : List (Fin ((rootSignTable r m degree_le).1 : ℕ))) :
    (matchedRootsAfter f r degree_le previous rest).map MatchedRoot.descriptor =
      reconstructionRootsAfter (rootSignTable r m degree_le) previous rest := by
  induction rest generalizing previous with
  | nil =>
      simp only [matchedRootsAfter, reconstructionRootsAfter]
      split <;> simp
  | cons next rest ih =>
      simp only [matchedRootsAfter, reconstructionRootsAfter, List.map_append, ih,
        matchedOptionalQRoot_descriptors]
      split <;> simp

private theorem matchedRoots_descriptors
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (f : R[X]) (r : Fin (2 * (s + 1)) → R[X])
    (degree_le : ∀ i, (r i).natDegree ≤ m) :
    (matchedRoots f r degree_le).map MatchedRoot.descriptor =
      reconstructionRoots (rootSignTable r m degree_le) := by
  let w := rootSignTable r m degree_le
  cases hks : qRootIndices w with
  | nil => simp [matchedRoots, reconstructionRoots, w, hks]
  | cons first rest =>
      by_cases hleft : derivativeSignInCell w 0 * lastSignAtQRoot w first = 1
      · simp [matchedRoots, reconstructionRoots, w, hks, hleft,
          matchedOptionalQRoot_descriptors,
          matchedRootsAfter_descriptors f r degree_le first rest]
      · simp [matchedRoots, reconstructionRoots, w, hks, hleft,
          matchedOptionalQRoot_descriptors,
          matchedRootsAfter_descriptors f r degree_le first rest]

private theorem reductionDivisor_castSucc
    {R : Type u} [Field R] {s : ℕ} (p : Fin (s + 1) → R[X]) (i : Fin s) :
    reductionDivisor p i.castSucc = p i.castSucc := by
  simp [reductionDivisor]

private theorem reductionDivisor_last
    {R : Type u} [Field R] {s : ℕ} (p : Fin (s + 1) → R[X]) :
    reductionDivisor p (Fin.last s) = (p (Fin.last s)).derivative := by
  simp [reductionDivisor]

private theorem mem_familyRoots_succ_iff
    {R : Type u} [Field R] [LinearOrder R] {s : ℕ}
    (p : Fin (s + 1) → R[X]) (hne : ∀ i, p i ≠ 0) (x : R) :
    x ∈ familyRoots p ↔
      (∃ i : Fin s, (p i.castSucc).IsRoot x) ∨ (p (Fin.last s)).IsRoot x := by
  simp only [familyRoots, Finset.mem_biUnion]
  constructor
  · rintro ⟨i, _hi, hroot⟩
    have hroot' : (p i).IsRoot x := (Polynomial.mem_roots (hne i)).1 (by simpa using hroot)
    cases i using Fin.lastCases with
    | last => exact Or.inr hroot'
    | cast i => exact Or.inl ⟨i, hroot'⟩
  · rintro (⟨i, hroot⟩ | hroot)
    · exact ⟨i.castSucc, Finset.mem_univ _, by
        simpa using (Polynomial.mem_roots (hne i.castSucc)).2 hroot⟩
    · exact ⟨Fin.last s, Finset.mem_univ _, by
        simpa using (Polynomial.mem_roots (hne (Fin.last s))).2 hroot⟩

private theorem keepQRoot_eq_true_iff_mem_familyRoots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (k : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (hk : k ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le))) :
    keepQRoot (rootSignTable (reducedFamily p) m
        (reducedFamily_degree_le p m degree_le)) k = true ↔
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) k ∈
        familyRoots p := by
  let f := p (Fin.last s)
  let q := reductionDivisor p
  let r := reducedFamily p
  let rdegree := reducedFamily_degree_le p m degree_le
  have hlastne : p (Fin.last s) ≠ 0 := fun h ↦ last_nonconstant (by simp [h])
  have hpne : ∀ i, p i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => exact hlastne
    | cast i => exact first_ne_zero i
  rw [keepQRoot_eq_true_iff f (fun i ↦ p i.castSucc) q r
    (fun i ↦ reductionDivisor_castSucc p i)
    (fun i ↦ reducedFamily_firstRow p i)
    (fun i ↦ reducedFamily_remainderRow p i) rdegree k hk]
  exact (mem_familyRoots_succ_iff p hpne _).symm

private theorem reductionDivisor_ne_zero'
    {R : Type u} [Field R] [CharZero R] {s : ℕ}
    (p : Fin (s + 1) → R[X]) (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    ∀ i, reductionDivisor p i ≠ 0 := by
  intro i
  cases i using Fin.lastCases with
  | last => simpa [reductionDivisor] using Polynomial.derivative_ne_zero.mpr last_nonconstant
  | cast i => simpa [reductionDivisor] using first_ne_zero i

private theorem internal_reconstruction_condition_iff
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (previous next : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (hprevious : previous ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (hnext : next ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (pre suffix : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
      pre ++ sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le) previous ::
        sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le) next :: suffix) :
    lastSignAtQRoot (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) previous *
        lastSignAtQRoot (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) next = -1 ↔
      ∃ x ∈ Set.Ioo
        (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
        (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next),
        (p (Fin.last s)).IsRoot x := by
  let f := p (Fin.last s)
  let q := reductionDivisor p
  let r := reducedFamily p
  let rdegree := reducedFamily_degree_le p m degree_le
  have hqne : ∀ i, q i ≠ 0 := reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hsorted : (pre ++ sourceRootValue r rdegree previous ::
      sourceRootValue r rdegree next :: suffix).SortedLT := by
    rw [← horder]
    exact (familyRoots q).sortedLT_sort
  have htail : (sourceRootValue r rdegree previous ::
      sourceRootValue r rdegree next :: suffix).Pairwise (· < ·) :=
    (List.pairwise_append.mp hsorted.pairwise).2.1
  have hab : sourceRootValue r rdegree previous < sourceRootValue r rdegree next :=
    (List.pairwise_cons.mp htail).1 _ (by simp)
  have hno := derivative_noRoot_Ioo_of_ordered_qRoots_adjacent f q hqne
    (reductionDivisor_last p) horder
  rw [lastSignAtQRoot_eq f q r (fun i ↦ reducedFamily_firstRow p i)
    (fun i ↦ reducedFamily_remainderRow p i) rdegree previous hprevious]
  rw [lastSignAtQRoot_eq f q r (fun i ↦ reducedFamily_firstRow p i)
    (fun i ↦ reducedFamily_remainderRow p i) rdegree next hnext]
  exact (exists_root_Ioo_iff_sign_mul_eq_neg_one hab hno).symm

private theorem initial_reconstruction_condition_iff
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (first : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (hfirstmem : first ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (suffix : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
      sourceRootValue (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) first :: suffix) :
    derivativeSignInCell (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) 0 *
        lastSignAtQRoot (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) first = 1 ↔
      ∃ x, x < sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le) first ∧
        (p (Fin.last s)).IsRoot x := by
  let f := p (Fin.last s)
  let q := reductionDivisor p
  let r := reducedFamily p
  let rdegree := reducedFamily_degree_le p m degree_le
  have hqne : ∀ i, q i ≠ 0 := reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hc : intervalSample r rdegree 0 < sourceRootValue r rdegree first :=
    intervalSample_lt_sourceRootValue r rdegree 0 first (Nat.zero_le _)
  have hno := derivative_noRoot_Iio_of_ordered_qRoots_cons f q hqne
    (reductionDivisor_last p) horder
  rw [derivativeSignInCell_eq q r (fun i ↦ reducedFamily_firstRow p i) rdegree]
  rw [show q (Fin.last s) = f.derivative by exact reductionDivisor_last p]
  rw [lastSignAtQRoot_eq f q r (fun i ↦ reducedFamily_firstRow p i)
    (fun i ↦ reducedFamily_remainderRow p i) rdegree first hfirstmem]
  exact (exists_root_Iio_iff_derivative_sign_mul_eq_one hc hno).symm

private theorem final_reconstruction_condition_iff
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (last : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (hlastmem : last ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (pre : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++
      [sourceRootValue (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) last]) :
    derivativeSignInCell (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le))
          (qCellAfterRoot (rootSignTable (reducedFamily p) m
            (reducedFamily_degree_le p m degree_le)) last) *
        lastSignAtQRoot (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) last = -1 ↔
      ∃ x, sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le) last < x ∧
        (p (Fin.last s)).IsRoot x := by
  let f := p (Fin.last s)
  let q := reductionDivisor p
  let r := reducedFamily p
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable r m rdegree
  have hqne : ∀ i, q i ≠ 0 := reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hc : sourceRootValue r rdegree last <
      intervalSample r rdegree (qCellAfterRoot w last) :=
    sourceRootValue_lt_intervalSample r rdegree last (qCellAfterRoot w last) (by
      change (last : ℕ) < (last : ℕ) + 1
      omega)
  have hno := derivative_noRoot_Ioi_of_ordered_qRoots_last f q hqne
    (reductionDivisor_last p) horder
  rw [derivativeSignInCell_eq q r (fun i ↦ reducedFamily_firstRow p i) rdegree]
  rw [show q (Fin.last s) = f.derivative by exact reductionDivisor_last p]
  rw [lastSignAtQRoot_eq f q r (fun i ↦ reducedFamily_firstRow p i)
    (fun i ↦ reducedFamily_remainderRow p i) rdegree last hlastmem]
  exact (exists_root_Ioi_iff_derivative_sign_mul_eq_neg_one hc hno).symm

private noncomputable def semanticRootBelow
    {R : Type u} [Field R] [LinearOrder R] (f : R[X]) (a : R) : List R := by
  classical
  exact if h : ∃ x, x < a ∧ f.IsRoot x then [chooseRootBelow f a] else []

private noncomputable def semanticRootBetween
    {R : Type u} [Field R] [LinearOrder R] (f : R[X]) (a b : R) : List R := by
  classical
  exact if h : ∃ x ∈ Set.Ioo a b, f.IsRoot x then [chooseRootBetween f a b] else []

private noncomputable def semanticRootAbove
    {R : Type u} [Field R] [LinearOrder R] (f : R[X]) (a : R) : List R := by
  classical
  exact if h : ∃ x, a < x ∧ f.IsRoot x then [chooseRootAbove f a] else []

private noncomputable def semanticKeptRoot
    {R : Type u} [Field R] [LinearOrder R]
    {s : ℕ} (p : Fin (s + 1) → R[X]) (x : R) : List R :=
  if x ∈ familyRoots p then [x] else []

private noncomputable def semanticRootsAfter
    {R : Type u} [Field R] [LinearOrder R]
    {s : ℕ} (f : R[X]) (p : Fin (s + 1) → R[X]) (previous : R) :
    List R → List R
  | [] => semanticRootAbove f previous
  | next :: rest => semanticRootBetween f previous next ++
      semanticKeptRoot p next ++ semanticRootsAfter f p next rest

private noncomputable def semanticRoots
    {R : Type u} [Field R] [LinearOrder R]
    {s : ℕ} (p : Fin (s + 1) → R[X]) : List R → List R
  | [] => [chooseRoot (p (Fin.last s))]
  | first :: rest => semanticRootBelow (p (Fin.last s)) first ++
      semanticKeptRoot p first ++ semanticRootsAfter (p (Fin.last s)) p first rest

private theorem semanticRootBelow_eq_singleton
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a : R}
    (h : ∃ x, x < a ∧ f.IsRoot x) :
    semanticRootBelow f a = [chooseRootBelow f a] := by
  unfold semanticRootBelow
  rw [dite_eq_left h]

private theorem semanticRootBelow_eq_nil
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a : R}
    (h : ¬∃ x, x < a ∧ f.IsRoot x) : semanticRootBelow f a = [] := by
  unfold semanticRootBelow
  rw [dite_eq_right h]

private theorem semanticRootBetween_eq_singleton
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a b : R}
    (h : ∃ x ∈ Set.Ioo a b, f.IsRoot x) :
    semanticRootBetween f a b = [chooseRootBetween f a b] := by
  unfold semanticRootBetween
  rw [dite_eq_left h]

private theorem semanticRootBetween_eq_nil
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a b : R}
    (h : ¬∃ x ∈ Set.Ioo a b, f.IsRoot x) : semanticRootBetween f a b = [] := by
  unfold semanticRootBetween
  rw [dite_eq_right h]

private theorem semanticRootAbove_eq_singleton
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a : R}
    (h : ∃ x, a < x ∧ f.IsRoot x) :
    semanticRootAbove f a = [chooseRootAbove f a] := by
  unfold semanticRootAbove
  rw [dite_eq_left h]

private theorem semanticRootAbove_eq_nil
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a : R}
    (h : ¬∃ x, a < x ∧ f.IsRoot x) : semanticRootAbove f a = [] := by
  unfold semanticRootAbove
  rw [dite_eq_right h]

private theorem semanticKeptRoot_eq_singleton
    {R : Type u} [Field R] [LinearOrder R] {s : ℕ}
    {p : Fin (s + 1) → R[X]} {x : R} (h : x ∈ familyRoots p) :
    semanticKeptRoot p x = [x] := by simp [semanticKeptRoot, h]

private theorem semanticKeptRoot_eq_nil
    {R : Type u} [Field R] [LinearOrder R] {s : ℕ}
    {p : Fin (s + 1) → R[X]} {x : R} (h : x ∉ familyRoots p) :
    semanticKeptRoot p x = [] := by simp [semanticKeptRoot, h]

private theorem isRoot_eq_of_derivative_noRoot_Iio
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a x y : R} {f : R[X]} (hno : ∀ z, z < a → ¬f.derivative.IsRoot z)
    (hx : x < a) (hy : y < a) (hfx : f.IsRoot x) (hfy : f.IsRoot y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · obtain ⟨z, hz, hroot⟩ := exists_derivative_root_between_roots hxy hfx hfy
    exact (hno z (hz.2.trans hy) hroot).elim
  · exact hxy
  · obtain ⟨z, hz, hroot⟩ := exists_derivative_root_between_roots hyx hfy hfx
    exact (hno z (hz.2.trans hx) hroot).elim

private theorem isRoot_eq_of_derivative_noRoot_Ioi
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {a x y : R} {f : R[X]} (hno : ∀ z, a < z → ¬f.derivative.IsRoot z)
    (hx : a < x) (hy : a < y) (hfx : f.IsRoot x) (hfy : f.IsRoot y) : x = y := by
  rcases lt_trichotomy x y with hxy | hxy | hyx
  · obtain ⟨z, hz, hroot⟩ := exists_derivative_root_between_roots hxy hfx hfy
    exact (hno z (hx.trans hz.1) hroot).elim
  · exact hxy
  · obtain ⟨z, hz, hroot⟩ := exists_derivative_root_between_roots hyx hfy hfx
    exact (hno z (hy.trans hz.1) hroot).elim

private theorem mem_semanticRootBelow_iff
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a x : R}
    (hunique : ∀ {x y}, x < a → y < a → f.IsRoot x → f.IsRoot y → x = y) :
    x ∈ semanticRootBelow f a ↔ x < a ∧ f.IsRoot x := by
  by_cases hex : ∃ y, y < a ∧ f.IsRoot y
  · rw [semanticRootBelow_eq_singleton hex]
    simp only [List.mem_singleton]
    have hs := chooseRootBelow_spec hex
    constructor
    · rintro rfl
      exact hs
    · intro hx
      exact hunique hx.1 hs.1 hx.2 hs.2
  · rw [semanticRootBelow_eq_nil hex]
    simp only [List.not_mem_nil, false_iff]
    exact fun hx ↦ hex ⟨x, hx⟩

private theorem mem_semanticRootBetween_iff
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a b x : R}
    (hunique : ∀ {x y}, x ∈ Set.Ioo a b → y ∈ Set.Ioo a b →
      f.IsRoot x → f.IsRoot y → x = y) :
    x ∈ semanticRootBetween f a b ↔ x ∈ Set.Ioo a b ∧ f.IsRoot x := by
  by_cases hex : ∃ y ∈ Set.Ioo a b, f.IsRoot y
  · rw [semanticRootBetween_eq_singleton hex]
    simp only [List.mem_singleton]
    have hs := chooseRootBetween_spec hex
    constructor
    · rintro rfl
      exact hs
    · intro hx
      exact hunique hx.1 hs.1 hx.2 hs.2
  · rw [semanticRootBetween_eq_nil hex]
    simp only [List.not_mem_nil, false_iff]
    exact fun hx ↦ hex ⟨x, hx.1, hx.2⟩

private theorem mem_semanticRootAbove_iff
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a x : R}
    (hunique : ∀ {x y}, a < x → a < y → f.IsRoot x → f.IsRoot y → x = y) :
    x ∈ semanticRootAbove f a ↔ a < x ∧ f.IsRoot x := by
  by_cases hex : ∃ y, a < y ∧ f.IsRoot y
  · rw [semanticRootAbove_eq_singleton hex]
    simp only [List.mem_singleton]
    have hs := chooseRootAbove_spec hex
    constructor
    · rintro rfl
      exact hs
    · intro hx
      exact hunique hx.1 hs.1 hx.2 hs.2
  · rw [semanticRootAbove_eq_nil hex]
    simp only [List.not_mem_nil, false_iff]
    exact fun hx ↦ hex ⟨x, hx⟩

private theorem mem_semanticKeptRoot_iff
    {R : Type u} [Field R] [LinearOrder R] {s : ℕ}
    {p : Fin (s + 1) → R[X]} {a x : R} :
    x ∈ semanticKeptRoot p a ↔ x = a ∧ a ∈ familyRoots p := by
  by_cases ha : a ∈ familyRoots p
  · rw [semanticKeptRoot_eq_singleton ha]
    simp [ha]
  · rw [semanticKeptRoot_eq_nil ha]
    simp [ha]

private theorem semanticRootBelow_sortedLT
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a : R} :
    (semanticRootBelow f a).SortedLT := by
  unfold semanticRootBelow
  split <;> apply List.Pairwise.sortedLT <;> simp

private theorem semanticRootBetween_sortedLT
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a b : R} :
    (semanticRootBetween f a b).SortedLT := by
  unfold semanticRootBetween
  split <;> apply List.Pairwise.sortedLT <;> simp

private theorem semanticRootAbove_sortedLT
    {R : Type u} [Field R] [LinearOrder R] {f : R[X]} {a : R} :
    (semanticRootAbove f a).SortedLT := by
  unfold semanticRootAbove
  split <;> apply List.Pairwise.sortedLT <;> simp

private theorem semanticKeptRoot_sortedLT
    {R : Type u} [Field R] [LinearOrder R] {s : ℕ}
    {p : Fin (s + 1) → R[X]} {a : R} :
    (semanticKeptRoot p a).SortedLT := by
  unfold semanticKeptRoot
  split <;> apply List.Pairwise.sortedLT <;> simp

private theorem matchedRootsAfter_values_eq_semantic
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (previous : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (rest : List (Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ)))
    (hprevious : previous ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (hrest : ∀ k ∈ rest, k ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (pre : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous ::
        rest.map (sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le))) :
    (matchedRootsAfter (p (Fin.last s)) (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) previous rest).map MatchedRoot.value =
      semanticRootsAfter (p (Fin.last s)) p
        (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
        (rest.map (sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le))) := by
  induction rest generalizing previous pre with
  | nil =>
      have hcondition := final_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant previous hprevious pre (by simpa using horder)
      simp only [matchedRootsAfter]
      change _ = semanticRootAbove (p (Fin.last s))
        (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
      by_cases hc : derivativeSignInCell
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          (qCellAfterRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) previous) *
          lastSignAtQRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
            previous = -1
      · have hex := hcondition.mp hc
        rw [semanticRootAbove_eq_singleton hex]
        simp [hc]
      · have hnex : ¬∃ x, sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le) previous < x ∧
            (p (Fin.last s)).IsRoot x := fun h ↦ hc (hcondition.mpr h)
        rw [semanticRootAbove_eq_nil hnex]
        simp [hc]
  | cons next rest ih =>
      have hnext : next ∈ qRootIndices (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) := hrest next (by simp)
      have htail : ∀ k ∈ rest, k ∈ qRootIndices (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) := by
        intro k hk
        exact hrest k (by simp [hk])
      have hcondition := internal_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant previous next hprevious hnext pre
        (rest.map (sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le))) (by simpa using horder)
      have horderTail : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
          (pre ++ [sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le) previous]) ++
          sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le) next ::
            rest.map (sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le)) := by
        simpa [List.append_assoc] using horder
      have ih' := ih next hnext htail _ horderTail
      have hkeep := keepQRoot_eq_true_iff_mem_familyRoots p degree_le first_ne_zero
        last_nonconstant next hnext
      simp only [matchedRootsAfter, List.map_append, ih']
      change _ = semanticRootBetween (p (Fin.last s))
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next) ++
        semanticKeptRoot p
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next) ++
        semanticRootsAfter (p (Fin.last s)) p
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next)
          (rest.map (sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le)))
      by_cases hc : lastSignAtQRoot
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) previous *
          lastSignAtQRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) next = -1
      · have hex := hcondition.mp hc
        by_cases hk : keepQRoot (rootSignTable (reducedFamily p) m
            (reducedFamily_degree_le p m degree_le)) next = true
        · have hmem := hkeep.mp hk
          rw [semanticRootBetween_eq_singleton hex, semanticKeptRoot_eq_singleton hmem]
          simp [hc, matchedOptionalQRoot, hk]
        · have hnmem : sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le) next ∉ familyRoots p :=
            fun h ↦ hk (hkeep.mpr h)
          rw [semanticRootBetween_eq_singleton hex, semanticKeptRoot_eq_nil hnmem]
          simp [hc, matchedOptionalQRoot, hk]
      · have hnex : ¬∃ x ∈ Set.Ioo
            (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
            (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next),
            (p (Fin.last s)).IsRoot x := fun h ↦ hc (hcondition.mpr h)
        by_cases hk : keepQRoot (rootSignTable (reducedFamily p) m
            (reducedFamily_degree_le p m degree_le)) next = true
        · have hmem := hkeep.mp hk
          rw [semanticRootBetween_eq_nil hnex, semanticKeptRoot_eq_singleton hmem]
          simp [hc, matchedOptionalQRoot, hk]
        · have hnmem : sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le) next ∉ familyRoots p :=
            fun h ↦ hk (hkeep.mpr h)
          rw [semanticRootBetween_eq_nil hnex, semanticKeptRoot_eq_nil hnmem]
          simp [hc, matchedOptionalQRoot, hk]

private theorem matchedRoots_values_eq_semantic
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    (matchedRoots (p (Fin.last s)) (reducedFamily p)
        (reducedFamily_degree_le p m degree_le)).map MatchedRoot.value =
      semanticRoots p ((familyRoots (reductionDivisor p)).sort (· ≤ ·)) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hvalues := qRootValues_eq (reductionDivisor p) (reducedFamily p)
    (fun i ↦ reducedFamily_firstRow p i) hqne rdegree
  cases hks : qRootIndices w with
  | nil =>
      have hqnil : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = [] := by
        simpa [w, hks, sourceRootValue] using hvalues.symm
      simp [matchedRoots, semanticRoots, w, hks, hqnil]
  | cons first rest =>
      have hfirstmem : first ∈ qRootIndices w := by simp [hks]
      have hrestmem : ∀ k ∈ rest, k ∈ qRootIndices w := by
        intro k hk
        rw [hks]
        simp [hk]
      have horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
          sourceRootValue (reducedFamily p) rdegree first ::
            rest.map (sourceRootValue (reducedFamily p) rdegree) := by
        rw [← hvalues]
        simp only [w, hks, List.map_cons]
        rfl
      have hafter := matchedRootsAfter_values_eq_semantic p degree_le first_ne_zero
        last_nonconstant first rest hfirstmem hrestmem [] (by simpa using horder)
      have hcondition := initial_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant first hfirstmem
        (rest.map (sourceRootValue (reducedFamily p) rdegree)) horder
      have hkeep := keepQRoot_eq_true_iff_mem_familyRoots p degree_le first_ne_zero
        last_nonconstant first hfirstmem
      rw [horder]
      change (matchedRoots (p (Fin.last s)) (reducedFamily p) rdegree).map
          MatchedRoot.value = _
      simp only [matchedRoots, w, hks, List.map_append, hafter]
      change _ = semanticRootBelow (p (Fin.last s))
          (sourceRootValue (reducedFamily p) rdegree first) ++
        semanticKeptRoot p (sourceRootValue (reducedFamily p) rdegree first) ++
        semanticRootsAfter (p (Fin.last s)) p
          (sourceRootValue (reducedFamily p) rdegree first)
          (rest.map (sourceRootValue (reducedFamily p) rdegree))
      by_cases hc : derivativeSignInCell w 0 * lastSignAtQRoot w first = 1
      · have hex := hcondition.mp hc
        by_cases hk : keepQRoot w first = true
        · have hmem := hkeep.mp hk
          rw [semanticRootBelow_eq_singleton hex, semanticKeptRoot_eq_singleton hmem]
          simp [hc, matchedOptionalQRoot, w, hk]
        · have hnmem : sourceRootValue (reducedFamily p) rdegree first ∉ familyRoots p :=
            fun h ↦ hk (hkeep.mpr h)
          rw [semanticRootBelow_eq_singleton hex, semanticKeptRoot_eq_nil hnmem]
          simp [hc, matchedOptionalQRoot, w, hk]
      · have hnex : ¬∃ x, x < sourceRootValue (reducedFamily p) rdegree first ∧
            (p (Fin.last s)).IsRoot x := fun h ↦ hc (hcondition.mpr h)
        by_cases hk : keepQRoot w first = true
        · have hmem := hkeep.mp hk
          rw [semanticRootBelow_eq_nil hnex, semanticKeptRoot_eq_singleton hmem]
          simp [hc, matchedOptionalQRoot, w, hk]
        · have hnmem : sourceRootValue (reducedFamily p) rdegree first ∉ familyRoots p :=
            fun h ↦ hk (hkeep.mpr h)
          rw [semanticRootBelow_eq_nil hnex, semanticKeptRoot_eq_nil hnmem]
          simp [hc, matchedOptionalQRoot, w, hk]

private theorem earlierRoot_mem_reductionRoots
    {R : Type u} [Field R] [LinearOrder R] [CharZero R] {s : ℕ}
    (p : Fin (s + 1) → R[X])
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    {i : Fin s} {x : R} (hroot : (p i.castSucc).IsRoot x) :
    x ∈ familyRoots (reductionDivisor p) := by
  apply isRoot_mem_familyRoots' (reductionDivisor p)
    (reductionDivisor_ne_zero' p first_ne_zero last_nonconstant) (i := i.castSucc)
  rw [reductionDivisor_castSucc]
  exact hroot

private theorem semanticRootsAfter_spec
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s : ℕ} (p : Fin (s + 1) → R[X])
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (previous : R) (rest pre : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
      pre ++ previous :: rest) :
    (semanticRootsAfter (p (Fin.last s)) p previous rest).SortedLT ∧
      ∀ x, x ∈ semanticRootsAfter (p (Fin.last s)) p previous rest ↔
        x ∈ familyRoots p ∧ previous < x := by
  have hlastne : p (Fin.last s) ≠ 0 := fun h ↦ last_nonconstant (by simp [h])
  have hpne : ∀ i, p i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => exact hlastne
    | cast i => exact first_ne_zero i
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  induction rest generalizing previous pre with
  | nil =>
      have horder' : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++ [previous] := by
        simpa using horder
      have hno := derivative_noRoot_Ioi_of_ordered_qRoots_last
        (p (Fin.last s)) (reductionDivisor p) hqne (reductionDivisor_last p) horder'
      have hunique : ∀ {x y}, previous < x → previous < y →
          (p (Fin.last s)).IsRoot x → (p (Fin.last s)).IsRoot y → x = y :=
        fun hx hy hfx hfy ↦ isRoot_eq_of_derivative_noRoot_Ioi hno hx hy hfx hfy
      change (semanticRootAbove (p (Fin.last s)) previous).SortedLT ∧
        ∀ x, x ∈ semanticRootAbove (p (Fin.last s)) previous ↔
          x ∈ familyRoots p ∧ previous < x
      refine ⟨semanticRootAbove_sortedLT, ?_⟩
      intro x
      rw [mem_semanticRootAbove_iff hunique]
      constructor
      · rintro ⟨hpx, hroot⟩
        exact ⟨isRoot_mem_familyRoots' p hpne hroot, hpx⟩
      · rintro ⟨hxold, hpx⟩
        rcases (mem_familyRoots_succ_iff p hpne x).1 hxold with ⟨i, hroot⟩ | hroot
        · have hxq : x ∈ (familyRoots (reductionDivisor p)).sort (· ≤ ·) :=
            (Finset.mem_sort (· ≤ ·)).2
              (earlierRoot_mem_reductionRoots p first_ne_zero last_nonconstant hroot)
          rw [horder'] at hxq
          exact (List.not_gt_last_of_sortedLT (by
            rw [← horder']
            exact (familyRoots (reductionDivisor p)).sortedLT_sort) hxq hpx).elim
        · exact ⟨hpx, hroot⟩
  | cons next rest ih =>
      have hsortedQ : (pre ++ previous :: next :: rest).SortedLT := by
        rw [← horder]
        exact (familyRoots (reductionDivisor p)).sortedLT_sort
      have htailPair : (previous :: next :: rest).Pairwise (· < ·) :=
        (List.pairwise_append.mp hsortedQ.pairwise).2.1
      have hpnext : previous < next :=
        (List.pairwise_cons.mp htailPair).1 next (by simp)
      have horderTail : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
          (pre ++ [previous]) ++ next :: rest := by
        simpa [List.append_assoc] using horder
      have ih' := ih next (pre ++ [previous]) horderTail
      have hno := derivative_noRoot_Ioo_of_ordered_qRoots_adjacent
        (p (Fin.last s)) (reductionDivisor p) hqne (reductionDivisor_last p)
        (pre := pre) (suffix := rest) horder
      have hunique : ∀ {x y}, x ∈ Set.Ioo previous next → y ∈ Set.Ioo previous next →
          (p (Fin.last s)).IsRoot x → (p (Fin.last s)).IsRoot y → x = y := by
        intro x y hx hy hfx hfy
        exact isRoot_injective_on_of_derivative_noRoot hno hx hy hfx hfy
      let between := semanticRootBetween (p (Fin.last s)) previous next
      let kept := semanticKeptRoot p next
      let tail := semanticRootsAfter (p (Fin.last s)) p next rest
      have hbetweenMem : ∀ x, x ∈ between ↔
          x ∈ Set.Ioo previous next ∧ (p (Fin.last s)).IsRoot x :=
        fun x ↦ mem_semanticRootBetween_iff hunique
      have hkeptMem : ∀ x, x ∈ kept ↔ x = next ∧ next ∈ familyRoots p :=
        fun x ↦ mem_semanticKeptRoot_iff
      have htailMem : ∀ x, x ∈ tail ↔ x ∈ familyRoots p ∧ next < x := ih'.2
      have hbetweenSorted : between.SortedLT := semanticRootBetween_sortedLT
      have hkeptSorted : kept.SortedLT := semanticKeptRoot_sortedLT
      have htailSorted : tail.SortedLT := ih'.1
      have hkeptTailPair : (kept ++ tail).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨hkeptSorted.pairwise, htailSorted.pairwise, ?_⟩
        intro x hx y hy
        have hx' := (hkeptMem x).1 hx
        rw [hx'.1]
        exact (htailMem y).1 hy |>.2
      have hallPair : (between ++ (kept ++ tail)).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨hbetweenSorted.pairwise, hkeptTailPair, ?_⟩
        intro x hx y hy
        have hx' := (hbetweenMem x).1 hx
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · have hy' := (hkeptMem y).1 hy
          rw [hy'.1]
          exact hx'.1.2
        · exact hx'.1.2.trans ((htailMem y).1 hy).2
      change (between ++ kept ++ tail).SortedLT ∧ _
      refine ⟨by simpa [List.append_assoc] using hallPair.sortedLT, ?_⟩
      intro x
      change x ∈ between ++ kept ++ tail ↔ x ∈ familyRoots p ∧ previous < x
      rw [List.mem_append, List.mem_append, hbetweenMem x, hkeptMem x, htailMem x]
      constructor
      · rintro ((⟨hxcell, hroot⟩ | ⟨rfl, hxold⟩) | ⟨hxold, hnextx⟩)
        · exact ⟨isRoot_mem_familyRoots' p hpne hroot, hxcell.1⟩
        · exact ⟨hxold, hpnext⟩
        · exact ⟨hxold, hpnext.trans hnextx⟩
      · rintro ⟨hxold, hprevx⟩
        rcases lt_trichotomy x next with hxnext | rfl | hnextx
        · exact Or.inl (Or.inl ⟨⟨hprevx, hxnext⟩, by
            rcases (mem_familyRoots_succ_iff p hpne x).1 hxold with ⟨i, hroot⟩ | hroot
            · have hxq : x ∈ (familyRoots (reductionDivisor p)).sort (· ≤ ·) :=
                (Finset.mem_sort (· ≤ ·)).2
                  (earlierRoot_mem_reductionRoots p first_ne_zero last_nonconstant hroot)
              rw [horder] at hxq
              exact (List.not_between_adjacent_of_sortedLT hsortedQ hxq
                ⟨hprevx, hxnext⟩).elim
            · exact hroot⟩)
        · exact Or.inl (Or.inr ⟨rfl, hxold⟩)
        · exact Or.inr ⟨hxold, hnextx⟩

private theorem semanticRoots_spec
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s : ℕ} (p : Fin (s + 1) → R[X])
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    let qroots := (familyRoots (reductionDivisor p)).sort (· ≤ ·)
    (semanticRoots p qroots).SortedLT ∧
      ∀ x, x ∈ semanticRoots p qroots ↔ x ∈ familyRoots p := by
  let qroots := (familyRoots (reductionDivisor p)).sort (· ≤ ·)
  have hlastne : p (Fin.last s) ≠ 0 := fun h ↦ last_nonconstant (by simp [h])
  have hpne : ∀ i, p i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => exact hlastne
    | cast i => exact first_ne_zero i
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  change (semanticRoots p qroots).SortedLT ∧
    ∀ x, x ∈ semanticRoots p qroots ↔ x ∈ familyRoots p
  cases hq : qroots with
  | nil =>
      have hderiv : ∀ x, ¬(p (Fin.last s)).derivative.IsRoot x := by
        intro x hroot
        have hxq : x ∈ qroots := by
          dsimp [qroots]
          exact (Finset.mem_sort (· ≤ ·)).2
            (isRoot_mem_familyRoots' (reductionDivisor p) hqne (i := Fin.last s)
              (by simpa [reductionDivisor_last] using hroot))
        rw [hq] at hxq
        simp at hxq
      obtain ⟨root, hroot, hunique⟩ :=
        exists_unique_root_of_derivative_no_roots hderiv
      have hchoose : (p (Fin.last s)).IsRoot (chooseRoot (p (Fin.last s))) :=
        chooseRoot_spec ⟨root, hroot⟩
      change [chooseRoot (p (Fin.last s))].SortedLT ∧
        ∀ x, x ∈ [chooseRoot (p (Fin.last s))] ↔ x ∈ familyRoots p
      refine ⟨(by apply List.Pairwise.sortedLT; simp), ?_⟩
      intro x
      simp only [List.mem_singleton]
      constructor
      · rintro rfl
        exact isRoot_mem_familyRoots' p hpne hchoose
      · intro hxold
        rcases (mem_familyRoots_succ_iff p hpne x).1 hxold with ⟨i, hrooti⟩ | hrootx
        · have hxq : x ∈ qroots := by
            dsimp [qroots]
            exact (Finset.mem_sort (· ≤ ·)).2
              (earlierRoot_mem_reductionRoots p first_ne_zero last_nonconstant hrooti)
          rw [hq] at hxq
          simp at hxq
        · exact hunique x hrootx |>.trans (hunique _ hchoose).symm
  | cons first rest =>
      have horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = first :: rest := by
        simpa [qroots] using hq
      have hno := derivative_noRoot_Iio_of_ordered_qRoots_cons
        (p (Fin.last s)) (reductionDivisor p) hqne (reductionDivisor_last p) horder
      have hunique : ∀ {x y}, x < first → y < first →
          (p (Fin.last s)).IsRoot x → (p (Fin.last s)).IsRoot y → x = y :=
        fun hx hy hfx hfy ↦ isRoot_eq_of_derivative_noRoot_Iio hno hx hy hfx hfy
      have htail := semanticRootsAfter_spec p first_ne_zero last_nonconstant
        first rest [] (by simpa using horder)
      let below := semanticRootBelow (p (Fin.last s)) first
      let kept := semanticKeptRoot p first
      let tail := semanticRootsAfter (p (Fin.last s)) p first rest
      have hbelowMem : ∀ x, x ∈ below ↔ x < first ∧ (p (Fin.last s)).IsRoot x :=
        fun x ↦ mem_semanticRootBelow_iff hunique
      have hkeptMem : ∀ x, x ∈ kept ↔ x = first ∧ first ∈ familyRoots p :=
        fun x ↦ mem_semanticKeptRoot_iff
      have htailMem : ∀ x, x ∈ tail ↔ x ∈ familyRoots p ∧ first < x := htail.2
      have hkeptTailPair : (kept ++ tail).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨semanticKeptRoot_sortedLT.pairwise, htail.1.pairwise, ?_⟩
        intro x hx y hy
        have hx' := (hkeptMem x).1 hx
        rw [hx'.1]
        exact (htailMem y).1 hy |>.2
      have hallPair : (below ++ (kept ++ tail)).Pairwise (· < ·) := by
        apply List.pairwise_append.mpr
        refine ⟨semanticRootBelow_sortedLT.pairwise, hkeptTailPair, ?_⟩
        intro x hx y hy
        have hx' := (hbelowMem x).1 hx
        rw [List.mem_append] at hy
        rcases hy with hy | hy
        · have hy' := (hkeptMem y).1 hy
          rw [hy'.1]
          exact hx'.1
        · exact hx'.1.trans ((htailMem y).1 hy).2
      change (below ++ kept ++ tail).SortedLT ∧
        ∀ x, x ∈ below ++ kept ++ tail ↔ x ∈ familyRoots p
      refine ⟨by simpa [List.append_assoc] using hallPair.sortedLT, ?_⟩
      intro x
      rw [List.mem_append, List.mem_append, hbelowMem x, hkeptMem x, htailMem x]
      constructor
      · rintro ((⟨_hxfirst, hroot⟩ | ⟨rfl, hxold⟩) | ⟨hxold, _hfirstx⟩)
        · exact isRoot_mem_familyRoots' p hpne hroot
        · exact hxold
        · exact hxold
      · intro hxold
        rcases lt_trichotomy x first with hxfirst | rfl | hfirstx
        · exact Or.inl (Or.inl ⟨hxfirst, by
            rcases (mem_familyRoots_succ_iff p hpne x).1 hxold with ⟨i, hroot⟩ | hroot
            · have hxq : x ∈ (familyRoots (reductionDivisor p)).sort (· ≤ ·) :=
                (Finset.mem_sort (· ≤ ·)).2
                  (earlierRoot_mem_reductionRoots p first_ne_zero last_nonconstant hroot)
              rw [horder] at hxq
              exact (List.not_lt_head_of_sortedLT (by
                rw [← horder]
                exact (familyRoots (reductionDivisor p)).sortedLT_sort) hxq hxfirst).elim
            · exact hroot⟩)
        · exact Or.inl (Or.inr ⟨rfl, hxold⟩)
        · exact Or.inr ⟨hxold, hfirstx⟩

private theorem semanticRoots_eq_ordered_familyRoots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s : ℕ} (p : Fin (s + 1) → R[X])
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    semanticRoots p ((familyRoots (reductionDivisor p)).sort (· ≤ ·)) =
      (familyRoots p).sort (· ≤ ·) := by
  have hsemantic := semanticRoots_spec p first_ne_zero last_nonconstant
  apply hsemantic.1.eq_of_mem_iff (familyRoots p).sortedLT_sort
  intro x
  rw [hsemantic.2 x, Finset.mem_sort]

private theorem matchedRoots_values_eq_ordered_familyRoots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    (matchedRoots (p (Fin.last s)) (reducedFamily p)
        (reducedFamily_degree_le p m degree_le)).map MatchedRoot.value =
      (familyRoots p).sort (· ≤ ·) := by
  rw [matchedRoots_values_eq_semantic p degree_le first_ne_zero last_nonconstant]
  exact semanticRoots_eq_ordered_familyRoots p first_ne_zero last_nonconstant

private theorem sign_eval_eq_of_no_familyRoot_Ioo
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {t : ℕ} (q : Fin t → R[X]) (hqne : ∀ i, q i ≠ 0)
    {a b x y : R} (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b)
    (hno : ∀ z ∈ Set.Ioo a b, z ∉ familyRoots q) (i : Fin t) :
    SignType.sign ((q i).eval x) = SignType.sign ((q i).eval y) := by
  apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue (q i)
  · exact fun hroot ↦ hno x hx (isRoot_mem_familyRoots' q hqne hroot)
  · exact fun hroot ↦ hno y hy (isRoot_mem_familyRoots' q hqne hroot)
  · intro z hroot
    have hzq := isRoot_mem_familyRoots' q hqne hroot
    constructor
    · rintro ⟨hxz, hzy⟩
      exact hno z ⟨lt_trans hx.1 hxz, lt_trans hzy hy.2⟩ hzq
    · rintro ⟨hyz, hzx⟩
      exact hno z ⟨lt_trans hy.1 hyz, lt_trans hzx hx.2⟩ hzq

private theorem sign_eval_eq_of_no_familyRoot_Iio
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {t : ℕ} (q : Fin t → R[X]) (hqne : ∀ i, q i ≠ 0)
    {a x y : R} (hx : x < a) (hy : y < a)
    (hno : ∀ z, z < a → z ∉ familyRoots q) (i : Fin t) :
    SignType.sign ((q i).eval x) = SignType.sign ((q i).eval y) := by
  apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue (q i)
  · exact fun hroot ↦ hno x hx (isRoot_mem_familyRoots' q hqne hroot)
  · exact fun hroot ↦ hno y hy (isRoot_mem_familyRoots' q hqne hroot)
  · intro z hroot
    have hzq := isRoot_mem_familyRoots' q hqne hroot
    constructor
    · rintro ⟨_hxz, hzy⟩
      exact hno z (hzy.trans hy) hzq
    · rintro ⟨_hyz, hzx⟩
      exact hno z (hzx.trans hx) hzq

private theorem sign_eval_eq_of_no_familyRoot_Ioi
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {t : ℕ} (q : Fin t → R[X]) (hqne : ∀ i, q i ≠ 0)
    {a x y : R} (hx : a < x) (hy : a < y)
    (hno : ∀ z, a < z → z ∉ familyRoots q) (i : Fin t) :
    SignType.sign ((q i).eval x) = SignType.sign ((q i).eval y) := by
  apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue (q i)
  · exact fun hroot ↦ hno x hx (isRoot_mem_familyRoots' q hqne hroot)
  · exact fun hroot ↦ hno y hy (isRoot_mem_familyRoots' q hqne hroot)
  · intro z hroot
    have hzq := isRoot_mem_familyRoots' q hqne hroot
    constructor
    · rintro ⟨hxz, _hzy⟩
      exact hno z (hx.trans hxz) hzq
    · rintro ⟨hyz, _hzx⟩
      exact hno z (hy.trans hyz) hzq

private theorem sign_eval_eq_of_no_familyRoot
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {t : ℕ} (q : Fin t → R[X]) (hqne : ∀ i, q i ≠ 0)
    (hno : familyRoots q = ∅) (x y : R) (i : Fin t) :
    SignType.sign ((q i).eval x) = SignType.sign ((q i).eval y) := by
  apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue (q i)
  · intro hroot
    have := isRoot_mem_familyRoots' q hqne hroot
    simp [hno] at this
  · intro hroot
    have := isRoot_mem_familyRoots' q hqne hroot
    simp [hno] at this
  · intro z hroot
    have hz := isRoot_mem_familyRoots' q hqne hroot
    simp [hno] at hz

private theorem no_familyRoot_Iio_of_ordered_cons
    {R : Type u} [Field R] [LinearOrder R] {t : ℕ}
    (q : Fin t → R[X]) {first : R} {rest : List R}
    (horder : (familyRoots q).sort (· ≤ ·) = first :: rest) :
    ∀ z, z < first → z ∉ familyRoots q := by
  intro z hz hzmem
  have hzmem' : z ∈ first :: rest := by
    rw [← horder]
    exact (Finset.mem_sort (· ≤ ·)).2 hzmem
  have hsorted : (first :: rest).SortedLT := by
    rw [← horder]
    exact (familyRoots q).sortedLT_sort
  exact List.not_lt_head_of_sortedLT hsorted hzmem' hz

private theorem no_familyRoot_Ioo_of_ordered_adjacent
    {R : Type u} [Field R] [LinearOrder R] {t : ℕ}
    (q : Fin t → R[X]) {a b : R} {pre suffix : List R}
    (horder : (familyRoots q).sort (· ≤ ·) = pre ++ a :: b :: suffix) :
    ∀ z ∈ Set.Ioo a b, z ∉ familyRoots q := by
  intro z hz hzmem
  have hzmem' : z ∈ pre ++ a :: b :: suffix := by
    rw [← horder]
    exact (Finset.mem_sort (· ≤ ·)).2 hzmem
  have hsorted : (pre ++ a :: b :: suffix).SortedLT := by
    rw [← horder]
    exact (familyRoots q).sortedLT_sort
  exact List.not_between_adjacent_of_sortedLT hsorted hzmem' hz

private theorem no_familyRoot_Ioi_of_ordered_last
    {R : Type u} [Field R] [LinearOrder R] {t : ℕ}
    (q : Fin t → R[X]) {last : R} {pre : List R}
    (horder : (familyRoots q).sort (· ≤ ·) = pre ++ [last]) :
    ∀ z, last < z → z ∉ familyRoots q := by
  intro z hz hzmem
  have hzmem' : z ∈ pre ++ [last] := by
    rw [← horder]
    exact (Finset.mem_sort (· ≤ ·)).2 hzmem
  have hsorted : (pre ++ [last]).SortedLT := by
    rw [← horder]
    exact (familyRoots q).sortedLT_sort
  exact List.not_gt_last_of_sortedLT hsorted hzmem' hz

private theorem reconstructedRootSigns_at_qRoot
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (k : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (hk : k ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le))) :
    reconstructedRootSigns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
        (reconstructedRootAtQRoot
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) k) =
      fun i ↦ SignType.sign ((p i).eval
        (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) k)) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [reconstructedRootSigns, reconstructedRootAtQRoot, Fin.lastCases_last]
      exact lastSignAtQRoot_eq (p (Fin.last s)) (reductionDivisor p) (reducedFamily p)
        (fun i ↦ reducedFamily_firstRow p i) (fun i ↦ reducedFamily_remainderRow p i)
        rdegree k hk
  | cast i =>
      simp only [reconstructedRootSigns, reconstructedRootAtQRoot, Fin.lastCases_castSucc]
      rw [reducedRootColumn_sign (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree i.castSucc k]
      simp only [reductionDivisor_castSucc, sourceRootValue]

private theorem reconstructedRootSigns_below
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (first : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (rest : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) first :: rest)
    (hex : ∃ x, x < sourceRootValue (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) first ∧ (p (Fin.last s)).IsRoot x) :
    reconstructedRootSigns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
        (reconstructedRootInCell
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) 0) =
      fun i ↦ SignType.sign ((p i).eval
        (chooseRootBelow (p (Fin.last s))
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) first))) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hno := no_familyRoot_Iio_of_ordered_cons (reductionDivisor p) horder
  have hchoice := chooseRootBelow_spec hex
  have hsample : intervalSample (reducedFamily p) rdegree 0 <
      sourceRootValue (reducedFamily p) rdegree first :=
    intervalSample_lt_sourceRootValue (reducedFamily p) rdegree 0 first (Nat.zero_le _)
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [reconstructedRootSigns, reconstructedRootInCell, Fin.lastCases_last]
      exact (sign_eq_zero_iff.mpr hchoice.2).symm
  | cast i =>
      simp only [reconstructedRootSigns, reconstructedRootInCell, Fin.lastCases_castSucc]
      rw [reducedIntervalColumn_sign (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree i.castSucc 0]
      simpa only [reductionDivisor_castSucc] using
        (sign_eval_eq_of_no_familyRoot_Iio (reductionDivisor p) hqne hsample hchoice.1
          hno i.castSucc)

private theorem reconstructedRootSigns_between
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (previous next : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (pre suffix : List R)
    (hindex : (previous : ℕ) < next)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous ::
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next :: suffix)
    (hex : ∃ x ∈ Set.Ioo
        (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
        (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next),
        (p (Fin.last s)).IsRoot x) :
    let w := rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)
    let cell := qCellAfterRoot w previous
    reconstructedRootSigns w (reconstructedRootInCell w cell) =
      fun i ↦ SignType.sign ((p i).eval
        (chooseRootBetween (p (Fin.last s))
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next))) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  let cell := qCellAfterRoot w previous
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hno := no_familyRoot_Ioo_of_ordered_adjacent (reductionDivisor p) horder
  have hchoice := chooseRootBetween_spec hex
  have hsampleLeft : sourceRootValue (reducedFamily p) rdegree previous <
      intervalSample (reducedFamily p) rdegree cell :=
    sourceRootValue_lt_intervalSample (reducedFamily p) rdegree previous cell (by
      dsimp [cell, qCellAfterRoot]
      omega)
  have hsampleRight : intervalSample (reducedFamily p) rdegree cell <
      sourceRootValue (reducedFamily p) rdegree next :=
    intervalSample_lt_sourceRootValue (reducedFamily p) rdegree cell next (by
      dsimp [cell, qCellAfterRoot]
      omega)
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [reconstructedRootSigns, reconstructedRootInCell, Fin.lastCases_last]
      exact (sign_eq_zero_iff.mpr hchoice.2).symm
  | cast i =>
      simp only [reconstructedRootSigns, reconstructedRootInCell, Fin.lastCases_castSucc]
      rw [reducedIntervalColumn_sign (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree i.castSucc cell]
      simpa only [reductionDivisor_castSucc] using
        (sign_eval_eq_of_no_familyRoot_Ioo (reductionDivisor p) hqne
          ⟨hsampleLeft, hsampleRight⟩ hchoice.1 hno i.castSucc)

private theorem reconstructedRootSigns_above
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (last : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (pre : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++
      [sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) last])
    (hex : ∃ x, sourceRootValue (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) last < x ∧ (p (Fin.last s)).IsRoot x) :
    let w := rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)
    let cell := qCellAfterRoot w last
    reconstructedRootSigns w (reconstructedRootInCell w cell) =
      fun i ↦ SignType.sign ((p i).eval
        (chooseRootAbove (p (Fin.last s))
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) last))) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  let cell := qCellAfterRoot w last
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hno := no_familyRoot_Ioi_of_ordered_last (reductionDivisor p) horder
  have hchoice := chooseRootAbove_spec hex
  have hsample : sourceRootValue (reducedFamily p) rdegree last <
      intervalSample (reducedFamily p) rdegree cell :=
    sourceRootValue_lt_intervalSample (reducedFamily p) rdegree last cell (by
      dsimp [cell, qCellAfterRoot]
      omega)
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [reconstructedRootSigns, reconstructedRootInCell, Fin.lastCases_last]
      exact (sign_eq_zero_iff.mpr hchoice.2).symm
  | cast i =>
      simp only [reconstructedRootSigns, reconstructedRootInCell, Fin.lastCases_castSucc]
      rw [reducedIntervalColumn_sign (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree i.castSucc cell]
      simpa only [reductionDivisor_castSucc] using
        (sign_eval_eq_of_no_familyRoot_Ioi (reductionDivisor p) hqne hsample hchoice.1
          hno i.castSucc)

private theorem reconstructedRootSigns_no_qRoots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (hno : familyRoots (reductionDivisor p) = ∅)
    (hroot : (p (Fin.last s)).IsRoot (chooseRoot (p (Fin.last s)))) :
    let w := rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)
    reconstructedRootSigns w (reconstructedRootInCell w 0) =
      fun i ↦ SignType.sign ((p i).eval (chooseRoot (p (Fin.last s)))) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [reconstructedRootSigns, reconstructedRootInCell, Fin.lastCases_last]
      exact (sign_eq_zero_iff.mpr hroot).symm
  | cast i =>
      simp only [reconstructedRootSigns, reconstructedRootInCell, Fin.lastCases_castSucc]
      rw [reducedIntervalColumn_sign (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree i.castSucc 0]
      simpa only [reductionDivisor_castSucc] using
        (sign_eval_eq_of_no_familyRoot (reductionDivisor p) hqne hno
          (intervalSample (reducedFamily p) rdegree 0) (chooseRoot (p (Fin.last s)))
          i.castSucc)

private theorem matchedOptionalQRoot_rootSigns
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (k : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (hk : k ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le))) :
    ∀ mr ∈ matchedOptionalQRoot (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) k,
      reconstructedRootSigns
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          mr.descriptor = fun i ↦ SignType.sign ((p i).eval mr.value) := by
  intro mr hmr
  by_cases hkeep : keepQRoot
      (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) k = true
  · simp only [matchedOptionalQRoot, ite_eq_left hkeep, List.mem_singleton] at hmr
    subst mr
    exact reconstructedRootSigns_at_qRoot p degree_le k hk
  · simp [matchedOptionalQRoot, hkeep] at hmr

private theorem matchedRootsAfter_rootSigns
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (previous : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (rest : List (Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ)))
    (hprevious : previous ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (hrest : ∀ k ∈ rest, k ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (pre : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous ::
        rest.map (sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le))) :
    ∀ mr ∈ matchedRootsAfter (p (Fin.last s)) (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) previous rest,
      reconstructedRootSigns
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          mr.descriptor = fun i ↦ SignType.sign ((p i).eval mr.value) := by
  induction rest generalizing previous pre with
  | nil =>
      have hcondition := final_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant previous hprevious pre (by simpa using horder)
      intro mr hmr
      by_cases hc : derivativeSignInCell
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          (qCellAfterRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) previous) *
          lastSignAtQRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
            previous = -1
      · have hex := hcondition.mp hc
        simp only [matchedRootsAfter, ite_eq_left hc, List.mem_singleton] at hmr
        subst mr
        exact reconstructedRootSigns_above p degree_le first_ne_zero last_nonconstant
          previous pre (by simpa using horder) hex
      · simp [matchedRootsAfter, hc] at hmr
  | cons next rest ih =>
      have hnext : next ∈ qRootIndices (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) := hrest next (by simp)
      have htail : ∀ k ∈ rest, k ∈ qRootIndices (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) := by
        intro k hk
        exact hrest k (by simp [hk])
      have hcondition := internal_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant previous next hprevious hnext pre
        (rest.map (sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le))) (by simpa using horder)
      have horderTail : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
          (pre ++ [sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le) previous]) ++
          sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le) next ::
            rest.map (sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le)) := by
        simpa [List.append_assoc] using horder
      have htailSigns := ih next hnext htail _ horderTail
      have hsorted : (pre ++
          sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous ::
          sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next ::
          rest.map (sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le))).SortedLT := by
        have hs := (familyRoots (reductionDivisor p)).sortedLT_sort
        rw [horder] at hs
        simpa only [List.map_cons] using hs
      have hvalue : sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le) previous <
          sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le) next := by
        have htailPair := (List.pairwise_append.mp hsorted.pairwise).2.1
        exact (List.pairwise_cons.mp htailPair).1 _ (by simp)
      have hindex : (previous : ℕ) < next :=
        (sourceRootValue_lt_sourceRootValue_iff (reducedFamily p)
          (reducedFamily_degree_le p m degree_le) previous next).mp hvalue
      intro mr hmr
      by_cases hc : lastSignAtQRoot
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) previous *
          lastSignAtQRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) next = -1
      · have hex := hcondition.mp hc
        simp only [matchedRootsAfter, ite_eq_left hc, List.mem_append, List.mem_singleton] at hmr
        rcases hmr with (rfl | hmr) | hmr
        · exact reconstructedRootSigns_between p degree_le first_ne_zero last_nonconstant
            previous next pre
            (rest.map (sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le))) hindex (by simpa using horder) hex
        · exact matchedOptionalQRoot_rootSigns p degree_le next hnext _ hmr
        · exact htailSigns _ hmr
      · simp only [matchedRootsAfter, ite_eq_right hc, List.nil_append, List.mem_append] at hmr
        rcases hmr with hmr | hmr
        · exact matchedOptionalQRoot_rootSigns p degree_le next hnext _ hmr
        · exact htailSigns _ hmr

private theorem matchedRoots_rootSigns
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    ∀ mr ∈ matchedRoots (p (Fin.last s)) (reducedFamily p)
        (reducedFamily_degree_le p m degree_le),
      reconstructedRootSigns
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          mr.descriptor = fun i ↦ SignType.sign ((p i).eval mr.value) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hvalues := qRootValues_eq (reductionDivisor p) (reducedFamily p)
    (fun i ↦ reducedFamily_firstRow p i) hqne rdegree
  cases hks : qRootIndices w with
  | nil =>
      have hsortednil : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = [] := by
        simpa [w, hks, sourceRootValue] using hvalues.symm
      have hqnil : familyRoots (reductionDivisor p) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' : x ∈ (familyRoots (reductionDivisor p)).sort (· ≤ ·) :=
          (Finset.mem_sort (· ≤ ·)).2 hx
        rw [hsortednil] at hx'
        simp at hx'
      have hderiv : ∀ x, ¬(p (Fin.last s)).derivative.IsRoot x := by
        intro x hroot
        have hxq := isRoot_mem_familyRoots' (reductionDivisor p) hqne
          (i := Fin.last s) (by simpa [reductionDivisor_last] using hroot)
        simp [hqnil] at hxq
      obtain ⟨root, hroot, _hunique⟩ :=
        exists_unique_root_of_derivative_no_roots hderiv
      have hchoose : (p (Fin.last s)).IsRoot (chooseRoot (p (Fin.last s))) :=
        chooseRoot_spec ⟨root, hroot⟩
      intro mr hmr
      simp only [matchedRoots, w, hks, List.mem_singleton] at hmr
      subst mr
      exact reconstructedRootSigns_no_qRoots p degree_le first_ne_zero
        last_nonconstant hqnil hchoose
  | cons first rest =>
      have hfirstmem : first ∈ qRootIndices w := by simp [hks]
      have hrestmem : ∀ k ∈ rest, k ∈ qRootIndices w := by
        intro k hk
        rw [hks]
        simp [hk]
      have horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
          sourceRootValue (reducedFamily p) rdegree first ::
            rest.map (sourceRootValue (reducedFamily p) rdegree) := by
        rw [← hvalues]
        simp only [w, hks, List.map_cons]
        rfl
      have hcondition := initial_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant first hfirstmem
        (rest.map (sourceRootValue (reducedFamily p) rdegree)) horder
      have htailSigns := matchedRootsAfter_rootSigns p degree_le first_ne_zero
        last_nonconstant first rest hfirstmem hrestmem [] (by simpa using horder)
      intro mr hmr
      by_cases hc : derivativeSignInCell w 0 * lastSignAtQRoot w first = 1
      · have hex := hcondition.mp hc
        simp only [matchedRoots, w, hks, ite_eq_left hc, List.mem_append,
          List.mem_singleton] at hmr
        rcases hmr with (rfl | hmr) | hmr
        · exact reconstructedRootSigns_below p degree_le first_ne_zero last_nonconstant
            first (rest.map (sourceRootValue (reducedFamily p) rdegree)) horder hex
        · exact matchedOptionalQRoot_rootSigns p degree_le first hfirstmem _ hmr
        · exact htailSigns _ hmr
      · simp only [matchedRoots, w, hks, ite_eq_right hc, List.nil_append,
          List.mem_append] at hmr
        rcases hmr with hmr | hmr
        · exact matchedOptionalQRoot_rootSigns p degree_le first hfirstmem _ hmr
        · exact htailSigns _ hmr

private theorem polynomialSignAtBot_eq_sign_eval_of_all_roots_gt
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {f : R[X]} {c : R} (hf : f ≠ 0) (hroots : ∀ z, f.IsRoot z → c < z) :
    polynomialSignAtBot f = SignType.sign (f.eval c) := by
  obtain ⟨lower, hlower⟩ := bound_polynomialSignAtBot f hf
  let z := min lower c - 1
  have hzl : z ≤ lower := by dsimp [z]; linarith [min_le_left lower c]
  have hzc : z < c := by dsimp [z]; linarith [min_le_right lower c]
  have hzne : ¬f.IsRoot z := fun hz ↦ (lt_asymm hzc (hroots z hz)).elim
  have hcne : ¬f.IsRoot c := fun hc ↦ (lt_irrefl c (hroots c hc)).elim
  have hsame := sign_eval_eq_of_no_root_between' polynomialIntermediateValue f
    hzne hcne (x := z) (y := c) (by
      intro x hx
      constructor
      · rintro ⟨_hzx, hxc⟩
        exact (lt_asymm hxc (hroots x hx)).elim
      · rintro ⟨hcx, hxz⟩
        exact (lt_asymm (hzc.trans hcx) hxz).elim)
  exact (hlower z hzl).symm.trans hsame

private theorem polynomialSignAtTop_eq_sign_eval_of_all_roots_lt
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {f : R[X]} {c : R} (hf : f ≠ 0) (hroots : ∀ z, f.IsRoot z → z < c) :
    polynomialSignAtTop f = SignType.sign (f.eval c) := by
  obtain ⟨upper, hupper⟩ := bound_polynomialSignAtTop f hf
  let z := max upper c + 1
  have huz : upper ≤ z := by dsimp [z]; linarith [le_max_left upper c]
  have hcz : c < z := by dsimp [z]; linarith [le_max_right upper c]
  have hzne : ¬f.IsRoot z := fun hz ↦ (lt_asymm (hroots z hz) hcz).elim
  have hcne : ¬f.IsRoot c := fun hc ↦ (lt_irrefl c (hroots c hc)).elim
  have hsame := sign_eval_eq_of_no_root_between' polynomialIntermediateValue f
    hzne hcne (x := z) (y := c) (by
      intro x hx
      constructor
      · rintro ⟨hzx, hxc⟩
        exact (lt_asymm (hcz.trans hzx) hxc).elim
      · rintro ⟨hcx, _hxz⟩
        exact (lt_asymm (hroots x hx) hcx).elim)
  exact (hupper z huz).symm.trans hsame

private theorem reconstructedInitialIntervalSigns_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    reconstructedInitialIntervalSigns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) =
      fun i ↦ SignType.sign ((p i).eval (intervalSample p degree_le 0)) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  let x := intervalSample p degree_le 0
  let c := intervalSample (reducedFamily p) rdegree 0
  have hlastne : p (Fin.last s) ≠ 0 := fun h ↦ last_nonconstant (by simp [h])
  have hpne : ∀ i, p i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => exact hlastne
    | cast i => exact first_ne_zero i
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hxroots : ∀ z ∈ familyRoots p, x < z := by
    intro z hz
    have hz' : z ∈ (familyRoots p).sort (· ≤ ·) := (Finset.mem_sort (· ≤ ·)).2 hz
    apply (intervalSample_spec p degree_le 0).2 z
    change z ∈ List.drop 0 ((familyRoots p).sort (· ≤ ·))
    simpa only [List.drop_zero] using hz'
  have hcroots : ∀ z ∈ familyRoots (reductionDivisor p), c < z := by
    intro z hz
    have hz' : z ∈ (familyRoots (reductionDivisor p)).sort (· ≤ ·) :=
      (Finset.mem_sort (· ≤ ·)).2 hz
    exact (intervalSample_spec (reducedFamily p) rdegree 0).2 z (by
      have hrmem : z ∈ familyRoots (reducedFamily p) := by
        rcases (Finset.mem_biUnion.mp hz) with ⟨i, _hi, hroot⟩
        have hroot' : (reductionDivisor p i).IsRoot z :=
          (Polynomial.mem_roots (hqne i)).1 (by simpa using hroot)
        simp only [familyRoots, Finset.mem_biUnion]
        refine ⟨firstReducedRow i, Finset.mem_univ _, ?_⟩
        rw [reducedFamily_firstRow]
        exact by simpa using (Polynomial.mem_roots (hqne i)).2 hroot'
      have hrmem' := (Finset.mem_sort (· ≤ ·)).2 hrmem
      change z ∈ List.drop 0 ((familyRoots (reducedFamily p)).sort (· ≤ ·))
      simpa only [List.drop_zero] using hrmem')
  funext i
  cases i using Fin.lastCases with
  | last =>
      have hfbot := polynomialSignAtBot_eq_sign_eval_of_all_roots_gt hlastne (c := x) (by
        intro z hroot
        exact hxroots z (isRoot_mem_familyRoots' p hpne hroot))
      have hdne : (p (Fin.last s)).derivative ≠ 0 :=
        Polynomial.derivative_ne_zero.mpr last_nonconstant
      have hdbot := polynomialSignAtBot_eq_sign_eval_of_all_roots_gt hdne (c := c) (by
        intro z hroot
        exact hcroots z (isRoot_mem_familyRoots' (reductionDivisor p) hqne
          (i := Fin.last s) (by simpa [reductionDivisor_last] using hroot)))
      have hrelation := polynomialSignAtBot_derivative (p (Fin.last s)) last_nonconstant
      simp only [reconstructedInitialIntervalSigns, Fin.lastCases_last]
      rw [derivativeSignInCell_eq (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree 0, reductionDivisor_last]
      rw [← hdbot, ← hfbot, hrelation]
      simp
  | cast i =>
      have hpbot := polynomialSignAtBot_eq_sign_eval_of_all_roots_gt
        (first_ne_zero i) (c := x) (by
          intro z hroot
          exact hxroots z (isRoot_mem_familyRoots' p hpne (i := i.castSucc) hroot))
      have hqbot := polynomialSignAtBot_eq_sign_eval_of_all_roots_gt
        (first_ne_zero i) (c := c) (by
          intro z hroot
          exact hcroots z (isRoot_mem_familyRoots' (reductionDivisor p) hqne
            (i := i.castSucc) (by simpa [reductionDivisor_castSucc] using hroot)))
      simp only [reconstructedInitialIntervalSigns, Fin.lastCases_castSucc]
      rw [reducedIntervalColumn_sign (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree i.castSucc 0,
        reductionDivisor_castSucc]
      exact hqbot.symm.trans hpbot

private theorem intervalSample_after_root_lt_later_familyRoot
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} (r : Fin (2 * (s + 1)) → R[X]) (degree_le : ∀ i, (r i).natDegree ≤ m)
    (k : Fin ((rootSignTable r m degree_le).1 : ℕ)) {z : R}
    (hz : z ∈ familyRoots r) (hkz : sourceRootValue r degree_le k < z) :
    intervalSample r degree_le (qCellAfterRoot (rootSignTable r m degree_le) k) < z := by
  let orderedRoots := (familyRoots r).sort (· ≤ ·)
  have hz' : z ∈ orderedRoots := (Finset.mem_sort (· ≤ ·)).2 hz
  obtain ⟨l, hl⟩ := List.mem_iff_get.mp hz'
  let l' : Fin ((rootSignTable r m degree_le).1 : ℕ) :=
    Fin.cast (by simp [rootSignTable, orderedRoots]) l
  have hzsource : sourceRootValue r degree_le l' = z := by
    unfold sourceRootValue
    rw [← hl]
    congr 1
  have hkl : (k : ℕ) < l' :=
    (sourceRootValue_lt_sourceRootValue_iff r degree_le k l').mp (by simpa [hzsource] using hkz)
  rw [← hzsource]
  exact intervalSample_lt_sourceRootValue r degree_le
    (qCellAfterRoot (rootSignTable r m degree_le) k) l'
    (by dsimp [qCellAfterRoot]; omega)

private theorem sign_eval_right_of_root_eq_derivative_sign
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {f : R[X]} {a b : R} (hab : a < b) (hroot : f.IsRoot a)
    (hderiv : ∀ z, a < z → z ≤ b → ¬f.derivative.IsRoot z) :
    SignType.sign (f.eval b) = SignType.sign (f.derivative.eval b) := by
  obtain ⟨c, hc, hmean⟩ := polynomialMeanValue (P := f) hab
  have hca : 0 < b - a := sub_pos.mpr hab
  have hdc : f.derivative.eval c ≠ 0 := by
    simpa only [Polynomial.IsRoot] using hderiv c hc.1 hc.2.le
  have hdb : f.derivative.eval b ≠ 0 := by
    simpa only [Polynomial.IsRoot] using hderiv b hab le_rfl
  have hsame : SignType.sign (f.derivative.eval c) =
      SignType.sign (f.derivative.eval b) := by
    apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue f.derivative
    · simpa only [Polynomial.IsRoot] using hdc
    · simpa only [Polynomial.IsRoot] using hdb
    · intro z hz
      constructor
      · rintro ⟨hcz, hzb⟩
        exact hderiv z (hc.1.trans hcz) hzb.le hz
      · rintro ⟨hbz, hzc⟩
        exact (lt_asymm (hc.2.trans hbz) hzc).elim
  change f.eval a = 0 at hroot
  rw [hroot, sub_zero] at hmean
  rw [hmean, sign_mul, sign_pos hca, mul_one, hsame]

private theorem reconstructedRightIntervalSigns_at_qRoot
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (k : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (hk : k ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (y : R)
    (hay : sourceRootValue (reducedFamily p)
      (reducedFamily_degree_le p m degree_le) k < y)
    (hfuture : ∀ z ∈ familyRoots p,
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) k < z →
        y < z) :
    reconstructedRightIntervalSigns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
        (reconstructedRootAtQRoot
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) k) =
      fun i ↦ SignType.sign ((p i).eval y) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  let a := sourceRootValue (reducedFamily p) rdegree k
  let c := intervalSample (reducedFamily p) rdegree (qCellAfterRoot w k)
  have hlastne : p (Fin.last s) ≠ 0 := fun h ↦ last_nonconstant (by simp [h])
  have hpne : ∀ i, p i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => exact hlastne
    | cast i => exact first_ne_zero i
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hac : a < c := sourceRootValue_lt_intervalSample (reducedFamily p) rdegree k
    (qCellAfterRoot w k) (by dsimp [qCellAfterRoot]; omega)
  have laterReducedRoot (z : R) (hz : z ∈ familyRoots (reducedFamily p))
      (haz : a < z) : c < z :=
    intervalSample_after_root_lt_later_familyRoot (reducedFamily p) rdegree k hz haz
  funext i
  cases i using Fin.lastCases with
  | last =>
      have hlast := lastSignAtQRoot_eq (p (Fin.last s)) (reductionDivisor p)
        (reducedFamily p) (fun j ↦ reducedFamily_firstRow p j)
        (fun j ↦ reducedFamily_remainderRow p j) rdegree k hk
      have hlast' : lastSignAtQRoot w k = SignType.sign ((p (Fin.last s)).eval a) := by
        simpa [w, a, sourceRootValue] using hlast
      by_cases hzero : lastSignAtQRoot w k = 0
      · have haroot : (p (Fin.last s)).IsRoot a := by
          apply sign_eq_zero_iff.mp
          exact hlast'.symm.trans hzero
        let d := (a + min c y) / 2
        have had : a < d := by
          dsimp [d]
          have : a < min c y := lt_min hac hay
          linarith
        have hdc : d < c := by
          dsimp [d]
          have := min_le_left c y
          linarith
        have hdy : d < y := by
          dsimp [d]
          have := min_le_right c y
          linarith
        have hderivNo : ∀ z, a < z → z ≤ d →
            ¬(p (Fin.last s)).derivative.IsRoot z := by
          intro z haz hzd hroot
          have hzq : z ∈ familyRoots (reducedFamily p) := by
            simp only [familyRoots, Finset.mem_biUnion]
            refine ⟨firstReducedRow (Fin.last s), Finset.mem_univ _, ?_⟩
            rw [reducedFamily_firstRow, reductionDivisor_last]
            exact by simpa using (Polynomial.mem_roots
              (by simpa [reductionDivisor_last] using hqne (Fin.last s))).2 hroot
          exact (not_lt_of_ge hzd) (hdc.trans (laterReducedRoot z hzq haz))
        have hfd := sign_eval_right_of_root_eq_derivative_sign had haroot hderivNo
        have hderivSame : SignType.sign ((p (Fin.last s)).derivative.eval d) =
            SignType.sign ((p (Fin.last s)).derivative.eval c) := by
          apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue
          · exact hderivNo d had le_rfl
          · intro hroot
            have hcq : c ∈ familyRoots (reducedFamily p) := by
              simp only [familyRoots, Finset.mem_biUnion]
              refine ⟨firstReducedRow (Fin.last s), Finset.mem_univ _, ?_⟩
              rw [reducedFamily_firstRow, reductionDivisor_last]
              exact by simpa using (Polynomial.mem_roots
                (by simpa [reductionDivisor_last] using hqne (Fin.last s))).2 hroot
            exact (lt_irrefl c (laterReducedRoot c hcq hac)).elim
          · intro z hroot
            constructor
            · rintro ⟨hdz, hzc⟩
              have hzq : z ∈ familyRoots (reducedFamily p) := by
                simp only [familyRoots, Finset.mem_biUnion]
                refine ⟨firstReducedRow (Fin.last s), Finset.mem_univ _, ?_⟩
                rw [reducedFamily_firstRow, reductionDivisor_last]
                exact by simpa using (Polynomial.mem_roots
                  (by simpa [reductionDivisor_last] using hqne (Fin.last s))).2 hroot
              exact (lt_asymm (laterReducedRoot z hzq (had.trans hdz)) hzc).elim
            · rintro ⟨hcz, hzd⟩
              exact (lt_asymm (hdc.trans hcz) hzd).elim
        have hfy : SignType.sign ((p (Fin.last s)).eval d) =
            SignType.sign ((p (Fin.last s)).eval y) := by
          apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue
          · intro hroot
            exact (lt_asymm hdy (hfuture d
              (isRoot_mem_familyRoots' p hpne hroot) had)).elim
          · intro hroot
            exact (lt_irrefl y (hfuture y
              (isRoot_mem_familyRoots' p hpne hroot) hay)).elim
          · intro z hroot
            have hzmem := isRoot_mem_familyRoots' p hpne hroot
            constructor
            · rintro ⟨hdz, hzy⟩
              exact (lt_asymm (hfuture z hzmem (had.trans hdz)) hzy).elim
            · rintro ⟨hyz, hzd⟩
              exact (lt_asymm (hfuture z hzmem (hay.trans hyz)) (hzd.trans hdy)).elim
        simp only [reconstructedRightIntervalSigns, Fin.lastCases_last]
        rw [ite_eq_left (by simpa [reconstructedRootAtQRoot, w] using hzero)]
        simp only [reconstructedRootAtQRoot]
        rw [derivativeSignInCell_eq (reductionDivisor p) (reducedFamily p)
          (fun j ↦ reducedFamily_firstRow p j) rdegree (qCellAfterRoot w k),
          reductionDivisor_last]
        exact hderivSame.symm.trans (hfd.symm.trans hfy)
      · simp only [reconstructedRightIntervalSigns, Fin.lastCases_last]
        rw [ite_eq_right (by simpa [reconstructedRootAtQRoot, w] using hzero)]
        simp only [reconstructedRootAtQRoot]
        rw [hlast']
        apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue
        · intro hroot
          exact hzero (hlast'.trans (sign_eq_zero_iff.mpr hroot))
        · intro hroot
          exact (lt_irrefl y (hfuture y
            (isRoot_mem_familyRoots' p hpne hroot) hay)).elim
        · intro z hroot
          have hzmem := isRoot_mem_familyRoots' p hpne hroot
          constructor
          · rintro ⟨haz, hzy⟩
            exact (lt_asymm (hfuture z hzmem haz) hzy).elim
          · rintro ⟨hyz, hza⟩
            exact (lt_asymm (hay.trans hyz) hza).elim
  | cast i =>
      have hci : ¬(p i.castSucc).IsRoot c := by
        intro hroot
        have hcr : c ∈ familyRoots (reducedFamily p) := by
          simp only [familyRoots, Finset.mem_biUnion]
          refine ⟨firstReducedRow i.castSucc, Finset.mem_univ _, ?_⟩
          rw [reducedFamily_firstRow, reductionDivisor_castSucc]
          exact by simpa using (Polynomial.mem_roots (first_ne_zero i)).2 hroot
        exact (lt_irrefl c (laterReducedRoot c hcr hac)).elim
      have hyi : ¬(p i.castSucc).IsRoot y := by
        intro hroot
        exact (lt_irrefl y (hfuture y
          (isRoot_mem_familyRoots' p hpne hroot) hay)).elim
      simp only [reconstructedRightIntervalSigns, reconstructedRootAtQRoot,
        Fin.lastCases_castSucc]
      rw [reducedIntervalColumn_sign (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree i.castSucc (qCellAfterRoot w k),
        reductionDivisor_castSucc]
      apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue _ hci hyi
      intro z hroot
      have hzold := isRoot_mem_familyRoots' p hpne hroot
      have hzred : z ∈ familyRoots (reducedFamily p) := by
        simp only [familyRoots, Finset.mem_biUnion]
        refine ⟨firstReducedRow i.castSucc, Finset.mem_univ _, ?_⟩
        rw [reducedFamily_firstRow, reductionDivisor_castSucc]
        exact by simpa using (Polynomial.mem_roots (first_ne_zero i)).2 hroot
      constructor
      · rintro ⟨hcz, hzy⟩
        exact (lt_asymm (hfuture z hzold (hac.trans hcz)) hzy).elim
      · rintro ⟨hyz, hzc⟩
        have haz : a < z := hay.trans hyz
        exact (lt_asymm (laterReducedRoot z hzred haz) hzc).elim

private theorem reconstructedRightIntervalSigns_inCell
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (cell : Fin (((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ) + 1))
    (a d y : R)
    (haroot : (p (Fin.last s)).IsRoot a)
    (haq : a ∉ familyRoots (reductionDivisor p))
    (hsame : ∀ i : Fin (s + 1),
      SignType.sign ((reductionDivisor p i).eval
        (intervalSample (reducedFamily p) (reducedFamily_degree_le p m degree_le) cell)) =
      SignType.sign ((reductionDivisor p i).eval a))
    (had : a < d)
    (hqAfter : ∀ z ∈ familyRoots (reductionDivisor p), a < z → d < z)
    (hay : a < y)
    (hfuture : ∀ z ∈ familyRoots p, a < z → y < z) :
    reconstructedRightIntervalSigns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
        (reconstructedRootInCell
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) cell) =
      fun i ↦ SignType.sign ((p i).eval y) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  let c := intervalSample (reducedFamily p) rdegree cell
  have hlastne : p (Fin.last s) ≠ 0 := fun h ↦ last_nonconstant (by simp [h])
  have hpne : ∀ i, p i ≠ 0 := by
    intro i
    cases i using Fin.lastCases with
    | last => exact hlastne
    | cast i => exact first_ne_zero i
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hderivNo : ∀ z, a < z → z ≤ d →
      ¬(p (Fin.last s)).derivative.IsRoot z := by
    intro z haz hzd hroot
    have hzq := isRoot_mem_familyRoots' (reductionDivisor p) hqne
      (i := Fin.last s) (by simpa [reductionDivisor_last] using hroot)
    exact (not_lt_of_ge hzd) (hqAfter z hzq haz)
  have hright := sign_eval_right_of_root_eq_derivative_sign had haroot hderivNo
  have hderivCD : SignType.sign ((p (Fin.last s)).derivative.eval c) =
      SignType.sign ((p (Fin.last s)).derivative.eval d) := by
    have hca := hsame (Fin.last s)
    rw [reductionDivisor_last] at hca
    exact hca.trans (by
      apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue
      · intro hroot
        exact haq (isRoot_mem_familyRoots' (reductionDivisor p) hqne
          (i := Fin.last s) (by simpa [reductionDivisor_last] using hroot))
      · exact hderivNo d had le_rfl
      · intro z hroot
        have hzq := isRoot_mem_familyRoots' (reductionDivisor p) hqne
          (i := Fin.last s) (by simpa [reductionDivisor_last] using hroot)
        constructor
        · rintro ⟨haz, hzd⟩
          exact (lt_asymm (hqAfter z hzq haz) hzd).elim
        · rintro ⟨hdz, hza⟩
          exact (lt_asymm (had.trans hdz) hza).elim)
  have hdFuture : ∀ z ∈ familyRoots p, a < z → d < z := by
    intro z hz haz
    rcases (mem_familyRoots_succ_iff p hpne z).1 hz with ⟨i, hroot⟩ | hroot
    · exact hqAfter z (isRoot_mem_familyRoots' (reductionDivisor p) hqne
        (i := i.castSucc) (by simpa [reductionDivisor_castSucc] using hroot)) haz
    · by_contra hn
      have hzd : z ≤ d := le_of_not_gt hn
      obtain ⟨u, hu, huroot⟩ := exists_derivative_root_between_roots haz haroot hroot
      have huq := isRoot_mem_familyRoots' (reductionDivisor p) hqne
        (i := Fin.last s) (by simpa [reductionDivisor_last] using huroot)
      exact (not_lt_of_ge (hu.2.le.trans hzd)) (hqAfter u huq hu.1)
  have hdySigns : SignType.sign ((p (Fin.last s)).eval d) =
      SignType.sign ((p (Fin.last s)).eval y) := by
    apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue
    · intro hroot
      exact (lt_irrefl d (hdFuture d (isRoot_mem_familyRoots' p hpne hroot) had)).elim
    · intro hroot
      exact (lt_irrefl y (hfuture y (isRoot_mem_familyRoots' p hpne hroot) hay)).elim
    · intro z hroot
      have hzold := isRoot_mem_familyRoots' p hpne hroot
      constructor
      · rintro ⟨hdz, hzy⟩
        exact (lt_asymm (hfuture z hzold (had.trans hdz)) hzy).elim
      · rintro ⟨hyz, hzd⟩
        exact (lt_asymm (hdFuture z hzold (hay.trans hyz)) hzd).elim
  funext i
  cases i using Fin.lastCases with
  | last =>
      simp only [reconstructedRightIntervalSigns, reconstructedRootInCell,
        Fin.lastCases_last]
      rw [ite_true]
      rw [derivativeSignInCell_eq (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree cell, reductionDivisor_last]
      exact hderivCD.trans (hright.symm.trans hdySigns)
  | cast i =>
      simp only [reconstructedRightIntervalSigns, reconstructedRootInCell,
        Fin.lastCases_castSucc]
      rw [reducedIntervalColumn_sign (reductionDivisor p) (reducedFamily p)
        (fun j ↦ reducedFamily_firstRow p j) rdegree i.castSucc cell,
        reductionDivisor_castSucc]
      have hs : SignType.sign ((p i.castSucc).eval c) =
          SignType.sign ((p i.castSucc).eval a) := by
        simpa only [reductionDivisor_castSucc] using (hsame i.castSucc)
      refine hs.trans ?_
      apply sign_eval_eq_of_no_root_between' polynomialIntermediateValue
      · intro hroot
        exact haq (isRoot_mem_familyRoots' (reductionDivisor p) hqne
          (i := i.castSucc) (by simpa [reductionDivisor_castSucc] using hroot))
      · intro hroot
        exact (lt_irrefl y (hfuture y
          (isRoot_mem_familyRoots' p hpne hroot) hay)).elim
      · intro z hroot
        have hzold := isRoot_mem_familyRoots' p hpne hroot
        constructor
        · rintro ⟨haz, hzy⟩
          exact (lt_asymm (hfuture z hzold haz) hzy).elim
        · rintro ⟨hyz, hza⟩
          exact (lt_asymm (hay.trans hyz) hza).elim

private theorem reconstructedRightIntervalSigns_below
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (first : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (rest : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) first :: rest)
    (hex : ∃ x, x < sourceRootValue (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) first ∧ (p (Fin.last s)).IsRoot x)
    (y : R)
    (hay : chooseRootBelow (p (Fin.last s))
      (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) first) < y)
    (hfuture : ∀ z ∈ familyRoots p,
      chooseRootBelow (p (Fin.last s))
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) first) < z →
        y < z) :
    reconstructedRightIntervalSigns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
        (reconstructedRootInCell
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) 0) =
      fun i ↦ SignType.sign ((p i).eval y) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let a := chooseRootBelow (p (Fin.last s))
    (sourceRootValue (reducedFamily p) rdegree first)
  let b := sourceRootValue (reducedFamily p) rdegree first
  let c := intervalSample (reducedFamily p) rdegree 0
  let d := (a + b) / 2
  have hchoice := chooseRootBelow_spec hex
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hno := no_familyRoot_Iio_of_ordered_cons (reductionDivisor p) horder
  have hcb : c < b := intervalSample_lt_sourceRootValue
    (reducedFamily p) rdegree 0 first (Nat.zero_le _)
  have had : a < d := by dsimp [d]; linarith [hchoice.1]
  have hdb : d < b := by dsimp [d]; linarith [hchoice.1]
  have hsame : ∀ i : Fin (s + 1), SignType.sign ((reductionDivisor p i).eval c) =
      SignType.sign ((reductionDivisor p i).eval a) := fun i ↦
    sign_eval_eq_of_no_familyRoot_Iio (reductionDivisor p) hqne hcb hchoice.1 hno i
  have hqAfter : ∀ z ∈ familyRoots (reductionDivisor p), a < z → d < z := by
    intro z hz _haz
    have hzmem : z ∈ b :: rest := by
      rw [← horder]
      exact (Finset.mem_sort (· ≤ ·)).2 hz
    simp only [List.mem_cons] at hzmem
    rcases hzmem with rfl | hzmem
    · exact hdb
    · have hs : (b :: rest).SortedLT := by
        rw [← horder]
        exact (familyRoots (reductionDivisor p)).sortedLT_sort
      exact hdb.trans ((List.pairwise_cons.mp hs.pairwise).1 z hzmem)
  exact reconstructedRightIntervalSigns_inCell p degree_le first_ne_zero last_nonconstant
    0 a d y hchoice.2 (hno a hchoice.1) hsame had hqAfter hay hfuture

private theorem reconstructedRightIntervalSigns_between
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (previous next : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (pre suffix : List R) (hindex : (previous : ℕ) < next)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous ::
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next :: suffix)
    (hex : ∃ x ∈ Set.Ioo
      (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
      (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next),
      (p (Fin.last s)).IsRoot x)
    (y : R)
    (hay : chooseRootBetween (p (Fin.last s))
      (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
      (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next) < y)
    (hfuture : ∀ z ∈ familyRoots p,
      chooseRootBetween (p (Fin.last s))
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous)
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next) < z →
        y < z) :
    let w := rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)
    let cell := qCellAfterRoot w previous
    reconstructedRightIntervalSigns w (reconstructedRootInCell w cell) =
      fun i ↦ SignType.sign ((p i).eval y) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  let cell := qCellAfterRoot w previous
  let left := sourceRootValue (reducedFamily p) rdegree previous
  let right := sourceRootValue (reducedFamily p) rdegree next
  let a := chooseRootBetween (p (Fin.last s)) left right
  let c := intervalSample (reducedFamily p) rdegree cell
  let d := (a + right) / 2
  have hchoice := chooseRootBetween_spec hex
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hno := no_familyRoot_Ioo_of_ordered_adjacent (reductionDivisor p) horder
  have hcleft : left < c := sourceRootValue_lt_intervalSample
    (reducedFamily p) rdegree previous cell (by dsimp [cell, qCellAfterRoot]; omega)
  have hcright : c < right := intervalSample_lt_sourceRootValue
    (reducedFamily p) rdegree cell next (by dsimp [cell, qCellAfterRoot]; omega)
  have had : a < d := by dsimp [d]; linarith [hchoice.1.2]
  have hdright : d < right := by dsimp [d]; linarith [hchoice.1.2]
  have hsame : ∀ i : Fin (s + 1), SignType.sign ((reductionDivisor p i).eval c) =
      SignType.sign ((reductionDivisor p i).eval a) := fun i ↦
    sign_eval_eq_of_no_familyRoot_Ioo (reductionDivisor p) hqne
      ⟨hcleft, hcright⟩ hchoice.1 hno i
  have hqAfter : ∀ z ∈ familyRoots (reductionDivisor p), a < z → d < z := by
    intro z hz haz
    rcases lt_trichotomy z right with hzr | rfl | hrz
    · exact (hno z ⟨hchoice.1.1.trans haz, hzr⟩ hz).elim
    · exact hdright
    · exact hdright.trans hrz
  exact reconstructedRightIntervalSigns_inCell p degree_le first_ne_zero last_nonconstant
    cell a d y hchoice.2 (hno a hchoice.1) hsame had hqAfter hay hfuture

private theorem reconstructedRightIntervalSigns_above
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (last : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (pre : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++
      [sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) last])
    (hex : ∃ x, sourceRootValue (reducedFamily p)
      (reducedFamily_degree_le p m degree_le) last < x ∧ (p (Fin.last s)).IsRoot x)
    (y : R)
    (hay : chooseRootAbove (p (Fin.last s))
      (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) last) < y)
    (hfuture : ∀ z ∈ familyRoots p,
      chooseRootAbove (p (Fin.last s))
          (sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) last) < z →
        y < z) :
    let w := rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)
    let cell := qCellAfterRoot w last
    reconstructedRightIntervalSigns w (reconstructedRootInCell w cell) =
      fun i ↦ SignType.sign ((p i).eval y) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  let cell := qCellAfterRoot w last
  let left := sourceRootValue (reducedFamily p) rdegree last
  let a := chooseRootAbove (p (Fin.last s)) left
  let c := intervalSample (reducedFamily p) rdegree cell
  let d := a + 1
  have hchoice := chooseRootAbove_spec hex
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hno := no_familyRoot_Ioi_of_ordered_last (reductionDivisor p) horder
  have hleftc : left < c := sourceRootValue_lt_intervalSample
    (reducedFamily p) rdegree last cell (by dsimp [cell, qCellAfterRoot]; omega)
  have had : a < d := by dsimp [d]; linarith
  have hsame : ∀ i : Fin (s + 1), SignType.sign ((reductionDivisor p i).eval c) =
      SignType.sign ((reductionDivisor p i).eval a) := fun i ↦
    sign_eval_eq_of_no_familyRoot_Ioi (reductionDivisor p) hqne hleftc hchoice.1 hno i
  have hqAfter : ∀ z ∈ familyRoots (reductionDivisor p), a < z → d < z := by
    intro z hz haz
    exact (hno z (hchoice.1.trans haz) hz).elim
  exact reconstructedRightIntervalSigns_inCell p degree_le first_ne_zero last_nonconstant
    cell a d y hchoice.2 (hno a hchoice.1) hsame had hqAfter hay hfuture

private theorem reconstructedRightIntervalSigns_no_qRoots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (hno : familyRoots (reductionDivisor p) = ∅)
    (hroot : (p (Fin.last s)).IsRoot (chooseRoot (p (Fin.last s))))
    (y : R) (hay : chooseRoot (p (Fin.last s)) < y)
    (hfuture : ∀ z ∈ familyRoots p, chooseRoot (p (Fin.last s)) < z → y < z) :
    let w := rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)
    reconstructedRightIntervalSigns w (reconstructedRootInCell w 0) =
      fun i ↦ SignType.sign ((p i).eval y) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let a := chooseRoot (p (Fin.last s))
  let c := intervalSample (reducedFamily p) rdegree 0
  let d := a + 1
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have had : a < d := by dsimp [d]; linarith
  have hsame : ∀ i : Fin (s + 1), SignType.sign ((reductionDivisor p i).eval c) =
      SignType.sign ((reductionDivisor p i).eval a) := fun i ↦
    sign_eval_eq_of_no_familyRoot (reductionDivisor p) hqne hno c a i
  have hqAfter : ∀ z ∈ familyRoots (reductionDivisor p), a < z → d < z := by
    intro z hz _haz
    simp [hno] at hz
  exact reconstructedRightIntervalSigns_inCell p degree_le first_ne_zero last_nonconstant
    0 a d y hroot (by simp [hno]) hsame had hqAfter hay hfuture

private theorem matchedOptionalQRoot_rightSigns
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (k : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (hk : k ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le))) :
    ∀ mr ∈ matchedOptionalQRoot (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) k,
      ∀ y, mr.value < y → (∀ z ∈ familyRoots p, mr.value < z → y < z) →
        reconstructedRightIntervalSigns
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
            mr.descriptor = fun i ↦ SignType.sign ((p i).eval y) := by
  intro mr hmr y hay hfuture
  by_cases hkeep : keepQRoot
      (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) k = true
  · simp only [matchedOptionalQRoot, ite_eq_left hkeep, List.mem_singleton] at hmr
    subst mr
    exact reconstructedRightIntervalSigns_at_qRoot p degree_le first_ne_zero
      last_nonconstant k hk y hay hfuture
  · simp [matchedOptionalQRoot, hkeep] at hmr

private theorem matchedRootsAfter_rightSigns
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0)
    (previous : Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ))
    (rest : List (Fin ((rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)).1 : ℕ)))
    (hprevious : previous ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (hrest : ∀ k ∈ rest, k ∈ qRootIndices (rootSignTable (reducedFamily p) m
      (reducedFamily_degree_le p m degree_le)))
    (pre : List R)
    (horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = pre ++
      sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous ::
        rest.map (sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le))) :
    ∀ mr ∈ matchedRootsAfter (p (Fin.last s)) (reducedFamily p)
        (reducedFamily_degree_le p m degree_le) previous rest,
      ∀ y, mr.value < y → (∀ z ∈ familyRoots p, mr.value < z → y < z) →
        reconstructedRightIntervalSigns
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
            mr.descriptor = fun i ↦ SignType.sign ((p i).eval y) := by
  induction rest generalizing previous pre with
  | nil =>
      have hcondition := final_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant previous hprevious pre (by simpa using horder)
      intro mr hmr y hay hfuture
      by_cases hc : derivativeSignInCell
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          (qCellAfterRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) previous) *
          lastSignAtQRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
            previous = -1
      · have hex := hcondition.mp hc
        simp only [matchedRootsAfter, ite_eq_left hc, List.mem_singleton] at hmr
        subst mr
        exact reconstructedRightIntervalSigns_above p degree_le first_ne_zero
          last_nonconstant previous pre (by simpa using horder) hex y hay hfuture
      · simp [matchedRootsAfter, hc] at hmr
  | cons next rest ih =>
      have hnext : next ∈ qRootIndices (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) := hrest next (by simp)
      have htail : ∀ k ∈ rest, k ∈ qRootIndices (rootSignTable (reducedFamily p) m
          (reducedFamily_degree_le p m degree_le)) := by
        intro k hk
        exact hrest k (by simp [hk])
      have hcondition := internal_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant previous next hprevious hnext pre
        (rest.map (sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le))) (by simpa using horder)
      have horderTail : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
          (pre ++ [sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le) previous]) ++
          sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le) next ::
            rest.map (sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le)) := by
        simpa [List.append_assoc] using horder
      have htailSigns := ih next hnext htail _ horderTail
      have hs := (familyRoots (reductionDivisor p)).sortedLT_sort
      rw [horder] at hs
      have hsorted : (pre ++
          sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) previous ::
          sourceRootValue (reducedFamily p) (reducedFamily_degree_le p m degree_le) next ::
          rest.map (sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le))).SortedLT := by
        simpa only [List.map_cons] using hs
      have hvalue : sourceRootValue (reducedFamily p)
          (reducedFamily_degree_le p m degree_le) previous <
          sourceRootValue (reducedFamily p)
            (reducedFamily_degree_le p m degree_le) next := by
        have htailPair := (List.pairwise_append.mp hsorted.pairwise).2.1
        exact (List.pairwise_cons.mp htailPair).1 _ (by simp)
      have hindex : (previous : ℕ) < next :=
        (sourceRootValue_lt_sourceRootValue_iff (reducedFamily p)
          (reducedFamily_degree_le p m degree_le) previous next).mp hvalue
      intro mr hmr y hay hfuture
      by_cases hc : lastSignAtQRoot
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) previous *
          lastSignAtQRoot
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) next = -1
      · have hex := hcondition.mp hc
        simp only [matchedRootsAfter, ite_eq_left hc, List.mem_append, List.mem_singleton] at hmr
        rcases hmr with (rfl | hmr) | hmr
        · exact reconstructedRightIntervalSigns_between p degree_le first_ne_zero
            last_nonconstant previous next pre
            (rest.map (sourceRootValue (reducedFamily p)
              (reducedFamily_degree_le p m degree_le))) hindex (by simpa using horder)
              hex y hay hfuture
        · exact matchedOptionalQRoot_rightSigns p degree_le first_ne_zero
            last_nonconstant next hnext _ hmr y hay hfuture
        · exact htailSigns _ hmr y hay hfuture
      · simp only [matchedRootsAfter, ite_eq_right hc, List.nil_append, List.mem_append] at hmr
        rcases hmr with hmr | hmr
        · exact matchedOptionalQRoot_rightSigns p degree_le first_ne_zero
            last_nonconstant next hnext _ hmr y hay hfuture
        · exact htailSigns _ hmr y hay hfuture

private theorem matchedRoots_rightSigns
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    ∀ mr ∈ matchedRoots (p (Fin.last s)) (reducedFamily p)
        (reducedFamily_degree_le p m degree_le),
      ∀ y, mr.value < y → (∀ z ∈ familyRoots p, mr.value < z → y < z) →
        reconstructedRightIntervalSigns
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
            mr.descriptor = fun i ↦ SignType.sign ((p i).eval y) := by
  let rdegree := reducedFamily_degree_le p m degree_le
  let w := rootSignTable (reducedFamily p) m rdegree
  have hqne : ∀ i, reductionDivisor p i ≠ 0 :=
    reductionDivisor_ne_zero' p first_ne_zero last_nonconstant
  have hvalues := qRootValues_eq (reductionDivisor p) (reducedFamily p)
    (fun i ↦ reducedFamily_firstRow p i) hqne rdegree
  cases hks : qRootIndices w with
  | nil =>
      have hsortednil : (familyRoots (reductionDivisor p)).sort (· ≤ ·) = [] := by
        simpa [w, hks, sourceRootValue] using hvalues.symm
      have hqnil : familyRoots (reductionDivisor p) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro x hx
        have hx' := (Finset.mem_sort (· ≤ ·)).2 hx
        rw [hsortednil] at hx'
        simp at hx'
      have hderiv : ∀ x, ¬(p (Fin.last s)).derivative.IsRoot x := by
        intro x hroot
        have hxq := isRoot_mem_familyRoots' (reductionDivisor p) hqne
          (i := Fin.last s) (by simpa [reductionDivisor_last] using hroot)
        simp [hqnil] at hxq
      obtain ⟨root, hroot, _hunique⟩ :=
        exists_unique_root_of_derivative_no_roots hderiv
      have hchoose : (p (Fin.last s)).IsRoot (chooseRoot (p (Fin.last s))) :=
        chooseRoot_spec ⟨root, hroot⟩
      intro mr hmr y hay hfuture
      simp only [matchedRoots, w, hks, List.mem_singleton] at hmr
      subst mr
      exact reconstructedRightIntervalSigns_no_qRoots p degree_le first_ne_zero
        last_nonconstant hqnil hchoose y hay hfuture
  | cons first rest =>
      have hfirstmem : first ∈ qRootIndices w := by simp [hks]
      have hrestmem : ∀ k ∈ rest, k ∈ qRootIndices w := by
        intro k hk
        rw [hks]
        simp [hk]
      have horder : (familyRoots (reductionDivisor p)).sort (· ≤ ·) =
          sourceRootValue (reducedFamily p) rdegree first ::
            rest.map (sourceRootValue (reducedFamily p) rdegree) := by
        rw [← hvalues]
        simp only [w, hks, List.map_cons]
        rfl
      have hcondition := initial_reconstruction_condition_iff p degree_le first_ne_zero
        last_nonconstant first hfirstmem
        (rest.map (sourceRootValue (reducedFamily p) rdegree)) horder
      have htailSigns := matchedRootsAfter_rightSigns p degree_le first_ne_zero
        last_nonconstant first rest hfirstmem hrestmem [] (by simpa using horder)
      intro mr hmr y hay hfuture
      by_cases hc : derivativeSignInCell w 0 * lastSignAtQRoot w first = 1
      · have hex := hcondition.mp hc
        simp only [matchedRoots, w, hks, ite_eq_left hc, List.mem_append,
          List.mem_singleton] at hmr
        rcases hmr with (rfl | hmr) | hmr
        · exact reconstructedRightIntervalSigns_below p degree_le first_ne_zero
            last_nonconstant first
            (rest.map (sourceRootValue (reducedFamily p) rdegree)) horder hex y hay hfuture
        · exact matchedOptionalQRoot_rightSigns p degree_le first_ne_zero
            last_nonconstant first hfirstmem _ hmr y hay hfuture
        · exact htailSigns _ hmr y hay hfuture
      · simp only [matchedRoots, w, hks, ite_eq_right hc, List.nil_append,
          List.mem_append] at hmr
        rcases hmr with hmr | hmr
        · exact matchedOptionalQRoot_rightSigns p degree_le first_ne_zero
            last_nonconstant first hfirstmem _ hmr y hay hfuture
        · exact htailSigns _ hmr y hay hfuture

private def rightSample {R : Type u} [Field R] (a : R) : List R → R
  | [] => a + 1
  | b :: _ => (a + b) / 2

private theorem lt_rightSample_of_sorted
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {a : R} {rest : List R} (hsorted : (a :: rest).SortedLT) :
    a < rightSample a rest := by
  cases rest with
  | nil => simp [rightSample]
  | cons b rest =>
      have hab := (List.pairwise_cons.mp hsorted.pairwise).1 b (by simp)
      simp only [rightSample]
      linarith

private theorem rightSample_lt_of_mem_sorted
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {a z : R} {rest : List R} (hsorted : (a :: rest).SortedLT)
    (hz : z ∈ a :: rest) (haz : a < z) :
    rightSample a rest < z := by
  cases rest with
  | nil =>
      simp only [List.mem_singleton] at hz
      subst z
      exact (lt_irrefl a haz).elim
  | cons b rest =>
      have htail := List.pairwise_cons.mp hsorted.pairwise
      have hab := htail.1 b (by simp)
      have hbrest : ∀ x ∈ rest, b < x := by
        exact (List.pairwise_cons.mp htail.2).1
      simp only [List.mem_cons] at hz
      rcases hz with hza | hzb | hz
      · subst z
        exact (lt_irrefl a haz).elim
      · subst z
        simp only [rightSample]
        linarith
      · simp only [rightSample]
        exact (by linarith [hbrest z hz] : (a + b) / 2 < z)

private theorem mem_tail_of_mem_sorted_append
    {R : Type u} [LinearOrder R] {pre rest : List R} {a z : R}
    (hsorted : (pre ++ a :: rest).SortedLT) (hz : z ∈ pre ++ a :: rest)
    (haz : a < z) : z ∈ rest := by
  rw [List.mem_append] at hz
  rcases hz with hzpre | hzsuffix
  · have hcross := (List.pairwise_append.mp hsorted.pairwise).2.2
    exact (lt_asymm (hcross z hzpre a (by simp)) haz).elim
  · simp only [List.mem_cons] at hzsuffix
    rcases hzsuffix with hza | hzrest
    · subst z
      exact (lt_irrefl a haz).elim
    · exact hzrest

private def signVector
    {R : Type u} [Field R] [LinearOrder R] {s : ℕ} (p : Fin (s + 1) → R[X]) (x : R) :
    Fin (s + 1) → SignType := fun i ↦ SignType.sign ((p i).eval x)

private def actualColumnsAfter
    {R : Type u} [Field R] [LinearOrder R] {s m : ℕ}
    {w : SignTable (2 * (s + 1)) m} (p : Fin (s + 1) → R[X]) :
    List (MatchedRoot (R := R) w) → List (Fin (s + 1) → SignType)
  | [] => []
  | mr :: rest =>
      signVector p mr.value ::
        signVector p (rightSample mr.value (rest.map MatchedRoot.value)) ::
          actualColumnsAfter p rest

private theorem actualColumnsAfter_eq_reconstructed
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    let all := matchedRoots (p (Fin.last s)) (reducedFamily p)
      (reducedFamily_degree_le p m degree_le)
    actualColumnsAfter p all = all.flatMap fun mr ↦
      [reconstructedRootSigns
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          mr.descriptor,
        reconstructedRightIntervalSigns
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          mr.descriptor] := by
  let all := matchedRoots (p (Fin.last s)) (reducedFamily p)
    (reducedFamily_degree_le p m degree_le)
  have hvalues := matchedRoots_values_eq_ordered_familyRoots p degree_le first_ne_zero
    last_nonconstant
  have hsortedAll : (all.map MatchedRoot.value).SortedLT := by
    rw [hvalues]
    exact (familyRoots p).sortedLT_sort
  have hmemAll : ∀ z, z ∈ all.map MatchedRoot.value ↔ z ∈ familyRoots p := by
    intro z
    rw [hvalues, Finset.mem_sort]
  have hrootSigns := matchedRoots_rootSigns p degree_le first_ne_zero last_nonconstant
  have hrightSigns := matchedRoots_rightSigns p degree_le first_ne_zero last_nonconstant
  have aux : ∀ (l : List (MatchedRoot (R := R)
      (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))))
      (pre : List R), all.map MatchedRoot.value = pre ++ l.map MatchedRoot.value →
      (∀ mr ∈ l, mr ∈ all) →
      actualColumnsAfter p l = l.flatMap fun mr ↦
        [reconstructedRootSigns
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
            mr.descriptor,
          reconstructedRightIntervalSigns
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
            mr.descriptor] := by
    intro l
    induction l with
    | nil => intro pre _hdecomp _hmem; simp [actualColumnsAfter]
    | cons mr rest ih =>
        intro pre hdecomp hmem
        have hmrmem : mr ∈ all := hmem mr (by simp)
        have hrestmem : ∀ x ∈ rest, x ∈ all := by
          intro x hx
          exact hmem x (by simp [hx])
        have hsuffix : (mr.value :: rest.map MatchedRoot.value).SortedLT := by
          have hsAll := hsortedAll
          rw [hdecomp] at hsAll
          have hs : (pre ++ mr.value :: rest.map MatchedRoot.value).SortedLT := by
            simpa only [List.map_cons] using hsAll
          exact (List.pairwise_append.mp hs.pairwise).2.1.sortedLT
        let y := rightSample mr.value (rest.map MatchedRoot.value)
        have hmry : mr.value < y := lt_rightSample_of_sorted hsuffix
        have hyfuture : ∀ z ∈ familyRoots p, mr.value < z → y < z := by
          intro z hzold hmrz
          have hzall : z ∈ all.map MatchedRoot.value := (hmemAll z).2 hzold
          rw [hdecomp] at hzall
          have hsAll := hsortedAll
          rw [hdecomp] at hsAll
          have hsDecomp : (pre ++ mr.value :: rest.map MatchedRoot.value).SortedLT := by
            simpa only [List.map_cons] using hsAll
          have hzrest := mem_tail_of_mem_sorted_append
            (pre := pre) (rest := rest.map MatchedRoot.value)
            hsDecomp (by simpa only [List.map_cons] using hzall) hmrz
          exact rightSample_lt_of_mem_sorted hsuffix (by simp [hzrest]) hmrz
        have hroot := hrootSigns mr hmrmem
        have hright := hrightSigns mr hmrmem y hmry hyfuture
        have htailDecomp : all.map MatchedRoot.value =
            (pre ++ [mr.value]) ++ rest.map MatchedRoot.value := by
          simpa [List.append_assoc] using hdecomp
        have htail := ih (pre ++ [mr.value]) htailDecomp hrestmem
        simp only [actualColumnsAfter, List.flatMap_cons]
        rw [hroot, hright, htail]
        rfl
  exact aux all [] (by simp) (fun _ h ↦ h)

private theorem samplesFrom_map_signVector_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} {w : SignTable (2 * (s + 1)) m}
    (p : Fin (s + 1) → R[X]) (a : R) (l : List (MatchedRoot (R := R) w)) :
    (samplesFrom a (l.map MatchedRoot.value)).map (signVector p) =
      signVector p (rightSample a (l.map MatchedRoot.value)) :: actualColumnsAfter p l := by
  induction l generalizing a with
  | nil => simp [samplesFrom, rightSample, actualColumnsAfter]
  | cons mr rest ih =>
      simp only [List.map_cons, samplesFrom, rightSample, List.map_cons, actualColumnsAfter]
      rw [ih]
      simp only [rightSample]

private def initialSample {R : Type u} [Field R] : List R → R
  | [] => 0
  | a :: _ => a - 1

private theorem cellSamples_get_interval_zero
    {R : Type u} [Field R] (roots : List R) :
    (cellSamples roots).get (cellSamplesIntervalIndex roots 0) = initialSample roots := by
  cases roots <;> rfl

private theorem cellSamples_map_signVector_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {s m : ℕ} {w : SignTable (2 * (s + 1)) m}
    (p : Fin (s + 1) → R[X]) (l : List (MatchedRoot (R := R) w)) :
    (cellSamples (l.map MatchedRoot.value)).map (signVector p) =
      signVector p (initialSample (l.map MatchedRoot.value)) :: actualColumnsAfter p l := by
  cases l with
  | nil => simp [cellSamples, initialSample, actualColumnsAfter]
  | cons mr rest =>
      have hsamples := samplesFrom_map_signVector_eq p mr.value rest
      simp only [List.map_cons, cellSamples, initialSample, actualColumnsAfter, List.map_cons]
      rw [hsamples]

private theorem intervalSample_zero_eq_initialSample
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {t m : ℕ} (p : Fin t → R[X]) (degree_le : ∀ i, (p i).natDegree ≤ m) :
    intervalSample p degree_le 0 = initialSample ((familyRoots p).sort (· ≤ ·)) := by
  unfold intervalSample
  let roots := (familyRoots p).sort (· ≤ ·)
  change (cellSamples roots).get
      (cellSamplesIntervalIndex roots (Fin.cast _ 0)) = initialSample roots
  have hk : Fin.cast
      (by simp [roots, rootSignTable] :
        ((rootSignTable p m degree_le).1 : ℕ) + 1 = roots.length + 1) 0 =
      (0 : Fin (roots.length + 1)) := by
    apply Fin.ext
    rfl
  rw [hk]
  exact cellSamples_get_interval_zero roots

private theorem reconstructedColumns_eq_cellSamples
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    reconstructedColumns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) =
      (cellSamples ((familyRoots p).sort (· ≤ ·))).map (signVector p) := by
  let all := matchedRoots (p (Fin.last s)) (reducedFamily p)
    (reducedFamily_degree_le p m degree_le)
  have hvalues := matchedRoots_values_eq_ordered_familyRoots p degree_le first_ne_zero
    last_nonconstant
  have hdescriptors := matchedRoots_descriptors (p (Fin.last s)) (reducedFamily p)
    (reducedFamily_degree_le p m degree_le)
  have hafter := actualColumnsAfter_eq_reconstructed p degree_le first_ne_zero
    last_nonconstant
  have hinitial := reconstructedInitialIntervalSigns_eq p degree_le first_ne_zero
    last_nonconstant
  have hvalues' : all.map MatchedRoot.value = (familyRoots p).sort (· ≤ ·) := by
    exact hvalues
  have hdescriptors' : all.map MatchedRoot.descriptor =
      reconstructionRoots
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) := by
    exact hdescriptors
  have hafter' : actualColumnsAfter p all = all.flatMap fun mr ↦
      [reconstructedRootSigns
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          mr.descriptor,
        reconstructedRightIntervalSigns
          (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
          mr.descriptor] := by
    exact hafter
  rw [← hvalues']
  simp only [reconstructedColumns]
  rw [← hdescriptors', List.flatMap_map]
  change _ :: all.flatMap (fun mr ↦
    [reconstructedRootSigns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
        mr.descriptor,
      reconstructedRightIntervalSigns
        (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))
        mr.descriptor]) = _
  rw [← hafter', hinitial, intervalSample_zero_eq_initialSample]
  rw [← hvalues']
  change signVector p (initialSample (all.map MatchedRoot.value)) ::
      actualColumnsAfter p all = _
  exact (cellSamples_map_signVector_eq p all).symm

private theorem reconstructionRoots_length_eq_card
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    {s m : ℕ} (p : Fin (s + 1) → R[X])
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last s)).natDegree ≠ 0) :
    (reconstructionRoots
      (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le))).length =
      (familyRoots p).card := by
  have hdescriptors := matchedRoots_descriptors (p (Fin.last s)) (reducedFamily p)
    (reducedFamily_degree_le p m degree_le)
  have hvalues := matchedRoots_values_eq_ordered_familyRoots p degree_le first_ne_zero
    last_nonconstant
  calc
    (reconstructionRoots
      (rootSignTable (reducedFamily p) m
        (reducedFamily_degree_le p m degree_le))).length =
        ((matchedRoots (p (Fin.last s)) (reducedFamily p)
          (reducedFamily_degree_le p m degree_le)).map MatchedRoot.descriptor).length := by
            rw [hdescriptors]
    _ = (matchedRoots (p (Fin.last s)) (reducedFamily p)
          (reducedFamily_degree_le p m degree_le)).length := by simp
    _ = ((matchedRoots (p (Fin.last s)) (reducedFamily p)
          (reducedFamily_degree_le p m degree_le)).map MatchedRoot.value).length := by simp
    _ = ((familyRoots p).sort (· ≤ ·)).length := by rw [hvalues]
    _ = (familyRoots p).card := Finset.length_sort (· ≤ ·)

private theorem signTable_ext_of_val
    {s m : ℕ} (a b : SignTable s m)
    (hcount : (a.1 : ℕ) = (b.1 : ℕ))
    (hentries : ∀ row (column : Fin (2 * (a.1 : ℕ) + 1)),
      a.2 row column = b.2 row (Fin.cast (by omega) column)) :
    a = b := by
  rcases a with ⟨ac, af⟩
  rcases b with ⟨bc, bf⟩
  change (ac : ℕ) = (bc : ℕ) at hcount
  have hc : ac = bc := Fin.ext hcount
  subst bc
  have hfun : af = bf := by
    funext row column
    simpa using hentries row column
  exact congrArg
    (fun f : Fin s → Fin (2 * (ac : ℕ) + 1) → SignType ↦
      (⟨ac, f⟩ : SignTable s m)) hfun

private theorem list_get_eq_of_eq
    {α : Type u} {l₁ l₂ : List α} (h : l₁ = l₂)
    (i₁ : Fin l₁.length) (i₂ : Fin l₂.length) (hi : (i₁ : ℕ) = i₂) :
    l₁.get i₁ = l₂.get i₂ := by
  subst l₂
  have : i₁ = i₂ := Fin.ext hi
  subst i₂
  rfl


/-- Book Lemma 1.4.5.  A finite, field-independent function reconstructs the old sign table from
the reduced sign table.

The hypotheses correspond exactly to the book: the last polynomial is nonconstant and the earlier
polynomials are nonzero.  Since the source and target types are finite, it is enough to show that
equal reduced sign tables force equal original sign tables.
-/
theorem exists_reconstruction (s m : ℕ) :
    ∃ reconstruct : SignTable (2 * (s + 1)) m → SignTable (s + 1) m,
      ∀ (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
        (p : Fin (s + 1) → R[X])
        (degree_le : ∀ i, (p i).natDegree ≤ m)
        (_first_ne_zero : ∀ i : Fin s, p i.castSucc ≠ 0)
        (_last_nonconstant : (p (Fin.last s)).natDegree ≠ 0),
        rootSignTable p m degree_le =
          reconstruct
            (rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)) := by
  refine ⟨reconstructSignTable s m, ?_⟩
  intro R _ _ _ _ p degree_le first_ne_zero last_nonconstant
  let w := rootSignTable (reducedFamily p) m (reducedFamily_degree_le p m degree_le)
  have hlength := reconstructionRoots_length_eq_card p degree_le first_ne_zero
    last_nonconstant
  have hbound : (reconstructionRoots w).length < (s + 1) * m + 1 := by
    rw [hlength]
    exact Nat.lt_succ_of_le (familyRoots_card_le p m degree_le)
  change rootSignTable p m degree_le = reconstructSignTable s m w
  have hreconstruct : reconstructSignTable s m w =
      (⟨⟨(reconstructionRoots w).length, hbound⟩, fun row column ↦
        (reconstructedColumns w).get
          (Fin.cast (by simp [reconstructedColumns_length]) column) row⟩ :
        SignTable (s + 1) m) := by
    unfold reconstructSignTable
    exact dite_eq_left hbound
  rw [hreconstruct]
  have hlengthw : (reconstructionRoots w).length = (familyRoots p).card := by
    simpa [w] using hlength
  refine signTable_ext_of_val _ _ (by
    simpa [rootSignTable] using hlengthw.symm) ?_
  intro row column
  let roots := (familyRoots p).sort (· ≤ ·)
  let leftIndex : Fin (cellSamples roots).length :=
    Fin.cast (by simp [roots, rootSignTable, cellSamples_length]) column
  let reconstructedColumn : Fin (2 * (reconstructionRoots w).length + 1) :=
    Fin.cast (by simp only [rootSignTable]; omega) column
  let rightIndex : Fin (reconstructedColumns w).length :=
    Fin.cast (by simp [reconstructedColumns_length]) reconstructedColumn
  let mappedIndex : Fin ((cellSamples roots).map (signVector p)).length :=
    ⟨column, by
      simp only [List.length_map, cellSamples_length, roots, Finset.length_sort]
      simp only [rootSignTable] at column
      exact column.isLt⟩
  change SignType.sign ((p row).eval ((cellSamples roots).get leftIndex)) =
    (reconstructedColumns w).get rightIndex row
  have hcolumns := reconstructedColumns_eq_cellSamples p degree_le first_ne_zero
    last_nonconstant
  have hget := list_get_eq_of_eq hcolumns rightIndex mappedIndex (by
    dsimp [rightIndex, reconstructedColumn, mappedIndex])
  rw [hget]
  simp only [List.get_eq_getElem, List.getElem_map, signVector]
  congr 3

private noncomputable def pseudoRemainderAux {A : Type u} [CommRing A]
    (q : A[X]) (d : ℕ) : ℕ → A[X] → A[X]
  | 0, p => p
  | k + 1, p =>
      pseudoRemainderAux q d k
        (C (q.coeff d) * p - monomial k (p.coeff (d + k)) * q)

private theorem pseudoRemainderAux_map {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) (q p : A[X]) (d k : ℕ) :
    (pseudoRemainderAux q d k p).map f =
      pseudoRemainderAux (q.map f) d k (p.map f) := by
  induction k generalizing p with
  | zero => rfl
  | succ k ih =>
      rw [pseudoRemainderAux, pseudoRemainderAux, ih]
      congr 1
      simp

private theorem pseudoRemainderAux_modEq {A : Type u} [CommRing A]
    (q p : A[X]) (d k : ℕ) :
    ∃ t : A[X], pseudoRemainderAux q d k p = C ((q.coeff d) ^ k) * p + q * t := by
  induction k generalizing p with
  | zero => exact ⟨0, by simp [pseudoRemainderAux]⟩
  | succ k ih =>
      let step := C (q.coeff d) * p - monomial k (p.coeff (d + k)) * q
      obtain ⟨t, ht⟩ := ih step
      refine ⟨t - C ((q.coeff d) ^ k) * monomial k (p.coeff (d + k)), ?_⟩
      rw [pseudoRemainderAux, ht]
      dsimp only [step]
      simp only [mul_sub, mul_assoc, C_mul, pow_succ]
      ring

private theorem pseudoRemainderStep_degree_lt {K : Type u} [CommRing K] [NoZeroDivisors K]
    (q p : K[X]) (d k : ℕ) (hqdeg : q.natDegree = d)
    (hpdeg : p.degree < (d + k + 1 : ℕ)) :
    (C (q.coeff d) * p - monomial k (p.coeff (d + k)) * q).degree <
      (d + k : ℕ) := by
  rw [Polynomial.degree_lt_iff_coeff_zero]
  intro e he
  by_cases heq : e = d + k
  · subst e
    simp only [coeff_sub, coeff_C_mul]
    rw [Polynomial.coeff_monomial_mul q k d]
    ring
  · have hgt : d + k < e := lt_of_le_of_ne he (Ne.symm heq)
    have hpcoeff : p.coeff e = 0 :=
      (Polynomial.degree_lt_iff_coeff_zero p (d + k + 1)).mp hpdeg e (by omega)
    rw [coeff_sub, coeff_C_mul, hpcoeff, mul_zero, zero_sub]
    rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, coeff_X_pow_mul']
    simp only [neg_eq_zero]
    split_ifs with hk
    · have hqcoeff : q.coeff (e - k) = 0 := by
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        rw [hqdeg]
        omega
      rw [hqcoeff, mul_zero]
    · simp

private theorem pseudoRemainderAux_degree_lt {K : Type u} [CommRing K] [NoZeroDivisors K]
    (q p : K[X]) (d k : ℕ) (hqdeg : q.natDegree = d)
    (hpdeg : p.degree < (d + k : ℕ)) :
    (pseudoRemainderAux q d k p).degree < (d : ℕ) := by
  induction k generalizing p with
  | zero =>
      change p.degree < (d : ℕ)
      simpa using hpdeg
  | succ k ih =>
      rw [pseudoRemainderAux]
      apply ih
      exact pseudoRemainderStep_degree_lt q p d k hqdeg
        (by simpa [Nat.add_assoc] using hpdeg)

private theorem pseudoRemainderAux_eq_pow_mul_mod {K : Type u} [Field K]
    (q p : K[X]) (d k : ℕ) (hqdeg : q.natDegree = d) (hq0 : q ≠ 0)
    (hpdeg : p.degree < (d + k : ℕ)) :
    pseudoRemainderAux q d k p = C ((q.coeff d) ^ k) * (p % q) := by
  let a := q.coeff d
  have ha : a ≠ 0 := by
    dsimp only [a]
    rw [← hqdeg]
    exact leadingCoeff_ne_zero.mpr hq0
  have hauxdeg : (pseudoRemainderAux q d k p).degree < q.degree := by
    rw [Polynomial.degree_eq_natDegree hq0, hqdeg]
    exact pseudoRemainderAux_degree_lt q p d k hqdeg hpdeg
  have hremdeg : (C (a ^ k) * (p % q)).degree < q.degree := by
    rw [Polynomial.degree_C_mul (pow_ne_zero k ha)]
    exact EuclideanDomain.mod_lt p hq0
  have hdvd : q ∣ pseudoRemainderAux q d k p - C (a ^ k) * (p % q) := by
    obtain ⟨t, ht⟩ := pseudoRemainderAux_modEq q p d k
    have hpdecomp : p = q * (p / q) + p % q := (EuclideanDomain.div_add_mod p q).symm
    have hmul : C (a ^ k) * p = C (a ^ k) * (q * (p / q) + p % q) :=
      congrArg (fun z : K[X] ↦ C (a ^ k) * z) hpdecomp
    refine ⟨C (a ^ k) * (p / q) + t, ?_⟩
    rw [ht]
    dsimp only [a]
    rw [hmul]
    ring
  have hmod := Polynomial.mod_eq_of_dvd_sub hdvd
  rw [(Polynomial.mod_eq_self_iff hq0).2 hauxdeg,
    (Polynomial.mod_eq_self_iff hq0).2 hremdeg] at hmod
  exact hmod

private noncomputable def positivePseudoRemainder {A : Type u} [CommRing A]
    (p q : A[X]) (M : ℕ) : A[X] :=
  let d := q.natDegree
  let k := M - d + 1
  C (q.leadingCoeff ^ k) * pseudoRemainderAux q d k p

private theorem positivePseudoRemainder_map {A : Type u} {K : Type v}
    [CommRing A] [Field K] (f : A →+* K) (p q : A[X]) (M : ℕ)
    (hpdeg : p.natDegree ≤ M) (hqdeg : q.natDegree ≤ M)
    (hqlead : f q.leadingCoeff ≠ 0) :
    (positivePseudoRemainder p q M).map f =
      C ((f q.leadingCoeff) ^ (2 * (M - q.natDegree + 1))) * (p.map f % q.map f) := by
  let d := q.natDegree
  let k := M - d + 1
  have hqmap0 : q.map f ≠ 0 := by
    intro hzero
    have := congrArg (fun r : K[X] ↦ r.coeff d) hzero
    simp [d, hqlead] at this
  have hqmapdeg : (q.map f).natDegree = d := by
    apply natDegree_eq_of_degree_eq
    rw [Polynomial.degree_map_eq_of_leadingCoeff_ne_zero f hqlead]
  have hpmapdeg : (p.map f).degree < (d + k : ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro e he
    rw [coeff_map]
    have hcoeff : p.coeff e = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      dsimp only [d, k] at he ⊢
      have : M < e := by omega
      exact hpdeg.trans_lt this
    simp [hcoeff]
  have haux := pseudoRemainderAux_eq_pow_mul_mod (q.map f) (p.map f) d k
    hqmapdeg hqmap0 hpmapdeg
  unfold positivePseudoRemainder
  rw [Polynomial.map_mul, Polynomial.map_C, map_pow, pseudoRemainderAux_map]
  change C ((f q.leadingCoeff) ^ k) *
      pseudoRemainderAux (q.map f) d k (p.map f) =
    C ((f q.leadingCoeff) ^ (2 * k)) * (p.map f % q.map f)
  rw [haux]
  have hcoeff : (q.map f).coeff d = f q.leadingCoeff := by
    change (q.map f).coeff q.natDegree = f q.leadingCoeff
    rw [coeff_map]
    rfl
  rw [hcoeff, ← mul_assoc, ← C_mul, ← pow_add]
  rw [show k + k = 2 * k by omega]

private theorem positivePseudoRemainder_degree_lt {A : Type u}
    [CommRing A] [NoZeroDivisors A] (p q : A[X]) (M : ℕ)
    (hpdeg : p.natDegree ≤ M) (hqdeg : q.natDegree ≤ M) (hq0 : q ≠ 0) :
    (positivePseudoRemainder p q M).degree < (q.natDegree : ℕ) := by
  let d := q.natDegree
  let k := M - d + 1
  have hpdegree : p.degree < (d + k : ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro e he
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    dsimp only [d, k] at he ⊢
    have : M < e := by omega
    exact hpdeg.trans_lt this
  rw [positivePseudoRemainder, Polynomial.degree_C_mul (pow_ne_zero _
    (leadingCoeff_ne_zero.mpr hq0))]
  exact pseudoRemainderAux_degree_lt q p d k rfl hpdegree

private noncomputable def polynomialComplexity {A : Type u} [Semiring A]
    (p : A[X]) : Multiset ℕ := by
  classical
  exact if p = 0 then ∅ else {p.natDegree + 1}

private noncomputable def parametricDegreeProfile {A : Type u} [Semiring A] {r : ℕ}
    (p : Fin r → A[X]) : Multiset ℕ :=
  ∑ i, polynomialComplexity (p i)

private theorem polynomialComplexity_eq_singleton {A : Type u} [Semiring A]
    {p : A[X]} (hp : p ≠ 0) : polynomialComplexity p = {p.natDegree + 1} := by
  simp [polynomialComplexity, hp]

private theorem parametricDegreeProfile_update {A : Type u} [Semiring A]
    {r : ℕ} (p : Fin r → A[X]) (i : Fin r) (q : A[X]) :
    parametricDegreeProfile (Function.update p i q) =
      (∑ j ∈ (Finset.univ : Finset (Fin r)).erase i, polynomialComplexity (p j)) +
        polynomialComplexity q := by
  classical
  unfold parametricDegreeProfile
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  rw [Function.update_self]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_erase] at hj
  rw [Function.update_of_ne hj.1]

private theorem parametricDegreeProfile_update_lt {A : Type u}
    [CommRing A] [NoZeroDivisors A] {r : ℕ} (p : Fin r → A[X]) (i : Fin r)
    (hp : p i ≠ 0) {q : A[X]}
    (hq : q = 0 ∨ q.natDegree < (p i).natDegree) :
    Multiset.IsDershowitzMannaLT
      (parametricDegreeProfile (Function.update p i q)) (parametricDegreeProfile p) := by
  classical
  let rest := ∑ j ∈ (Finset.univ : Finset (Fin r)).erase i, polynomialComplexity (p j)
  let replacement := polynomialComplexity q
  refine ⟨rest, replacement, {(p i).natDegree + 1}, by simp,
    parametricDegreeProfile_update p i q, ?_, ?_⟩
  · unfold parametricDegreeProfile
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
    simp [polynomialComplexity_eq_singleton hp, rest]
  · intro degree hdegree
    by_cases hq0 : q = 0
    · dsimp only [replacement] at hdegree
      simp [polynomialComplexity, hq0] at hdegree
    · dsimp only [replacement] at hdegree
      rw [polynomialComplexity_eq_singleton hq0,
        Multiset.mem_singleton] at hdegree
      subst degree
      refine ⟨(p i).natDegree + 1, by simp, ?_⟩
      rcases hq with rfl | hq
      · contradiction
      · omega

private theorem map_eraseLead_eq_of_leadingCoeff_eq_zero {A : Type u} {K : Type v}
    [CommRing A] [CommRing K] (f : A →+* K) (p : A[X])
    (hlead : f p.leadingCoeff = 0) : p.eraseLead.map f = p.map f := by
  ext i
  rw [coeff_map, coeff_map, eraseLead_coeff]
  split_ifs with hi
  · subst i
    change f 0 = f p.leadingCoeff
    rw [map_zero, hlead]
  · rfl

private theorem map_ne_zero_of_leadingCoeff_ne_zero {A : Type u} {K : Type v}
    [Semiring A] [Semiring K] (f : A →+* K) (p : A[X])
    (hlead : f p.leadingCoeff ≠ 0) : p.map f ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun q : K[X] ↦ q.coeff p.natDegree) hzero
  rw [coeff_map] at hcoeff
  exact hlead (by simpa using hcoeff)

private noncomputable def truncateFamily {A : Type u} [CommRing A] {r : ℕ}
    (p : Fin r → A[X]) (i : Fin r) : Fin r → A[X] :=
  Function.update p i (p i).eraseLead

private theorem truncateFamily_degree_le {A : Type u} [CommRing A] {r m : ℕ}
    (p : Fin r → A[X]) (degree_le : ∀ i, (p i).natDegree ≤ m) (i : Fin r) :
    ∀ j, (truncateFamily p i j).natDegree ≤ m := by
  classical
  intro j
  by_cases hji : j = i
  · subst j
    rw [truncateFamily, Function.update_self]
    exact (p i).eraseLead_natDegree_le_aux.trans (degree_le i)
  · rw [truncateFamily, Function.update_of_ne hji]
    exact degree_le j

private theorem truncateFamily_profile_lt {A : Type u}
    [CommRing A] [NoZeroDivisors A] {r : ℕ} (p : Fin r → A[X]) (i : Fin r)
    (hp : p i ≠ 0) :
    Multiset.IsDershowitzMannaLT
      (parametricDegreeProfile (truncateFamily p i)) (parametricDegreeProfile p) := by
  apply parametricDegreeProfile_update_lt p i hp
  exact (p i).eraseLead_natDegree_lt_or_eraseLead_eq_zero.symm

private theorem truncateFamily_map_eq {A : Type u} {K : Type v}
    [CommRing A] [CommRing K] {r : ℕ} (f : A →+* K) (p : Fin r → A[X])
    (i : Fin r) (hlead : f (p i).leadingCoeff = 0) :
    (fun j ↦ (truncateFamily p i j).map f) = fun j ↦ (p j).map f := by
  classical
  funext j
  by_cases hji : j = i
  · subst j
    rw [truncateFamily, Function.update_self,
      map_eraseLead_eq_of_leadingCoeff_eq_zero f (p i) hlead]
  · rw [truncateFamily, Function.update_of_ne hji]

private def constantSignTable {r m : ℕ} (signs : Fin r → SignType) : SignTable r m :=
  ⟨⟨0, by omega⟩, fun row _ ↦ signs row⟩

namespace Formula

private def verum (n : ℕ) : Formula n := .not .falsum

private def conjunction {n : ℕ} : List (Formula n) → Formula n
  | [] => verum n
  | formula :: formulas => .and formula (conjunction formulas)

private def disjunction {n : ℕ} : List (Formula n) → Formula n
  | [] => .falsum
  | formula :: formulas => .or formula (disjunction formulas)

private theorem realize_verum {n : ℕ} {R : Type u} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (y : Fin n → R) : (verum n).Realize y := by
  simp [verum, Realize]

private theorem realize_conjunction_iff {n : ℕ} {R : Type u} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (formulas : List (Formula n)) (y : Fin n → R) :
    (conjunction formulas).Realize y ↔ ∀ formula ∈ formulas, formula.Realize y := by
  induction formulas with
  | nil => simp [conjunction, realize_verum]
  | cons formula formulas ih => simp [conjunction, Realize, ih]

private theorem realize_disjunction_iff {n : ℕ} {R : Type u} [CommRing R] [LinearOrder R]
    [IsStrictOrderedRing R] (formulas : List (Formula n)) (y : Fin n → R) :
    (disjunction formulas).Realize y ↔ ∃ formula ∈ formulas, formula.Realize y := by
  induction formulas with
  | nil => simp [disjunction, Realize]
  | cons formula formulas ih => simp [disjunction, Realize, ih]

private noncomputable def allLeadingNonzero {n r : ℕ}
    (p : Fin r → (IntPolynomial n)[X]) : Formula n :=
  conjunction (List.ofFn fun i ↦
    if p i = 0 then verum n else .not (.sign (p i).leadingCoeff 0))

private theorem realize_allLeadingNonzero_iff {n r : ℕ}
    (p : Fin r → (IntPolynomial n)[X]) {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] (y : Fin n → R) :
    (allLeadingNonzero p).Realize y ↔
      ∀ i, p i ≠ 0 →
        MvPolynomial.eval₂Hom (Int.castRingHom R) y (p i).leadingCoeff ≠ 0 := by
  rw [allLeadingNonzero, realize_conjunction_iff]
  simp only [List.mem_ofFn', Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  constructor
  · intro h i hi
    simpa [hi, Realize, sign_eq_zero_iff] using h i
  · intro h i
    by_cases hi : p i = 0
    · simp [hi, realize_verum]
    · simpa [hi, Realize, sign_eq_zero_iff] using h i hi

private noncomputable def realizesSignVector {n r : ℕ}
    (p : Fin r → (IntPolynomial n)[X]) (signs : Fin r → SignType) : Formula n :=
  conjunction (List.ofFn fun i ↦ .sign ((p i).coeff 0) (signs i))

private theorem realize_realizesSignVector_iff {n r : ℕ}
    (p : Fin r → (IntPolynomial n)[X]) (signs : Fin r → SignType)
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (y : Fin n → R) :
    (realizesSignVector p signs).Realize y ↔
      ∀ i, SignType.sign
        (MvPolynomial.eval₂Hom (Int.castRingHom R) y ((p i).coeff 0)) = signs i := by
  rw [realizesSignVector, realize_conjunction_iff]
  simp only [List.mem_ofFn', Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  rfl

private noncomputable def constantCase {n r m : ℕ}
    (p : Fin r → (IntPolynomial n)[X]) (tables : Set (SignTable r m)) : Formula n := by
  classical
  exact disjunction <|
    ((Finset.univ.filter fun signs : Fin r → SignType ↦
      constantSignTable signs ∈ tables).toList.map (realizesSignVector p))

private theorem realize_constantCase_iff {n r m : ℕ}
    (p : Fin r → (IntPolynomial n)[X]) (tables : Set (SignTable r m))
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R] (y : Fin n → R) :
    (constantCase p tables).Realize y ↔
      constantSignTable (fun i ↦ SignType.sign
        (MvPolynomial.eval₂Hom (Int.castRingHom R) y ((p i).coeff 0))) ∈ tables := by
  classical
  rw [constantCase, realize_disjunction_iff]
  simp only [List.mem_map, Finset.mem_toList, Finset.mem_filter, Finset.mem_univ, true_and,
    exists_exists_and_eq_and, realize_realizesSignVector_iff]
  constructor
  · rintro ⟨signs, htable, hsigns⟩
    have heq : signs = fun i ↦ SignType.sign
        (MvPolynomial.eval₂Hom (Int.castRingHom R) y ((p i).coeff 0)) := by
      funext i
      exact (hsigns i).symm
    simpa [heq] using htable
  · intro htable
    refine ⟨(fun i ↦ SignType.sign
      (MvPolynomial.eval₂Hom (Int.castRingHom R) y ((p i).coeff 0))), htable, ?_⟩
    intro i
    rfl

end Formula

private theorem signTable_ext_of_val' {r m : ℕ} (a b : SignTable r m)
    (hcount : (a.1 : ℕ) = (b.1 : ℕ))
    (hentries : ∀ row (column : Fin (2 * (a.1 : ℕ) + 1)),
      a.2 row column = b.2 row (Fin.cast (by omega) column)) : a = b := by
  rcases a with ⟨ac, af⟩
  rcases b with ⟨bc, bf⟩
  change (ac : ℕ) = (bc : ℕ) at hcount
  have hc : ac = bc := Fin.ext hcount
  subst bc
  have hfun : af = bf := by
    funext row column
    simpa using hentries row column
  exact congrArg
    (fun f : Fin r → Fin (2 * (ac : ℕ) + 1) → SignType ↦
      (⟨ac, f⟩ : SignTable r m)) hfun

private noncomputable def signTableFromRoots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} (p : Fin r → R[X]) (roots : Finset R)
    (card_le : roots.card ≤ r * m) : SignTable r m :=
  ⟨⟨roots.card, Nat.lt_succ_of_le card_le⟩, fun row column ↦
    SignType.sign ((p row).eval
      ((cellSamples (roots.sort (· ≤ ·))).get
        (Fin.cast (by simp [cellSamples_length]) column)))⟩

private theorem rootSignTable_eq_signTableFromRoots
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} (p : Fin r → R[X]) (degree_le : ∀ i, (p i).natDegree ≤ m)
    (roots : Finset R) (hroots : familyRoots p = roots) (card_le : roots.card ≤ r * m) :
    rootSignTable p m degree_le = signTableFromRoots p roots card_le := by
  subst roots
  rfl

private theorem signTableFromRoots_eq_of_sign_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} (p q : Fin r → R[X]) (roots : Finset R)
    (card_le_p card_le_q : roots.card ≤ r * m)
    (hsign : ∀ i x, SignType.sign ((p i).eval x) = SignType.sign ((q i).eval x)) :
    signTableFromRoots p roots card_le_p = signTableFromRoots q roots card_le_q := by
  refine signTable_ext_of_val' _ _ (by rfl) ?_
  intro row column
  exact hsign row _

private theorem rootSignTable_eq_of_familyRoots_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} (p q : Fin r → R[X])
    (degree_le_p : ∀ i, (p i).natDegree ≤ m)
    (degree_le_q : ∀ i, (q i).natDegree ≤ m)
    (hroots : familyRoots p = familyRoots q)
    (hsign : ∀ i x, SignType.sign ((p i).eval x) = SignType.sign ((q i).eval x)) :
    rootSignTable p m degree_le_p = rootSignTable q m degree_le_q := by
  let roots := familyRoots p
  have card_le_p : roots.card ≤ r * m := familyRoots_card_le p m degree_le_p
  have card_le_q : roots.card ≤ r * m := by
    dsimp only [roots]
    rw [hroots]
    exact familyRoots_card_le q m degree_le_q
  calc
    rootSignTable p m degree_le_p = signTableFromRoots p roots card_le_p :=
      rootSignTable_eq_signTableFromRoots p degree_le_p roots rfl card_le_p
    _ = signTableFromRoots q roots card_le_q :=
      signTableFromRoots_eq_of_sign_eq p q roots card_le_p card_le_q hsign
    _ = rootSignTable q m degree_le_q :=
      (rootSignTable_eq_signTableFromRoots q degree_le_q roots hroots.symm card_le_q).symm

private theorem rootSignTable_scale_pos
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} (p : Fin r → R[X]) (c : Fin r → R)
    (hc : ∀ i, 0 < c i)
    (degree_le_p : ∀ i, (p i).natDegree ≤ m)
    (degree_le_scaled : ∀ i, (C (c i) * p i).natDegree ≤ m) :
    rootSignTable (fun i ↦ C (c i) * p i) m degree_le_scaled =
      rootSignTable p m degree_le_p := by
  apply rootSignTable_eq_of_familyRoots_eq
  · ext x
    simp only [familyRoots, Finset.mem_biUnion]
    constructor
    · rintro ⟨i, -, hx⟩
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simpa [Polynomial.roots_C_mul _ (ne_of_gt (hc i))] using hx
    · rintro ⟨i, -, hx⟩
      refine ⟨i, Finset.mem_univ i, ?_⟩
      simpa [Polynomial.roots_C_mul _ (ne_of_gt (hc i))] using hx
  · intro i x
    rw [eval_mul, eval_C, sign_mul, sign_pos (hc i), one_mul]

private def permuteSignTable {r m : ℕ} (e : Equiv.Perm (Fin r))
    (table : SignTable r m) : SignTable r m :=
  ⟨table.1, fun row column ↦ table.2 (e row) column⟩

private theorem permuteSignTable_symm {r m : ℕ} (e : Equiv.Perm (Fin r))
    (table : SignTable r m) :
    permuteSignTable e.symm (permuteSignTable e table) = table := by
  rcases table with ⟨rootCount, entries⟩
  refine signTable_ext_of_val' _ _ ?_ ?_
  · rfl
  · intro row column
    simp [permuteSignTable]
    congr

private theorem familyRoots_comp_equiv
    {R : Type u} [Field R] [LinearOrder R] {r : ℕ}
    (p : Fin r → R[X]) (e : Equiv.Perm (Fin r)) :
    familyRoots (p ∘ e) = familyRoots p := by
  ext x
  simp only [familyRoots, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨e i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨e.symm i, by simpa only [Function.comp_apply, e.apply_symm_apply] using hi⟩

private theorem signTableFromRoots_comp_equiv
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} (p : Fin r → R[X]) (e : Equiv.Perm (Fin r))
    (roots : Finset R) (card_le : roots.card ≤ r * m) :
    signTableFromRoots (p ∘ e) roots card_le =
      permuteSignTable e (signTableFromRoots p roots card_le) := by
  refine signTable_ext_of_val' _ _ (by rfl) ?_
  intro row column
  rfl

private theorem rootSignTable_comp_equiv
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} (p : Fin r → R[X]) (e : Equiv.Perm (Fin r))
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (degree_le_comp : ∀ i, (p (e i)).natDegree ≤ m) :
    rootSignTable (p ∘ e) m degree_le_comp =
      permuteSignTable e (rootSignTable p m degree_le) := by
  let roots := familyRoots p
  have card_le : roots.card ≤ r * m := familyRoots_card_le p m degree_le
  calc
    rootSignTable (p ∘ e) m degree_le_comp =
        signTableFromRoots (p ∘ e) roots card_le :=
      rootSignTable_eq_signTableFromRoots (p ∘ e) degree_le_comp roots
        (familyRoots_comp_equiv p e) card_le
    _ = permuteSignTable e (signTableFromRoots p roots card_le) :=
      signTableFromRoots_comp_equiv p e roots card_le
    _ = permuteSignTable e (rootSignTable p m degree_le) := by
      rw [rootSignTable_eq_signTableFromRoots p degree_le roots rfl card_le]

private theorem rootSignTable_eq_of_family_eq
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} {p q : Fin r → R[X]} (hp : ∀ i, (p i).natDegree ≤ m)
    (hq : ∀ i, (q i).natDegree ≤ m) (h : p = q) :
    rootSignTable p m hp = rootSignTable q m hq := by
  subst q
  rfl

private theorem rootSignTable_eq_permute_comp_equiv
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    {r m : ℕ} (p : Fin r → R[X]) (e : Equiv.Perm (Fin r))
    (degree_le : ∀ i, (p i).natDegree ≤ m)
    (degree_le_comp : ∀ i, (p (e i)).natDegree ≤ m) :
    rootSignTable p m degree_le =
      permuteSignTable e.symm (rootSignTable (p ∘ e) m degree_le_comp) := by
  rw [rootSignTable_comp_equiv p e degree_le degree_le_comp]
  exact (permuteSignTable_symm e (rootSignTable p m degree_le)).symm

private theorem parametricDegreeProfile_comp_equiv {A : Type u} [Semiring A]
    {a b : ℕ} (p : Fin b → A[X]) (e : Fin a ≃ Fin b) :
    parametricDegreeProfile (p ∘ e) = parametricDegreeProfile p := by
  unfold parametricDegreeProfile
  exact Fintype.sum_equiv e _ _ (fun i ↦ rfl)

private theorem parametricDegreeProfile_append {A : Type u} [Semiring A]
    {a b : ℕ} (p : Fin a → A[X]) (q : Fin b → A[X]) :
    parametricDegreeProfile (Fin.append p q) =
      parametricDegreeProfile p + parametricDegreeProfile q := by
  unfold parametricDegreeProfile
  rw [Fin.sum_univ_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.append_left]
  · apply Finset.sum_congr rfl
    intro i _
    rw [Fin.append_right]

private noncomputable def symbolicReductionDivisor {A : Type u} [CommRing A]
    {r : ℕ} (p : Fin (r + 1) → A[X]) : Fin (r + 1) → A[X] :=
  Fin.lastCases (p (Fin.last r)).derivative (fun i ↦ p i.castSucc)

private noncomputable def symbolicReducedFamily {A : Type u} [CommRing A]
    {r : ℕ} (p : Fin (r + 1) → A[X]) (M : ℕ) :
    Fin (2 * (r + 1)) → A[X] :=
  let q := symbolicReductionDivisor p
  (Fin.append q (fun i ↦ positivePseudoRemainder (p (Fin.last r)) (q i) M)) ∘
    Fin.cast (by omega : 2 * (r + 1) = (r + 1) + (r + 1))

private theorem symbolicReductionDivisor_degree_le {A : Type u} [CommRing A]
    {r M : ℕ} (p : Fin (r + 1) → A[X]) (degree_le : ∀ i, (p i).natDegree ≤ M) :
    ∀ i, (symbolicReductionDivisor p i).natDegree ≤ M := by
  intro i
  cases i using Fin.lastCases with
  | last =>
      simpa [symbolicReductionDivisor] using (Polynomial.natDegree_derivative_le
        (p (Fin.last r))).trans ((Nat.sub_le _ _).trans (degree_le (Fin.last r)))
  | cast i => simpa [symbolicReductionDivisor] using degree_le i.castSucc

private theorem symbolicReducedFamily_degree_le {A : Type u}
    [CommRing A] [NoZeroDivisors A] {r M : ℕ} (p : Fin (r + 1) → A[X])
    (degree_le : ∀ i, (p i).natDegree ≤ M)
    (divisor_ne_zero : ∀ i, symbolicReductionDivisor p i ≠ 0) :
    ∀ i, (symbolicReducedFamily p M i).natDegree ≤ M := by
  intro i
  unfold symbolicReducedFamily
  let j := Fin.cast (by omega : 2 * (r + 1) = (r + 1) + (r + 1)) i
  change (Fin.append (symbolicReductionDivisor p)
    (fun i ↦
      positivePseudoRemainder (p (Fin.last r)) (symbolicReductionDivisor p i) M)
      j).natDegree ≤ M
  cases j using Fin.addCases with
  | left j => simpa using symbolicReductionDivisor_degree_le p degree_le j
  | right j =>
      simp only [Fin.append_right]
      by_cases hzero : positivePseudoRemainder (p (Fin.last r))
          (symbolicReductionDivisor p j) M = 0
      · simp [hzero]
      · have hlt := (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr
          (positivePseudoRemainder_degree_lt (p (Fin.last r))
            (symbolicReductionDivisor p j) M (degree_le (Fin.last r))
            (symbolicReductionDivisor_degree_le p degree_le j) (divisor_ne_zero j))
        exact hlt.le.trans (symbolicReductionDivisor_degree_le p degree_le j)

private theorem symbolicReductionDivisor_profile {A : Type u} [CommRing A]
    {r : ℕ} (p : Fin (r + 1) → A[X]) :
    parametricDegreeProfile (symbolicReductionDivisor p) =
      parametricDegreeProfile (fun i : Fin r ↦ p i.castSucc) +
        polynomialComplexity (p (Fin.last r)).derivative := by
  unfold parametricDegreeProfile
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro i _
    simp [symbolicReductionDivisor]
  · simp [symbolicReductionDivisor]

private theorem family_profile_last {A : Type u} [Semiring A]
    {r : ℕ} (p : Fin (r + 1) → A[X]) :
    parametricDegreeProfile p =
      parametricDegreeProfile (fun i : Fin r ↦ p i.castSucc) +
        polynomialComplexity (p (Fin.last r)) := by
  unfold parametricDegreeProfile
  rw [Fin.sum_univ_castSucc]

private theorem symbolicReducedFamily_profile {A : Type u} [CommRing A]
    {r M : ℕ} (p : Fin (r + 1) → A[X]) :
    parametricDegreeProfile (symbolicReducedFamily p M) =
      parametricDegreeProfile (symbolicReductionDivisor p) +
        parametricDegreeProfile (fun i ↦ positivePseudoRemainder
          (p (Fin.last r)) (symbolicReductionDivisor p i) M) := by
  let e : Fin (2 * (r + 1)) ≃ Fin ((r + 1) + (r + 1)) :=
    finCongr (by omega)
  rw [show symbolicReducedFamily p M =
      (Fin.append (symbolicReductionDivisor p)
        (fun i ↦ positivePseudoRemainder (p (Fin.last r))
          (symbolicReductionDivisor p i) M)) ∘ e by rfl]
  rw [parametricDegreeProfile_comp_equiv, parametricDegreeProfile_append]

private theorem mem_polynomialComplexity_iff {A : Type u} [Semiring A]
    {p : A[X]} {degree : ℕ} :
    degree ∈ polynomialComplexity p ↔ p ≠ 0 ∧ degree = p.natDegree + 1 := by
  classical
  by_cases hp : p = 0
  · simp [polynomialComplexity, hp]
  · simp [polynomialComplexity, hp]

private theorem mem_parametricDegreeProfile_iff {A : Type u} [Semiring A]
    {r : ℕ} {p : Fin r → A[X]} {degree : ℕ} :
    degree ∈ parametricDegreeProfile p ↔
      ∃ i, degree ∈ polynomialComplexity (p i) := by
  classical
  unfold parametricDegreeProfile
  simp

private theorem symbolicReductionDivisor_ne_zero {A : Type u}
    [CommRing A] [NoZeroDivisors A] [CharZero A] {r : ℕ}
    (p : Fin (r + 1) → A[X]) (first_ne_zero : ∀ i : Fin r, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last r)).natDegree ≠ 0) :
    ∀ i, symbolicReductionDivisor p i ≠ 0 := by
  intro i
  cases i using Fin.lastCases with
  | last =>
      simpa [symbolicReductionDivisor] using Polynomial.derivative_ne_zero.mpr last_nonconstant
  | cast i => simpa [symbolicReductionDivisor] using first_ne_zero i

private theorem symbolicReductionDivisor_map {A : Type u} {K : Type v}
    [CommRing A] [Field K] {r : ℕ} (f : A →+* K)
    (p : Fin (r + 1) → A[X]) (i : Fin (r + 1)) :
    (symbolicReductionDivisor p i).map f =
      reductionDivisor (fun j ↦ (p j).map f) i := by
  cases i using Fin.lastCases with
  | last => simp [symbolicReductionDivisor, reductionDivisor, Polynomial.derivative_map]
  | cast i => simp [symbolicReductionDivisor, reductionDivisor]

private theorem symbolicReductionDivisor_lead_map_ne_zero {A : Type u} {K : Type v}
    [CommRing A] [IsAddTorsionFree A] [Field K] [CharZero K]
    {r : ℕ} (f : A →+* K)
    (p : Fin (r + 1) → A[X]) (leading_ne_zero : ∀ i, f (p i).leadingCoeff ≠ 0)
    (last_nonconstant : (p (Fin.last r)).natDegree ≠ 0) :
    ∀ i, f (symbolicReductionDivisor p i).leadingCoeff ≠ 0 := by
  intro i
  cases i using Fin.lastCases with
  | last =>
      rw [symbolicReductionDivisor, Fin.lastCases_last, Polynomial.leadingCoeff_derivative,
        map_mul, map_natCast]
      exact mul_ne_zero (leading_ne_zero (Fin.last r))
        (Nat.cast_ne_zero.mpr last_nonconstant)
  | cast i => simpa [symbolicReductionDivisor] using leading_ne_zero i.castSucc

private noncomputable def symbolicReductionScale {A : Type u} {K : Type v}
    [CommRing A] [Field K] {r : ℕ} (f : A →+* K)
    (p : Fin (r + 1) → A[X]) (M : ℕ) : Fin (2 * (r + 1)) → K := fun i ↦
  let j := Fin.cast (by omega : 2 * (r + 1) = (r + 1) + (r + 1)) i
  Fin.append (fun _ ↦ 1) (fun k ↦
    (f (symbolicReductionDivisor p k).leadingCoeff) ^
      (2 * (M - (symbolicReductionDivisor p k).natDegree + 1))) j

private theorem symbolicReductionScale_pos {A : Type u} {K : Type v}
    [CommRing A] [IsAddTorsionFree A] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [CharZero K]
    {r : ℕ} (f : A →+* K) (p : Fin (r + 1) → A[X]) (M : ℕ)
    (leading_ne_zero : ∀ i, f (p i).leadingCoeff ≠ 0)
    (last_nonconstant : (p (Fin.last r)).natDegree ≠ 0) :
    ∀ i, 0 < symbolicReductionScale f p M i := by
  intro i
  unfold symbolicReductionScale
  let j := Fin.cast (by omega : 2 * (r + 1) = (r + 1) + (r + 1)) i
  change 0 < Fin.append (fun _ : Fin (r + 1) ↦ (1 : K))
    (fun k ↦ (f (symbolicReductionDivisor p k).leadingCoeff) ^
      (2 * (M - (symbolicReductionDivisor p k).natDegree + 1))) j
  cases j using Fin.addCases with
  | left j => simp
  | right j =>
      simp only [Fin.append_right]
      have hne := symbolicReductionDivisor_lead_map_ne_zero f p leading_ne_zero
        last_nonconstant j
      rw [show 2 * (M - (symbolicReductionDivisor p j).natDegree + 1) =
        (M - (symbolicReductionDivisor p j).natDegree + 1) +
          (M - (symbolicReductionDivisor p j).natDegree + 1) by omega, pow_add]
      exact mul_self_pos.mpr (pow_ne_zero _ hne)

private theorem symbolicReducedFamily_map_eq_scale_reducedFamily
    {A : Type u} {K : Type v} [CommRing A] [Field K]
    {r M : ℕ} (f : A →+* K) (p : Fin (r + 1) → A[X])
    (degree_le : ∀ i, (p i).natDegree ≤ M)
    (divisor_lead_ne_zero : ∀ i, f (symbolicReductionDivisor p i).leadingCoeff ≠ 0) :
    ∀ i, (symbolicReducedFamily p M i).map f =
      C (symbolicReductionScale f p M i) *
        reducedFamily (fun j ↦ (p j).map f) i := by
  intro i
  unfold symbolicReducedFamily symbolicReductionScale reducedFamily
  simp only [Function.comp_apply]
  generalize Fin.cast (by omega : 2 * (r + 1) = (r + 1) + (r + 1)) i = j
  change (Fin.append (symbolicReductionDivisor p)
      (fun k ↦ positivePseudoRemainder (p (Fin.last r))
        (symbolicReductionDivisor p k) M) j).map f =
    C (Fin.append (fun _ : Fin (r + 1) ↦ (1 : K))
      (fun k ↦ (f (symbolicReductionDivisor p k).leadingCoeff) ^
        (2 * (M - (symbolicReductionDivisor p k).natDegree + 1))) j) *
      Fin.append (reductionDivisor (fun j ↦ (p j).map f))
        (fun j ↦ (p (Fin.last r)).map f %
          reductionDivisor (fun j ↦ (p j).map f) j) j
  cases j using Fin.addCases with
  | left j =>
      simp only [Fin.append_left, map_one, one_mul]
      rw [symbolicReductionDivisor_map]
  | right j =>
      simp only [Fin.append_right]
      rw [positivePseudoRemainder_map f (p (Fin.last r))
        (symbolicReductionDivisor p j) M (degree_le (Fin.last r))
        (symbolicReductionDivisor_degree_le p degree_le j) (divisor_lead_ne_zero j)]
      rw [symbolicReductionDivisor_map]

private theorem rootSignTable_symbolicReduced_map
    {A : Type u} {K : Type v} [CommRing A] [NoZeroDivisors A] [CharZero A]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K]
    {r M : ℕ} (f : A →+* K) (p : Fin (r + 1) → A[X])
    (degree_le : ∀ i, (p i).natDegree ≤ M)
    (first_ne_zero : ∀ i : Fin r, p i.castSucc ≠ 0)
    (last_nonconstant : (p (Fin.last r)).natDegree ≠ 0)
    (leading_ne_zero : ∀ i, f (p i).leadingCoeff ≠ 0) :
    let specialized := fun i ↦ (p i).map f
    let specializedReduced := fun i ↦ (symbolicReducedFamily p M i).map f
    let specializedDegree : ∀ i, (specialized i).natDegree ≤ M := fun i ↦
      Polynomial.natDegree_map_le.trans (degree_le i)
    let symbolicDegree : ∀ i, (specializedReduced i).natDegree ≤ M := fun i ↦
      Polynomial.natDegree_map_le.trans
        (symbolicReducedFamily_degree_le p degree_le
          (symbolicReductionDivisor_ne_zero p first_ne_zero last_nonconstant) i)
    rootSignTable specializedReduced M symbolicDegree =
      rootSignTable (reducedFamily specialized) M
        (reducedFamily_degree_le specialized M specializedDegree) := by
  dsimp only
  let specialized := fun i ↦ (p i).map f
  let scale := symbolicReductionScale f p M
  have divisorLead := symbolicReductionDivisor_lead_map_ne_zero f p leading_ne_zero
    last_nonconstant
  have hfamily : (fun i ↦ (symbolicReducedFamily p M i).map f) =
      (fun i ↦ C (scale i) * reducedFamily specialized i) := by
    funext i
    exact symbolicReducedFamily_map_eq_scale_reducedFamily f p degree_le divisorLead i
  have specializedDegree : ∀ i, (specialized i).natDegree ≤ M := fun i ↦
    Polynomial.natDegree_map_le.trans (degree_le i)
  have reducedDegree := reducedFamily_degree_le specialized M specializedDegree
  have scaledDegree : ∀ i, (C (scale i) * reducedFamily specialized i).natDegree ≤ M := by
    intro i
    rw [Polynomial.natDegree_C_mul
      (ne_of_gt (symbolicReductionScale_pos f p M leading_ne_zero last_nonconstant i))]
    exact reducedDegree i
  have symbolicDegree : ∀ i, ((symbolicReducedFamily p M i).map f).natDegree ≤ M :=
    fun i ↦ Polynomial.natDegree_map_le.trans
      (symbolicReducedFamily_degree_le p degree_le
        (symbolicReductionDivisor_ne_zero p first_ne_zero last_nonconstant) i)
  have htable : rootSignTable (fun i ↦ (symbolicReducedFamily p M i).map f) M
      symbolicDegree = rootSignTable (fun i ↦ C (scale i) * reducedFamily specialized i) M
        scaledDegree := by
    apply rootSignTable_eq_of_familyRoots_eq
    · exact congrArg familyRoots hfamily
    · intro i x
      rw [congrFun hfamily i]
  calc
    rootSignTable (fun i ↦ (symbolicReducedFamily p M i).map f) M symbolicDegree =
        rootSignTable (fun i ↦ C (scale i) * reducedFamily specialized i) M scaledDegree := htable
    _ = rootSignTable (reducedFamily specialized) M reducedDegree :=
      rootSignTable_scale_pos (reducedFamily specialized) scale
        (symbolicReductionScale_pos f p M leading_ne_zero last_nonconstant)
        reducedDegree scaledDegree

private noncomputable def cleanFamily {A : Type u} [CommRing A] {r : ℕ}
    (p : Fin r → A[X]) : Fin r → A[X] := by
  classical
  exact fun i ↦ if p i = 0 then 1 else p i

private theorem cleanFamily_ne_zero {A : Type u} [CommRing A] [Nontrivial A] {r : ℕ}
    (p : Fin r → A[X]) : ∀ i, cleanFamily p i ≠ 0 := by
  classical
  intro i
  by_cases hp : p i = 0
  · simp [cleanFamily, hp]
  · simp [cleanFamily, hp]

private theorem cleanFamily_degree_le {A : Type u} [CommRing A] {r M : ℕ}
    (p : Fin r → A[X]) (degree_le : ∀ i, (p i).natDegree ≤ M) :
    ∀ i, (cleanFamily p i).natDegree ≤ M := by
  classical
  intro i
  by_cases hp : p i = 0
  · simp [cleanFamily, hp]
  · simpa [cleanFamily, hp] using degree_le i

private noncomputable def restoreZeroRows {A : Type u} [CommRing A] {r m : ℕ}
    (p : Fin r → A[X]) (table : SignTable r m) : SignTable r m := by
  classical
  exact ⟨table.1, fun row column ↦ if p row = 0 then 0 else table.2 row column⟩

private theorem familyRoots_clean_map {A : Type u} {K : Type v}
    [CommRing A] [Nontrivial A] [Field K] [LinearOrder K] {r : ℕ} (f : A →+* K)
    (p : Fin r → A[X]) :
    familyRoots (fun i ↦ (cleanFamily p i).map f) =
      familyRoots (fun i ↦ (p i).map f) := by
  classical
  ext x
  simp only [familyRoots, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    by_cases hp : p i = 0
    · simp [cleanFamily, hp] at hi
    · exact ⟨i, by simpa [cleanFamily, hp] using hi⟩
  · rintro ⟨i, hi⟩
    by_cases hp : p i = 0
    · simp [hp] at hi
    · exact ⟨i, by simpa [cleanFamily, hp] using hi⟩

private theorem rootSignTable_clean_map {A : Type u} {K : Type v}
    [CommRing A] [Nontrivial A] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r M : ℕ} (f : A →+* K) (p : Fin r → A[X])
    (degree_le : ∀ i, (p i).natDegree ≤ M) :
    let originalDegree : ∀ i, ((p i).map f).natDegree ≤ M := fun i ↦
      Polynomial.natDegree_map_le.trans (degree_le i)
    let cleanDegree : ∀ i, ((cleanFamily p i).map f).natDegree ≤ M := fun i ↦
      Polynomial.natDegree_map_le.trans (cleanFamily_degree_le p degree_le i)
    rootSignTable (fun i ↦ (p i).map f) M originalDegree =
      restoreZeroRows p (rootSignTable (fun i ↦ (cleanFamily p i).map f) M cleanDegree) := by
  dsimp only
  let roots := familyRoots (fun i ↦ (p i).map f)
  have originalDegree : ∀ i, ((p i).map f).natDegree ≤ M := fun i ↦
    Polynomial.natDegree_map_le.trans (degree_le i)
  have cleanDegree : ∀ i, ((cleanFamily p i).map f).natDegree ≤ M := fun i ↦
    Polynomial.natDegree_map_le.trans (cleanFamily_degree_le p degree_le i)
  have card_le : roots.card ≤ r * M := familyRoots_card_le _ M originalDegree
  have hcleanRoots := familyRoots_clean_map f p
  rw [rootSignTable_eq_signTableFromRoots _ originalDegree roots rfl card_le]
  rw [rootSignTable_eq_signTableFromRoots _ cleanDegree roots hcleanRoots card_le]
  refine signTable_ext_of_val' _ _ (by rfl) ?_
  intro row column
  by_cases hp : p row = 0
  · simp [signTableFromRoots, restoreZeroRows, hp]
  · simp only [signTableFromRoots, restoreZeroRows, cleanFamily, hp, ↓reduceIte]
    congr 3

private noncomputable def zeroReplacementComplexity {A : Type u} [Semiring A]
    (p : A[X]) : Multiset ℕ := by
  classical
  exact if p = 0 then {1} else ∅

private theorem complexity_cleanFamily {A : Type u} [CommRing A] [Nontrivial A] {r : ℕ}
    (p : Fin r → A[X]) (i : Fin r) :
    polynomialComplexity (cleanFamily p i) =
      polynomialComplexity (p i) + zeroReplacementComplexity (p i) := by
  classical
  by_cases hp : p i = 0
  · have hone : (1 : A[X]) ≠ 0 := one_ne_zero
    simp [cleanFamily, polynomialComplexity, zeroReplacementComplexity, hp, hone]
  · simp [cleanFamily, zeroReplacementComplexity, hp]

private theorem cleanFamily_profile {A : Type u} [CommRing A] [Nontrivial A] {r : ℕ}
    (p : Fin r → A[X]) :
    parametricDegreeProfile (cleanFamily p) = parametricDegreeProfile p +
      ∑ i, zeroReplacementComplexity (p i) := by
  unfold parametricDegreeProfile
  simp_rw [complexity_cleanFamily]
  exact Finset.sum_add_distrib

private theorem mem_zeroReplacementComplexity {A : Type u} [Semiring A]
    {p : A[X]} {degree : ℕ} (h : degree ∈ zeroReplacementComplexity p) : degree = 1 := by
  classical
  by_cases hp : p = 0
  · simpa [zeroReplacementComplexity, hp] using h
  · simp [zeroReplacementComplexity, hp] at h

private theorem symbolicReducedFamily_clean_profile_lt {A : Type u}
    [CommRing A] [Nontrivial A] [NoZeroDivisors A] [CharZero A] {r M : ℕ}
    (p : Fin (r + 1) → A[X]) (degree_le : ∀ i, (p i).natDegree ≤ M)
    (last_nonconstant : (p (Fin.last r)).natDegree ≠ 0)
    (last_maximal : ∀ i, (p i).natDegree ≤ (p (Fin.last r)).natDegree) :
    Multiset.IsDershowitzMannaLT
      (parametricDegreeProfile (symbolicReducedFamily (cleanFamily p) M))
      (parametricDegreeProfile p) := by
  classical
  have hlast0 : p (Fin.last r) ≠ 0 :=
    ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero last_nonconstant)
  have hcleanLast : cleanFamily p (Fin.last r) = p (Fin.last r) := by
    simp [cleanFamily, hlast0]
  have hcleanDegree : ∀ i, (cleanFamily p i).natDegree ≤ M :=
    cleanFamily_degree_le p degree_le
  have hcleanMaximal : ∀ i,
      (cleanFamily p i).natDegree ≤ (cleanFamily p (Fin.last r)).natDegree := by
    intro i
    by_cases hi : p i = 0
    · simp [cleanFamily, hi, hlast0]
    · simpa [cleanFamily, hi, hlast0] using last_maximal i
  have hcleanLastNonconstant : (cleanFamily p (Fin.last r)).natDegree ≠ 0 := by
    simpa [hcleanLast] using last_nonconstant
  have hcleanFirst : ∀ i : Fin r, cleanFamily p i.castSucc ≠ 0 := fun i ↦
    cleanFamily_ne_zero p i.castSucc
  let initial := parametricDegreeProfile (fun i : Fin r ↦ p i.castSucc)
  let replacements := ∑ i : Fin r, zeroReplacementComplexity (p i.castSucc)
  let remainders := parametricDegreeProfile (fun i ↦ positivePseudoRemainder
    (p (Fin.last r)) (symbolicReductionDivisor (cleanFamily p) i) M)
  let smaller := replacements + polynomialComplexity (p (Fin.last r)).derivative + remainders
  refine ⟨initial, smaller, {(p (Fin.last r)).natDegree + 1}, by simp, ?_, ?_, ?_⟩
  · have hfirstProfile :
        parametricDegreeProfile (fun i : Fin r ↦ cleanFamily p i.castSucc) =
          initial + replacements := by
      change parametricDegreeProfile (cleanFamily (fun i : Fin r ↦ p i.castSucc)) = _
      simpa [initial, replacements] using
        (cleanFamily_profile (fun i : Fin r ↦ p i.castSucc))
    rw [symbolicReducedFamily_profile, symbolicReductionDivisor_profile, hfirstProfile,
      hcleanLast]
    simp only [initial, replacements, remainders, smaller, add_assoc]
  · rw [family_profile_last, polynomialComplexity_eq_singleton hlast0]
  · intro degree hdegree
    simp only [smaller, Multiset.mem_add] at hdegree
    rcases hdegree with (hreplacement | hderivative) | hremainder
    · rw [Multiset.mem_sum] at hreplacement
      obtain ⟨i, _, hi⟩ := hreplacement
      rw [mem_zeroReplacementComplexity hi]
      refine ⟨(p (Fin.last r)).natDegree + 1, by simp, ?_⟩
      omega
    · rw [mem_polynomialComplexity_iff] at hderivative
      rcases hderivative with ⟨_, rfl⟩
      refine ⟨(p (Fin.last r)).natDegree + 1, by simp, ?_⟩
      have hderivativeDegree := Polynomial.natDegree_derivative_lt last_nonconstant
      omega
    · rw [mem_parametricDegreeProfile_iff] at hremainder
      obtain ⟨i, hi⟩ := hremainder
      rw [mem_polynomialComplexity_iff] at hi
      rcases hi with ⟨hrem0, rfl⟩
      refine ⟨(p (Fin.last r)).natDegree + 1, by simp, ?_⟩
      have hdivisor0 := symbolicReductionDivisor_ne_zero (cleanFamily p)
        hcleanFirst hcleanLastNonconstant i
      have hdegree := positivePseudoRemainder_degree_lt (cleanFamily p (Fin.last r))
        (symbolicReductionDivisor (cleanFamily p) i) M
        (hcleanDegree (Fin.last r))
        (symbolicReductionDivisor_degree_le (cleanFamily p) hcleanDegree i) hdivisor0
      rw [hcleanLast] at hdegree
      have hnat := (Polynomial.natDegree_lt_iff_degree_lt hrem0).mpr hdegree
      have hdivisorDegree :=
        symbolicReductionDivisor_degree_le (cleanFamily p) hcleanMaximal i
      rw [hcleanLast] at hdivisorDegree
      exact Nat.succ_lt_succ
        (hnat.trans_le hdivisorDegree)

private theorem rootSignTable_C {R : Type u} [Field R] [LinearOrder R]
    [IsStrictOrderedRing R] {r m : ℕ} (c : Fin r → R)
    (degree_le : ∀ i, (C (c i)).natDegree ≤ m) :
    rootSignTable (fun i ↦ C (c i)) m degree_le =
      constantSignTable (fun i ↦ SignType.sign (c i)) := by
  classical
  have hroots : familyRoots (fun i ↦ C (c i)) = ∅ := by
    ext x
    simp [familyRoots]
  rw [show rootSignTable (fun i ↦ C (c i)) m degree_le =
      ⟨⟨(familyRoots (fun i ↦ C (c i))).card,
        Nat.lt_succ_of_le (familyRoots_card_le (fun i ↦ C (c i)) m degree_le)⟩,
        fun row column ↦ SignType.sign ((C (c row)).eval
          ((cellSamples ((familyRoots (fun i ↦ C (c i))).sort (· ≤ ·))).get
            (Fin.cast (by simp [cellSamples_length]) column)))⟩ by rfl]
  refine signTable_ext_of_val' _ _ ?_ ?_
  · simp [hroots, constantSignTable]
  · intro row column
    simp [hroots, constantSignTable, cellSamples]

private theorem rootSignTable_map_eq_constant {n r m : ℕ}
    (p : Fin r → (IntPolynomial n)[X]) (degree_le : ∀ i, (p i).natDegree ≤ m)
    (constant : ∀ i, (p i).natDegree = 0)
    {R : Type u} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (y : Fin n → R) :
    let f := MvPolynomial.eval₂Hom (Int.castRingHom R) y
    let specialized := fun i ↦ (p i).map f
    let specializedDegree : ∀ i, (specialized i).natDegree ≤ m := fun i ↦
      Polynomial.natDegree_map_le.trans (degree_le i)
    rootSignTable specialized m specializedDegree =
      constantSignTable (fun i ↦ SignType.sign (f ((p i).coeff 0))) := by
  dsimp only
  let f := MvPolynomial.eval₂Hom (Int.castRingHom R) y
  let specialized := fun i ↦ (p i).map f
  let constants := fun i ↦ C (f ((p i).coeff 0))
  have hfamily : specialized = constants := by
    funext i
    change (p i).map f = C (f ((p i).coeff 0))
    rw [Polynomial.eq_C_of_natDegree_eq_zero (constant i)]
    simp
  have specializedDegree : ∀ i, (specialized i).natDegree ≤ m := fun i ↦
    Polynomial.natDegree_map_le.trans (degree_le i)
  have constantDegree : ∀ i, (constants i).natDegree ≤ m := by
    intro i
    rw [← hfamily]
    exact specializedDegree i
  calc
    rootSignTable specialized m specializedDegree =
        rootSignTable constants m constantDegree :=
      rootSignTable_eq_of_family_eq specializedDegree constantDegree hfamily
    _ = constantSignTable (fun i ↦ SignType.sign (f ((p i).coeff 0))) :=
      rootSignTable_C (fun i ↦ f ((p i).coeff 0)) constantDegree

private theorem rootSignTable_eq_restore_reconstruct
    {A : Type u} {K : Type v} [CommRing A] [Nontrivial A] [NoZeroDivisors A] [CharZero A]
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [CharZero K]
    {r M : ℕ} (f : A →+* K) (p : Fin (r + 1) → A[X])
    (degree_le : ∀ i, (p i).natDegree ≤ M)
    (last_nonconstant : (p (Fin.last r)).natDegree ≠ 0)
    (leading_ne_zero : ∀ i, p i ≠ 0 → f (p i).leadingCoeff ≠ 0)
    (reconstruct : SignTable (2 * (r + 1)) M → SignTable (r + 1) M)
    (reconstruct_spec :
      let cleaned := cleanFamily p
      let specializedCleaned := fun i ↦ (cleaned i).map f
      let cleanedDegree : ∀ i, (specializedCleaned i).natDegree ≤ M := fun i ↦
        Polynomial.natDegree_map_le.trans (cleanFamily_degree_le p degree_le i)
      rootSignTable specializedCleaned M cleanedDegree =
        reconstruct (rootSignTable (reducedFamily specializedCleaned) M
          (reducedFamily_degree_le specializedCleaned M cleanedDegree))) :
    let specialized := fun i ↦ (p i).map f
    let reduced := symbolicReducedFamily (cleanFamily p) M
    let specializedDegree : ∀ i, (specialized i).natDegree ≤ M := fun i ↦
      Polynomial.natDegree_map_le.trans (degree_le i)
    let reducedDegree : ∀ i, ((reduced i).map f).natDegree ≤ M := fun i ↦
      Polynomial.natDegree_map_le.trans
        (symbolicReducedFamily_degree_le (cleanFamily p)
          (cleanFamily_degree_le p degree_le)
          (symbolicReductionDivisor_ne_zero (cleanFamily p)
            (fun i ↦ cleanFamily_ne_zero p i.castSucc)
            (by simpa [cleanFamily,
                ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero last_nonconstant)] using
              last_nonconstant)) i)
    rootSignTable specialized M specializedDegree =
      restoreZeroRows p (reconstruct
        (rootSignTable (fun i ↦ (reduced i).map f) M reducedDegree)) := by
  dsimp only
  have hlast0 : p (Fin.last r) ≠ 0 :=
    ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero last_nonconstant)
  have hcleanLastNonconstant : (cleanFamily p (Fin.last r)).natDegree ≠ 0 := by
    simpa [cleanFamily, hlast0] using last_nonconstant
  have hcleanLeading : ∀ i, f (cleanFamily p i).leadingCoeff ≠ 0 := by
    intro i
    by_cases hi : p i = 0
    · simp [cleanFamily, hi]
    · simpa [cleanFamily, hi] using leading_ne_zero i hi
  let specialized := fun i ↦ (p i).map f
  let cleaned := cleanFamily p
  let specializedCleaned := fun i ↦ (cleaned i).map f
  let reduced := symbolicReducedFamily cleaned M
  have specializedDegree : ∀ i, (specialized i).natDegree ≤ M := fun i ↦
    Polynomial.natDegree_map_le.trans (degree_le i)
  have cleanedDegree : ∀ i, (specializedCleaned i).natDegree ≤ M := fun i ↦
    Polynomial.natDegree_map_le.trans (cleanFamily_degree_le p degree_le i)
  have reducedDegree : ∀ i, ((reduced i).map f).natDegree ≤ M := fun i ↦
    Polynomial.natDegree_map_le.trans
      (symbolicReducedFamily_degree_le cleaned (cleanFamily_degree_le p degree_le)
        (symbolicReductionDivisor_ne_zero cleaned
          (fun i ↦ cleanFamily_ne_zero p i.castSucc) hcleanLastNonconstant) i)
  have hclean := rootSignTable_clean_map f p degree_le
  have hsymbolic := rootSignTable_symbolicReduced_map f cleaned
    (cleanFamily_degree_le p degree_le) (fun i ↦ cleanFamily_ne_zero p i.castSucc)
    hcleanLastNonconstant hcleanLeading
  calc
    rootSignTable specialized M specializedDegree =
        restoreZeroRows p (rootSignTable specializedCleaned M cleanedDegree) := hclean
    _ = restoreZeroRows p (reconstruct
          (rootSignTable (reducedFamily specializedCleaned) M
            (reducedFamily_degree_le specializedCleaned M cleanedDegree))) :=
      congrArg (restoreZeroRows p) reconstruct_spec
    _ = restoreZeroRows p (reconstruct
          (rootSignTable (fun i ↦ (reduced i).map f) M reducedDegree)) :=
      congrArg (fun table ↦ restoreZeroRows p (reconstruct table)) hsymbolic.symm

private theorem symbolic_signTable_preimage_definable {n s m : ℕ}
    (p : Fin s → (IntPolynomial n)[X]) (degree_le : ∀ i, (p i).natDegree ≤ m)
    (tables : Set (SignTable s m)) :
    ∃ formula : Formula n,
      ∀ (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
        (y : Fin n → R),
        let f := MvPolynomial.eval₂Hom (Int.castRingHom R) y
        let specialized := fun i ↦ (p i).map f
        let specializedDegree : ∀ i, (specialized i).natDegree ≤ m := fun i ↦
          Polynomial.natDegree_map_le.trans (degree_le i)
        rootSignTable specialized m specializedDegree ∈ tables ↔ formula.Realize y := by
  classical
  let P : Multiset ℕ → Prop := fun profile ↦
    ∀ (familySize : ℕ) (q : Fin familySize → (IntPolynomial n)[X]),
      parametricDegreeProfile q = profile →
      ∀ (qDegree : ∀ i, (q i).natDegree ≤ m) (qTables : Set (SignTable familySize m)),
        ∃ formula : Formula n,
          ∀ (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
            (y : Fin n → R),
            let f := MvPolynomial.eval₂Hom (Int.castRingHom R) y
            let specialized := fun i ↦ (q i).map f
            let specializedDegree : ∀ i, (specialized i).natDegree ≤ m := fun i ↦
              Polynomial.natDegree_map_le.trans (qDegree i)
            rootSignTable specialized m specializedDegree ∈ qTables ↔ formula.Realize y
  suffices hP : P (parametricDegreeProfile p) by
    exact hP s p rfl degree_le tables
  apply Multiset.wellFounded_isDershowitzMannaLT.induction
  intro profile ih familySize p hprofile degree_le tables
  by_cases hconstant : ∀ i, (p i).natDegree = 0
  · refine ⟨Formula.constantCase p tables, ?_⟩
    intro R _ _ _ _ y
    dsimp only
    rw [rootSignTable_map_eq_constant p degree_le hconstant y]
    exact (Formula.realize_constantCase_iff p tables y).symm
  · cases familySize with
    | zero =>
        exact (hconstant (fun i ↦ Fin.elim0 i)).elim
    | succ r =>
      obtain ⟨maxIndex, _, hmaximal⟩ := Finset.exists_max_image
        (Finset.univ : Finset (Fin (r + 1))) (fun i ↦ (p i).natDegree)
        Finset.univ_nonempty
      have hmaxNonconstant : (p maxIndex).natDegree ≠ 0 := by
        intro hzero
        apply hconstant
        intro i
        have hi := hmaximal i (Finset.mem_univ i)
        omega
      let e : Equiv.Perm (Fin (r + 1)) := Equiv.swap maxIndex (Fin.last r)
      let permuted := p ∘ e
      have hpermutedDegree : ∀ i, (permuted i).natDegree ≤ m := fun i ↦ degree_le (e i)
      have hpermutedLast : permuted (Fin.last r) = p maxIndex := by
        simp [permuted, e]
      have hpermutedLastNonconstant : (permuted (Fin.last r)).natDegree ≠ 0 := by
        simpa [hpermutedLast] using hmaxNonconstant
      have hpermutedLastMaximal : ∀ i,
          (permuted i).natDegree ≤ (permuted (Fin.last r)).natDegree := by
        intro i
        rw [hpermutedLast]
        exact hmaximal (e i) (Finset.mem_univ (e i))
      have hpermutedProfile : parametricDegreeProfile permuted =
          parametricDegreeProfile p := by
        exact parametricDegreeProfile_comp_equiv p e
      let permutedTables : Set (SignTable (r + 1) m) :=
        {table | permuteSignTable e.symm table ∈ tables}
      obtain ⟨reconstruct, reconstruct_spec⟩ := exists_reconstruction r m
      let reduced := symbolicReducedFamily (cleanFamily permuted) m
      have hcleanedDivisor : ∀ i, symbolicReductionDivisor (cleanFamily permuted) i ≠ 0 :=
        symbolicReductionDivisor_ne_zero (cleanFamily permuted)
          (fun i ↦ cleanFamily_ne_zero permuted i.castSucc)
          (by simpa [cleanFamily,
              ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero hpermutedLastNonconstant)] using
            hpermutedLastNonconstant)
      have hReducedDegree : ∀ i, (reduced i).natDegree ≤ m :=
        symbolicReducedFamily_degree_le (cleanFamily permuted)
          (cleanFamily_degree_le permuted hpermutedDegree) hcleanedDivisor
      have hReducedLt : Multiset.IsDershowitzMannaLT
          (parametricDegreeProfile reduced) profile := by
        rw [← hprofile, ← hpermutedProfile]
        exact symbolicReducedFamily_clean_profile_lt permuted hpermutedDegree
          hpermutedLastNonconstant hpermutedLastMaximal
      let reducedTables : Set (SignTable (2 * (r + 1)) m) :=
        {table | permuteSignTable e.symm
          (restoreZeroRows permuted (reconstruct table)) ∈ tables}
      obtain ⟨reducedFormula, reducedFormula_spec⟩ :=
        ih (parametricDegreeProfile reduced) hReducedLt (2 * (r + 1))
          reduced rfl hReducedDegree reducedTables
      have hTruncatedLt (i : Fin (r + 1)) (hi : permuted i ≠ 0) :
          Multiset.IsDershowitzMannaLT
            (parametricDegreeProfile (truncateFamily permuted i)) profile := by
        rw [← hprofile, ← hpermutedProfile]
        exact truncateFamily_profile_lt permuted i hi
      have truncatedWitness (i : Fin (r + 1)) (hi : permuted i ≠ 0) :
          ∃ formula : Formula n,
            ∀ (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
              (y : Fin n → R),
              let f := MvPolynomial.eval₂Hom (Int.castRingHom R) y
              let specialized := fun j ↦ (truncateFamily permuted i j).map f
              let specializedDegree : ∀ j, (specialized j).natDegree ≤ m := fun j ↦
                Polynomial.natDegree_map_le.trans
                  (truncateFamily_degree_le permuted hpermutedDegree i j)
              rootSignTable specialized m specializedDegree ∈ permutedTables ↔
                formula.Realize y :=
        ih (parametricDegreeProfile (truncateFamily permuted i)) (hTruncatedLt i hi)
          (r + 1) (truncateFamily permuted i) rfl
          (truncateFamily_degree_le permuted hpermutedDegree i) permutedTables
      let exceptionalFormula (i : Fin (r + 1)) : Formula n :=
        if hi : permuted i = 0 then .falsum else (truncatedWitness i hi).choose
      have exceptionalFormula_spec (i : Fin (r + 1)) (hi : permuted i ≠ 0) :
          ∀ (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
            (y : Fin n → R),
            let f := MvPolynomial.eval₂Hom (Int.castRingHom R) y
            let specialized := fun j ↦ (truncateFamily permuted i j).map f
            let specializedDegree : ∀ j, (specialized j).natDegree ≤ m := fun j ↦
              Polynomial.natDegree_map_le.trans
                (truncateFamily_degree_le permuted hpermutedDegree i j)
            rootSignTable specialized m specializedDegree ∈ permutedTables ↔
              (exceptionalFormula i).Realize y := by
        intro R _ _ _ _ y
        rw [show exceptionalFormula i = (truncatedWitness i hi).choose by
          simp [exceptionalFormula, hi]]
        exact (truncatedWitness i hi).choose_spec R y
      let exceptionalDisjunction := Formula.disjunction (List.ofFn fun i ↦
        Formula.and (.sign (permuted i).leadingCoeff 0) (exceptionalFormula i))
      let formula := Formula.or
        (Formula.and (Formula.allLeadingNonzero permuted) reducedFormula)
        exceptionalDisjunction
      refine ⟨formula, ?_⟩
      intro R _ _ _ _ y
      dsimp only
      let f := MvPolynomial.eval₂Hom (Int.castRingHom R) y
      let specialized := fun i ↦ (p i).map f
      let specializedPermuted := fun i ↦ (permuted i).map f
      have specializedDegree : ∀ i, (specialized i).natDegree ≤ m := fun i ↦
        Polynomial.natDegree_map_le.trans (degree_le i)
      have specializedPermutedDegree : ∀ i, (specializedPermuted i).natDegree ≤ m := fun i ↦
        Polynomial.natDegree_map_le.trans (hpermutedDegree i)
      have hspecializedComp : specialized ∘ e = specializedPermuted := by
        funext i
        rfl
      have hrootPermuted : rootSignTable specialized m specializedDegree =
          permuteSignTable e.symm
            (rootSignTable specializedPermuted m specializedPermutedDegree) := by
        have h := rootSignTable_eq_permute_comp_equiv specialized e specializedDegree
          (fun i ↦ specializedDegree (e i))
        have hcomp := rootSignTable_eq_of_family_eq (fun i ↦ specializedDegree (e i))
          specializedPermutedDegree hspecializedComp
        exact h.trans (congrArg (permuteSignTable e.symm) hcomp)
      rw [hrootPermuted]
      change rootSignTable specializedPermuted m specializedPermutedDegree ∈ permutedTables ↔
        formula.Realize y
      have hExceptionalRealize : exceptionalDisjunction.Realize y ↔
          ∃ i : Fin (r + 1),
            (Formula.sign (permuted i).leadingCoeff 0).Realize y ∧
              (exceptionalFormula i).Realize y := by
        change (Formula.disjunction (List.ofFn fun i ↦
          Formula.and (.sign (permuted i).leadingCoeff 0)
            (exceptionalFormula i))).Realize y ↔ _
        rw [Formula.realize_disjunction_iff]
        simp only [List.mem_ofFn', Set.mem_range, exists_exists_eq_and,
          Formula.Realize]
      change rootSignTable specializedPermuted m specializedPermutedDegree ∈ permutedTables ↔
        ((Formula.allLeadingNonzero permuted).Realize y ∧ reducedFormula.Realize y) ∨
          exceptionalDisjunction.Realize y
      rw [hExceptionalRealize]
      have hAllLeading := Formula.realize_allLeadingNonzero_iff permuted y
      by_cases hall : ∀ i, permuted i ≠ 0 → f (permuted i).leadingCoeff ≠ 0
      · have hmain :
            rootSignTable specializedPermuted m specializedPermutedDegree ∈ permutedTables ↔
              reducedFormula.Realize y := by
          let cleaned := cleanFamily permuted
          let specializedCleaned := fun i ↦ (cleaned i).map f
          have cleanedDegree : ∀ i, (specializedCleaned i).natDegree ≤ m := fun i ↦
            Polynomial.natDegree_map_le.trans
              (cleanFamily_degree_le permuted hpermutedDegree i)
          have hcleanLeading : ∀ i, f (cleaned i).leadingCoeff ≠ 0 := by
            intro i
            by_cases hi : permuted i = 0
            · simp [cleaned, cleanFamily, hi]
            · simpa [cleaned, cleanFamily, hi] using hall i hi
          have hfirstSpecialized : ∀ i : Fin r, specializedCleaned i.castSucc ≠ 0 :=
            fun i ↦ map_ne_zero_of_leadingCoeff_ne_zero f (cleaned i.castSucc)
              (hcleanLeading i.castSucc)
          have hlastSpecialized :
              (specializedCleaned (Fin.last r)).natDegree ≠ 0 := by
            rw [Polynomial.natDegree_map_of_leadingCoeff_ne_zero f
              (hcleanLeading (Fin.last r))]
            simpa [cleaned, cleanFamily,
              ne_zero_of_natDegree_gt (Nat.pos_of_ne_zero hpermutedLastNonconstant)] using
              hpermutedLastNonconstant
          have hreconstruct := reconstruct_spec R specializedCleaned cleanedDegree
            hfirstSpecialized hlastSpecialized
          have hroot := rootSignTable_eq_restore_reconstruct f permuted hpermutedDegree
            hpermutedLastNonconstant hall reconstruct hreconstruct
          let specializedReduced := fun i ↦ (reduced i).map f
          have specializedReducedDegree : ∀ i, (specializedReduced i).natDegree ≤ m := fun i ↦
            Polynomial.natDegree_map_le.trans (hReducedDegree i)
          have hrecursive := reducedFormula_spec R y
          change rootSignTable specializedReduced m specializedReducedDegree ∈ reducedTables ↔
            reducedFormula.Realize y at hrecursive
          rw [hroot]
          exact hrecursive
        have hexceptionFalse : ¬∃ i : Fin (r + 1),
            (Formula.sign (permuted i).leadingCoeff 0).Realize y ∧
              (exceptionalFormula i).Realize y := by
          rintro ⟨i, hsign, hformula⟩
          by_cases hi : permuted i = 0
          · simp [exceptionalFormula, hi, Formula.Realize] at hformula
          · exact (hall i hi) (sign_eq_zero_iff.mp hsign)
        simp only [hAllLeading.mpr hall, true_and, hexceptionFalse, or_false]
        exact hmain
      · have hallFalse : ¬(Formula.allLeadingNonzero permuted).Realize y := by
          exact fun h ↦ hall (hAllLeading.mp h)
        have hexists : ∃ i : Fin (r + 1),
            permuted i ≠ 0 ∧ f (permuted i).leadingCoeff = 0 := by
          push Not at hall
          exact hall
        have exception_equiv (i : Fin (r + 1)) (hi : permuted i ≠ 0)
            (hlead : f (permuted i).leadingCoeff = 0) :
            rootSignTable specializedPermuted m specializedPermutedDegree ∈ permutedTables ↔
              (exceptionalFormula i).Realize y := by
          let specializedTruncated := fun j ↦ (truncateFamily permuted i j).map f
          have specializedTruncatedDegree : ∀ j,
              (specializedTruncated j).natDegree ≤ m := fun j ↦
            Polynomial.natDegree_map_le.trans
              (truncateFamily_degree_le permuted hpermutedDegree i j)
          have hfamily := truncateFamily_map_eq f permuted i hlead
          have hroot := rootSignTable_eq_of_family_eq specializedTruncatedDegree
            specializedPermutedDegree hfamily
          have hrecursive := exceptionalFormula_spec i hi R y
          change rootSignTable specializedTruncated m specializedTruncatedDegree ∈
              permutedTables ↔ (exceptionalFormula i).Realize y at hrecursive
          rw [hroot] at hrecursive
          exact hrecursive
        constructor
        · intro htable
          right
          obtain ⟨i, hi, hlead⟩ := hexists
          refine ⟨i, ?_, (exception_equiv i hi hlead).mp htable⟩
          exact sign_eq_zero_iff.mpr hlead
        · rintro (hmain | ⟨i, hsign, hformula⟩)
          · exact (hallFalse hmain.1).elim
          · by_cases hi : permuted i = 0
            · simp [exceptionalFormula, hi, Formula.Realize] at hformula
            · exact (exception_equiv i hi (sign_eq_zero_iff.mp hsign)).mpr hformula

/-! ## Parametric induction: Proposition 1.4.6 -/

/-- Degree in the variable that will be eliminated. -/
noncomputable def xDegree (p : IntPolynomialWithParameter n) : ℕ :=
  (MvPolynomial.finSuccEquiv ℤ n p).natDegree

/-- A uniform degree bound for a finite family. -/
noncomputable def maxXDegree (p : Fin s → IntPolynomialWithParameter n) : ℕ :=
  Finset.univ.sup fun i ↦ xDegree (p i)

theorem xDegree_le_maxXDegree (p : Fin s → IntPolynomialWithParameter n) (i : Fin s) :
    xDegree (p i) ≤ maxXDegree p := by
  exact Finset.le_sup (s := (Finset.univ : Finset (Fin s))) (f := fun j ↦ xDegree (p j))
    (Finset.mem_univ i)

/-- Specializing parameters cannot increase degree in the eliminated variable. -/
theorem specialize_degree_le {R : Type u} [CommRing R]
    (p : IntPolynomialWithParameter n) (y : Fin n → R) :
    (specialize p y).natDegree ≤ xDegree p := by
  exact Polynomial.natDegree_map_le

/-- Book Proposition 1.4.6: the inverse image of any collection of sign tables is definable by a
quantifier-free Boolean combination of sign conditions on integer polynomials.

The proof splits on the leading coefficients.  When they are nonzero, clear the denominators in
Euclidean remainders by even powers of those coefficients and invoke `exists_reconstruction`.  When
a leading coefficient is zero, truncate the corresponding polynomial.  Both cases decrease
`parametricDegreeProfile`, so `Multiset.wellFounded_isDershowitzMannaLT` supplies the induction.
-/
theorem signTable_preimage_definable (p : Fin s → IntPolynomialWithParameter n) (m : ℕ)
    (degree_le : ∀ i, xDegree (p i) ≤ m) (tables : Set (SignTable s m)) :
    ∃ formula : Formula n,
      ∀ (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
        (y : Fin n → R),
        rootSignTable (fun i ↦ specialize (p i) y) m
            (fun i ↦ (specialize_degree_le (p i) y).trans (degree_le i)) ∈ tables ↔
          formula.Realize y := by
  let symbolic := fun i ↦ MvPolynomial.finSuccEquiv ℤ n (p i)
  have symbolicDegree : ∀ i, (symbolic i).natDegree ≤ m := degree_le
  obtain ⟨formula, formula_spec⟩ :=
    symbolic_signTable_preimage_definable symbolic symbolicDegree tables
  refine ⟨formula, ?_⟩
  intro R _ _ _ _ y
  simpa only [specialize, symbolic] using formula_spec R y

/-! ## The uniform one-variable elimination theorem -/

/-- **Tarski--Seidenberg theorem**, in the form of Theorem 1.4.2 of Bochnak--Coste--Roy.

For a finite family of integer polynomials `pᵢ(X, Y)` and prescribed signs `requiredSign i`,
there is a Boolean combination of sign conditions involving only `Y` that is equivalent, in every
real closed field, to the existence of an `X` realizing all prescribed signs.
-/
theorem tarski_seidenberg (p : Fin s → IntPolynomialWithParameter n)
    (requiredSign : Fin s → SignType) :
    ∃ formula : Formula n,
      ∀ (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
        (y : Fin n → R),
        HasSolution p requiredSign y ↔ formula.Realize y := by
  let m := maxXDegree p
  have degree_le : ∀ i, xDegree (p i) ≤ m := xDegree_le_maxXDegree p
  obtain ⟨formula, formula_spec⟩ :=
    signTable_preimage_definable p m degree_le { table | table.Accepts requiredSign }
  refine ⟨formula, ?_⟩
  intro R _ _ _ _ y
  change (∃ x : R, ∀ i, SignType.sign ((specialize (p i) y).eval x) = requiredSign i) ↔ _
  rw [hasSolution_iff_accepts_rootSignTable (fun i ↦ specialize (p i) y) requiredSign m
    (fun i ↦ (specialize_degree_le (p i) y).trans (degree_le i))]
  simpa only [Set.mem_ofPred_eq] using formula_spec R y

end TarskiSeidenberg
