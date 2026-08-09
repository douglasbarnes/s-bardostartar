import Mathlib

/-!
# Extremal-vector summation lemma

This file isolates the finite-dimensional geometry used near the end of the appendix of the
paper.  Nothing here depends on Navier--Stokes or Fourier analysis.
-/

namespace BardosTartar.Nonextendable

open scoped BigOperators
open Finset

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Two nonzero vectors are parallel when nonzero scalar multiples of them agree. -/
def Parallel (x y : E) : Prop :=
  ∃ a b : ℝ, a ≠ 0 ∧ b ≠ 0 ∧ a • x = b • y

namespace Parallel

/-- Symmetry of the parallel relation. -/
theorem symm {x y : E} (h : Parallel x y) : Parallel y x := by
  rcases h with ⟨a, b, ha, hb, hab⟩
  exact ⟨b, a, hb, ha, hab.symm⟩

/-- For nonzero vectors, parallelity is equivalent to being a nonzero scalar multiple. -/
theorem iff_eq_smul {x y : E} (hx : x ≠ 0) (hy : y ≠ 0) :
    Parallel x y ↔ ∃ c : ℝ, c ≠ 0 ∧ x = c • y := by
  constructor
  · rintro ⟨a, b, ha, hb, hab⟩
    refine ⟨b / a, div_ne_zero hb ha, ?_⟩
    calc
      x = a⁻¹ • (a • x) := by simp [smul_smul, ha]
      _ = a⁻¹ • (b • y) := by rw [hab]
      _ = (b / a) • y := by simp [smul_smul, div_eq_mul_inv, mul_comm]
  · rintro ⟨c, hc, hxy⟩
    exact ⟨1, c, one_ne_zero, hc, by simpa [hxy]⟩

/-- Transitivity of parallelity for nonzero vectors. -/
theorem trans {x y z : E} (hx : x ≠ 0) (hy : y ≠ 0) (hz : z ≠ 0)
    (hxy : Parallel x y) (hyz : Parallel y z) : Parallel x z := by
  rcases (iff_eq_smul hx hy).1 hxy with ⟨c, hc, hxy'⟩
  rcases (iff_eq_smul hy hz).1 hyz with ⟨d, hd, hyz'⟩
  refine (iff_eq_smul hx hz).2 ⟨c * d, mul_ne_zero hc hd, ?_⟩
  rw [hxy', hyz', smul_smul]

end Parallel

/--
The hypotheses saying that `(p,q)` is the pair selected in the paper: `q` has maximal norm
in `S`, `p` is shorter and nonparallel to `q`, and `p·q` is maximal among all pairs with the
same admissibility conditions.
-/
structure ExtremalPair (S : Set E) (p q : E) : Prop where
  p_mem : p ∈ S
  q_mem : q ∈ S
  nonzero_mem : ∀ ⦃x : E⦄, x ∈ S → x ≠ 0
  not_parallel : ¬ Parallel p q
  norm_lt : ‖p‖ < ‖q‖
  max_norm : ∀ ⦃x : E⦄, x ∈ S → ‖x‖ ≤ ‖q‖
  inner_max : ∀ ⦃a b : E⦄, a ∈ S → b ∈ S → ¬ Parallel a b →
    ‖a‖ < ‖b‖ → ‖b‖ = ‖q‖ → inner ℝ a b ≤ inner ℝ p q

private def deficit (q x : E) : ℝ :=
  ‖q‖ ^ 2 - inner ℝ x q

private theorem deficit_nonneg {q x : E} (hxq : ‖x‖ ≤ ‖q‖) :
    0 ≤ deficit q x := by
  have hinner : inner ℝ x q ≤ ‖x‖ * ‖q‖ := real_inner_le_norm x q
  have hmul : ‖x‖ * ‖q‖ ≤ ‖q‖ * ‖q‖ :=
    mul_le_mul_of_nonneg_right hxq (norm_nonneg q)
  dsimp [deficit]
  nlinarith

private theorem eq_of_deficit_eq_zero {q x : E} (hxq : ‖x‖ ≤ ‖q‖)
    (hzero : deficit q x = 0) : x = q := by
  have hinner : inner ℝ x q = ‖q‖ ^ 2 := by
    dsimp [deficit] at hzero
    linarith
  have hprod : 0 ≤ (‖q‖ - ‖x‖) * (‖q‖ + ‖x‖) :=
    mul_nonneg (sub_nonneg.mpr hxq) (add_nonneg (norm_nonneg q) (norm_nonneg x))
  have hsubsq : ‖x - q‖ ^ 2 ≤ 0 := by
    rw [norm_sub_sq_real, hinner]
    nlinarith
  have hsubsq0 : ‖x - q‖ ^ 2 = 0 := le_antisymm hsubsq (sq_nonneg _)
  have hnorm0 : ‖x - q‖ = 0 := by nlinarith [norm_nonneg (x - q)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)

private theorem sum_deficit_eq
    {n : ℕ} {p q : E} (v : Fin (n + 1) → E)
    (hsum : ∑ i, v i = p + (n : ℝ) • q) :
    ∑ i, deficit q (v i) = ‖q‖ ^ 2 - inner ℝ p q := by
  have hinner :
      (∑ i, inner ℝ (v i) q) = inner ℝ p q + (n : ℝ) * ‖q‖ ^ 2 := by
    have hs := congrArg (fun z : E => inner ℝ z q) hsum
    rw [sum_inner] at hs
    rw [inner_add_left, real_inner_smul_left, real_inner_self_eq_norm_sq] at hs
    simpa [pow_two] using hs
  rw [show (∑ i, deficit q (v i)) =
      (∑ _i : Fin (n + 1), ‖q‖ ^ 2) - ∑ i, inner ℝ (v i) q by
        simp [deficit, Finset.sum_sub_distrib]]
  rw [hinner]
  simp [Fintype.card_fin]
  ring

private theorem sum_erase_eq_smul_of_eq
    {n : ℕ} {q : E} (v : Fin (n + 1) → E) (i : Fin (n + 1))
    (h : ∀ j, j ≠ i → v j = q) :
    ∑ j ∈ Finset.univ.erase i, v j = (n : ℝ) • q := by
  calc
    ∑ j ∈ Finset.univ.erase i, v j = ∑ _j ∈ Finset.univ.erase i, q := by
      apply Finset.sum_congr rfl
      intro j hj
      exact h j (by simpa using hj)
    _ = (Finset.univ.erase i).card • q := by simp
    _ = n • q := by simp
    _ = (n : ℝ) • q := by
      exact (Nat.cast_smul_eq_nsmul ℝ n q).symm

/--
Inner-product-space form of the extremal summation argument.  The paper-facing Euclidean
specialisation is `extremal_vector_summation_euclidean` below.
-/
theorem extremal_vector_summation
    {S : Set E} {p q : E} (hpq : ExtremalPair S p q)
    {n : ℕ} (hn : 0 < n) (v : Fin (n + 1) → E)
    (hv : ∀ i, v i ∈ S)
    (hsum : ∑ i, v i = p + (n : ℝ) • q) :
    (∀ i, ‖v i‖ = ‖q‖) ∨
      ∃ i, v i = p ∧ ∀ j, j ≠ i → v j = q := by
  classical
  have hq0 : q ≠ 0 := hpq.nonzero_mem hpq.q_mem
  have hp0 : p ≠ 0 := hpq.nonzero_mem hpq.p_mem
  have hnorm : ∀ i, ‖v i‖ ≤ ‖q‖ := fun i => hpq.max_norm (hv i)
  have hδ : ∀ i, 0 ≤ deficit q (v i) := fun i => deficit_nonneg (hnorm i)
  have hδsum := sum_deficit_eq v hsum
  by_cases hall : ∀ i, ‖v i‖ = ‖q‖
  · exact Or.inl hall
  · right
    have hlowExists : ∃ i, ‖v i‖ < ‖q‖ := by
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      exact ⟨i, lt_of_le_of_ne (hnorm i) hi⟩
    by_cases hgood : ∃ i, ‖v i‖ < ‖q‖ ∧ ¬ Parallel (v i) q
    · obtain ⟨i, hi_lt, hi_np⟩ := hgood
      have hinner : inner ℝ (v i) q ≤ inner ℝ p q :=
        hpq.inner_max (hv i) hpq.q_mem hi_np hi_lt rfl
      have hδi_ge : ‖q‖ ^ 2 - inner ℝ p q ≤ deficit q (v i) := by
        dsimp [deficit]
        linarith
      have hδi_le : deficit q (v i) ≤ ∑ j, deficit q (v j) :=
        Finset.single_le_sum (fun j _ => hδ j) (Finset.mem_univ i)
      have hδi_eq : deficit q (v i) = ∑ j, deficit q (v j) := by
        apply le_antisymm hδi_le
        rw [hδsum]
        exact hδi_ge
      have herase0 : ∑ j ∈ Finset.univ.erase i, deficit q (v j) = 0 := by
        have hsplit := Finset.sum_erase_add (s := Finset.univ)
          (f := fun j => deficit q (v j)) (Finset.mem_univ i)
        linarith
      have hδzero : ∀ j, j ≠ i → deficit q (v j) = 0 := by
        intro j hji
        have hjmem : j ∈ Finset.univ.erase i := by simp [hji]
        have hallzero :=
          (Finset.sum_eq_zero_iff_of_nonneg (fun k hk => hδ k)).1 herase0
        exact hallzero j hjmem
      have hjq : ∀ j, j ≠ i → v j = q := by
        intro j hji
        exact eq_of_deficit_eq_zero (hnorm j) (hδzero j hji)
      have herase : ∑ j ∈ Finset.univ.erase i, v j = (n : ℝ) • q :=
        sum_erase_eq_smul_of_eq v i hjq
      have hvi : v i = p := by
        have hs := hsum
        rw [← Finset.sum_erase_add (s := Finset.univ) (f := v) (Finset.mem_univ i), herase] at hs
        have hs' : (n : ℝ) • q + v i = (n : ℝ) • q + p := by
          simpa [add_comm] using hs
        exact add_left_cancel hs'
      exact ⟨i, hvi, hjq⟩
    · push Not at hgood
      obtain ⟨i, hi_lt⟩ := hlowExists
      have hi_par : Parallel (v i) q := hgood i hi_lt
      have hvi0 : v i ≠ 0 := hpq.nonzero_mem (hv i)
      obtain ⟨c, hc0, hvi⟩ := (Parallel.iff_eq_smul hvi0 hq0).1 hi_par
      have hqnorm : 0 < ‖q‖ := norm_pos_iff.mpr hq0
      have hcabs : |c| < 1 := by
        rw [hvi, norm_smul, Real.norm_eq_abs] at hi_lt
        nlinarith [abs_nonneg c]
      have hc_lt : c < 1 := lt_of_le_of_lt (le_abs_self c) hcabs

      have hjExists : ∃ j, ¬ Parallel (v j) q := by
        by_contra hnone
        push Not at hnone
        have hrep : ∀ j, ∃ r : ℝ, r ≠ 0 ∧ v j = r • q := by
          intro j
          exact (Parallel.iff_eq_smul (hpq.nonzero_mem (hv j)) hq0).1 (hnone j)
        choose r hr0 hvr using hrep
        have hsum_smul : ∑ j, v j = (∑ j, r j) • q := by
          simp_rw [hvr]
          rw [Finset.sum_smul]
        have hp_eq : p = ((∑ j, r j) - n) • q := by
          have hs := hsum
          rw [hsum_smul] at hs
          calc
            p = (∑ j, r j) • q - (n : ℝ) • q := by rw [hs]; abel
            _ = ((∑ j, r j) - n) • q := by rw [sub_smul]
        have hcoef0 : (∑ j, r j) - (n : ℝ) ≠ 0 := by
          intro hz
          have : p = 0 := by simpa [hz] using hp_eq
          exact hp0 this
        exact hpq.not_parallel
          ((Parallel.iff_eq_smul hp0 hq0).2 ⟨(∑ j, r j) - n, hcoef0, hp_eq⟩)
      obtain ⟨j, hj_np⟩ := hjExists
      have hj_norm : ‖v j‖ = ‖q‖ := by
        apply le_antisymm (hnorm j)
        apply le_of_not_gt
        intro hj_lt
        exact hj_np (hgood j hj_lt)
      have hji : j ≠ i := by
        intro hji
        subst j
        exact hj_np hi_par
      have hδj_ne : deficit q (v j) ≠ 0 := by
        intro hzero
        have hvjq := eq_of_deficit_eq_zero (hnorm j) hzero
        apply hj_np
        exact (Parallel.iff_eq_smul (hpq.nonzero_mem (hv j)) hq0).2
          ⟨1, one_ne_zero, by simpa [hvjq]⟩
      have hδj_pos : 0 < deficit q (v j) :=
        lt_of_le_of_ne (hδ j) hδj_ne.symm
      have htwo_le : deficit q (v i) + deficit q (v j) ≤ ∑ k, deficit q (v k) := by
        have himem : i ∈ Finset.univ.erase j := by simp [hji.symm]
        have hi_le_erase : deficit q (v i) ≤
            ∑ k ∈ Finset.univ.erase j, deficit q (v k) :=
          Finset.single_le_sum (fun k _ => hδ k) himem
        have hsplit := Finset.sum_erase_add (s := Finset.univ)
          (f := fun k => deficit q (v k)) (Finset.mem_univ j)
        linarith
      have hprodpos : 0 < (1 - c) * deficit q (v j) :=
        mul_pos (sub_pos.mpr hc_lt) hδj_pos
      have hdiff :
          (deficit q (v i) + deficit q (v j)) -
              (‖q‖ ^ 2 - inner ℝ (v j) (v i)) =
            (1 - c) * deficit q (v j) := by
        rw [hvi]
        simp only [deficit, real_inner_smul_left, real_inner_smul_right,
          real_inner_self_eq_norm_sq]
        ring
      have hstrict :
          ‖q‖ ^ 2 - inner ℝ (v j) (v i) < deficit q (v i) + deficit q (v j) := by
        linarith [hprodpos, hdiff]
      have htwo_le' :
          deficit q (v i) + deficit q (v j) ≤ ‖q‖ ^ 2 - inner ℝ p q := by
        calc
          deficit q (v i) + deficit q (v j) ≤ ∑ k, deficit q (v k) := htwo_le
          _ = ‖q‖ ^ 2 - inner ℝ p q := hδsum
      have hinner_gt' : inner ℝ p q < inner ℝ (v j) (v i) := by
        linarith [lt_of_lt_of_le hstrict htwo_le']
      have hinner_gt : inner ℝ p q < inner ℝ (v i) (v j) := by
        simpa [real_inner_comm] using hinner_gt'
      have hi_j_np : ¬ Parallel (v i) (v j) := by
        intro hijpar
        have hvj0 := hpq.nonzero_mem (hv j)
        have hvjqpar := Parallel.trans hvj0 hvi0 hq0 hijpar.symm hi_par
        exact hj_np hvjqpar
      have hmax := hpq.inner_max (hv i) (hv j) hi_j_np (by simpa [hj_norm] using hi_lt) hj_norm
      linarith


/--
Paper Lemma `stupid` (Appendix, “Miscellaneous results”).

Let `S ⊂ ℝ^d \ {0}` and let `p,q ∈ S` be selected as in the paper. If `n > 0` and `n+1`
vectors of `S` sum to `p+nq`, then either every summand has maximal norm `‖q‖`, or the
summands are one copy of `p` and `n` copies of `q`, in some order.
-/
theorem extremal_vector_summation_euclidean
    {d : ℕ} {S : Set (EuclideanSpace ℝ (Fin d))}
    {p q : EuclideanSpace ℝ (Fin d)} (hpq : ExtremalPair S p q)
    {n : ℕ} (hn : 0 < n) (v : Fin (n + 1) → EuclideanSpace ℝ (Fin d))
    (hv : ∀ i, v i ∈ S)
    (hsum : ∑ i, v i = p + (n : ℝ) • q) :
    (∀ i, ‖v i‖ = ‖q‖) ∨
      ∃ i, v i = p ∧ ∀ j, j ≠ i → v j = q :=
  extremal_vector_summation hpq hn v hv hsum

end BardosTartar.Nonextendable
