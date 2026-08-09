import Mathlib

/-!
# Finite-sum and interpolation helpers

Elementary finite-dimensional inequalities used by later convolution estimates.
-/

open scoped BigOperators

namespace BardosTartar
namespace FiniteSums

variable {ι : Type*}

/-- An `L¹` sum is bounded by cardinality times a uniform pointwise bound. -/
theorem sum_abs_le_card_mul_of_bound (s : Finset ι) (f : ι → ℝ) (M : ℝ)
    (hM : ∀ i ∈ s, |f i| ≤ M) :
    ∑ i ∈ s, |f i| ≤ (s.card : ℝ) * M := by
  calc
    ∑ i ∈ s, |f i| ≤ ∑ _i ∈ s, M := Finset.sum_le_sum hM
    _ = (s.card : ℝ) * M := by simp

/-- The elementary finite `L²² ≤ L∞ L¹` interpolation inequality. -/
theorem sum_sq_abs_le_bound_mul_sum_abs (s : Finset ι) (f : ι → ℝ) (M : ℝ)
    (hM : ∀ i ∈ s, |f i| ≤ M) :
    ∑ i ∈ s, |f i| ^ 2 ≤ M * ∑ i ∈ s, |f i| := by
  calc
    ∑ i ∈ s, |f i| ^ 2 ≤ ∑ i ∈ s, M * |f i| := by
      apply Finset.sum_le_sum
      intro i hi
      have h0 : 0 ≤ |f i| := abs_nonneg _
      have h := mul_le_mul_of_nonneg_right (hM i hi) h0
      simpa [pow_two] using h
    _ = M * ∑ i ∈ s, |f i| := by rw [Finset.mul_sum]

/-- Combining `L¹ ≤ #s L∞` and `L²² ≤ L∞ L¹`. -/
theorem sum_sq_abs_le_card_mul_bound_sq (s : Finset ι) (f : ι → ℝ) (M : ℝ)
    (hM0 : 0 ≤ M) (hM : ∀ i ∈ s, |f i| ≤ M) :
    ∑ i ∈ s, |f i| ^ 2 ≤ (s.card : ℝ) * M ^ 2 := by
  calc
    ∑ i ∈ s, |f i| ^ 2 ≤ M * ∑ i ∈ s, |f i| :=
      sum_sq_abs_le_bound_mul_sum_abs s f M hM
    _ ≤ M * ((s.card : ℝ) * M) :=
      mul_le_mul_of_nonneg_left (sum_abs_le_card_mul_of_bound s f M hM) hM0
    _ = (s.card : ℝ) * M ^ 2 := by ring

/-- Two-dimensional Cauchy--Schwarz, useful for reducing small finite recombinations. -/
theorem cauchy_schwarz_two (a b c d : ℝ) :
    (a * c + b * d) ^ 2 ≤ (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) := by
  nlinarith [sq_nonneg (a * d - b * c)]

/-- Young's quadratic inequality in the form used to split products. -/
theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- A weighted Jensen consequence for the convex real power `x ↦ x^p`, `p ≥ 1`. -/
theorem weighted_rpow_jensen (s : Finset ι) (w x : ι → ℝ) {p : ℝ}
    (hp : 1 ≤ p) (hw : ∀ i ∈ s, 0 ≤ w i)
    (hw1 : ∑ i ∈ s, w i = 1) (hx : ∀ i ∈ s, 0 ≤ x i) :
    (∑ i ∈ s, w i * x i) ^ p ≤ ∑ i ∈ s, w i * (x i) ^ p := by
  simpa [smul_eq_mul] using
    (convexOn_rpow hp).map_sum_le hw hw1 (fun i hi ↦ hx i hi)

/-- A direct wrapper around Mathlib's weighted Hölder inequality for nonnegative finite data. -/
theorem weighted_holder (s : Finset ι) {p : ℝ} (hp : 1 ≤ p)
    (w f : ι → NNReal) :
    ∑ i ∈ s, w i * f i ≤
      (∑ i ∈ s, w i) ^ (1 - p⁻¹) * (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ :=
  NNReal.inner_le_weight_mul_Lp s hp w f

/-- Weighted Hölder with normalized weights. -/
theorem weighted_holder_of_sum_eq_one (s : Finset ι) {p : ℝ} (hp : 1 ≤ p)
    (w f : ι → NNReal) (hw1 : ∑ i ∈ s, w i = 1) :
    ∑ i ∈ s, w i * f i ≤ (∑ i ∈ s, w i * f i ^ p) ^ p⁻¹ := by
  simpa [hw1] using weighted_holder s hp w f

end FiniteSums
end BardosTartar
