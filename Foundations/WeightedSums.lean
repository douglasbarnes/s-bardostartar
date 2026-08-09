import Mathlib

/-!
# Weighted-sum covariance helpers

The Dirichlet-quotient argument later uses the covariance identity obtained by introducing two
independent copies of a finitely supported spectral random variable.  The result below is the
underlying finite weighted-sum identity, with no probability machinery.
-/

open scoped BigOperators

namespace BardosTartar
namespace WeightedSums

variable {ι : Type*}

/-- Weighted expectation of a scalar function over a finite support. -/
def mean (s : Finset ι) (w f : ι → ℝ) : ℝ :=
  ∑ i ∈ s, w i * f i

/-- Weighted expectation over two independent copies of the same finite distribution. -/
def pairMean (s : Finset ι) (w : ι → ℝ) (F : ι → ι → ℝ) : ℝ :=
  ∑ i ∈ s, ∑ j ∈ s, w i * w j * F i j

/-- Expansion of the two-copy covariance kernel before normalization of the weights. -/
theorem pairMean_sub_mul_sub (s : Finset ι) (w f g : ι → ℝ) :
    pairMean s w (fun i j ↦ (f i - f j) * (g i - g j)) =
      2 * (∑ i ∈ s, w i) * mean s w (fun i ↦ f i * g i) -
      2 * mean s w f * mean s w g := by
  classical
  simp only [pairMean, mean]
  have hterm (i j : ι) :
      w i * w j * ((f i - f j) * (g i - g j)) =
        (w i * (f i * g i)) * w j -
        (w i * f i) * (w j * g j) -
        (w i * g i) * (w j * f j) +
        w i * (w j * (f j * g j)) := by
    ring
  simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
  ring

/-- Covariance identity with two iid copies for normalized finite weights. -/
theorem covariance_eq_half_pairMean (s : Finset ι) (w f g : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    mean s w (fun i ↦ f i * g i) - mean s w f * mean s w g =
      (1 / 2 : ℝ) * pairMean s w (fun i j ↦ (f i - f j) * (g i - g j)) := by
  rw [pairMean_sub_mul_sub, hw]
  ring

/-- Symmetric variance identity, obtained by taking the same observable twice. -/
theorem variance_eq_half_pairMean_sq (s : Finset ι) (w f : ι → ℝ)
    (hw : ∑ i ∈ s, w i = 1) :
    mean s w (fun i ↦ f i ^ 2) - (mean s w f) ^ 2 =
      (1 / 2 : ℝ) * pairMean s w (fun i j ↦ (f i - f j) ^ 2) := by
  simpa [pow_two] using covariance_eq_half_pairMean s w f f hw

end WeightedSums
end BardosTartar
