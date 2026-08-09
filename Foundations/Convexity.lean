import Mathlib

/-!
# Convexity helpers for real powers

Small wrappers exposing exactly the convexity/concavity facts repeatedly needed in the later
Dirichlet-quotient argument.
-/

open Set

namespace BardosTartar
namespace Convexity

/-- `x ↦ x^p` is convex on the nonnegative reals for `p ≥ 1`. -/
theorem rpow_convexOn {p : ℝ} (hp : 1 ≤ p) :
    ConvexOn ℝ (Ici 0) (fun x : ℝ ↦ x ^ p) :=
  convexOn_rpow hp

/-- `x ↦ x^p` is concave on the nonnegative reals for `0 ≤ p ≤ 1`. -/
theorem rpow_concaveOn {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ (Ici 0) (fun x : ℝ ↦ x ^ p) :=
  Real.concaveOn_rpow hp0 hp1

/-- Bernoulli's inequality for real exponents at least one. -/
theorem one_add_mul_le_rpow_one_add {x p : ℝ} (hx : -1 ≤ x) (hp : 1 ≤ p) :
    1 + p * x ≤ (1 + x) ^ p :=
  one_add_mul_self_le_rpow_one_add hx hp

/-- Concave Bernoulli inequality for exponents in `[0,1]`. -/
theorem rpow_one_add_le_one_add_mul {x p : ℝ}
    (hx : -1 ≤ x) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (1 + x) ^ p ≤ 1 + p * x :=
  rpow_one_add_le_one_add_mul_self hx hp0 hp1

/-- The secant gap at the midpoint is nonnegative for a convex real power. -/
theorem midpoint_rpow_le_average {a b p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 1 ≤ p) :
    ((a + b) / 2) ^ p ≤ (a ^ p + b ^ p) / 2 := by
  have h := (convexOn_rpow hp).2 ha hb (show 0 ≤ (1 / 2 : ℝ) by norm_num)
    (show 0 ≤ (1 / 2 : ℝ) by norm_num) (by norm_num : (1 / 2 : ℝ) + 1 / 2 = 1)
  rw [show (a + b) / 2 =
      (2 : ℝ)⁻¹ * a + (2 : ℝ)⁻¹ * b by ring]
  rw [show (a ^ p + b ^ p) / 2 =
      (2 : ℝ)⁻¹ * a ^ p + (2 : ℝ)⁻¹ * b ^ p by ring]
  simpa only [smul_eq_mul, one_div] using h

end Convexity
end BardosTartar
