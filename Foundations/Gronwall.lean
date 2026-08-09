import Mathlib

/-!
# Grönwall wrappers

Convenience wrappers around Mathlib's one-sided Grönwall inequality.  These are generic real
calculus statements and contain no Navier--Stokes-specific assumptions.
-/

open Set
open Real

namespace BardosTartar
namespace Gronwall

/-- Constant-coefficient exponential upper decay:
if `y' ≤ -κ y` on `[0,T)`, then `y(t) ≤ y(0) exp(-κt)`. -/
theorem le_initial_mul_exp_neg_of_hasDerivWithinAt
    {y y' : ℝ → ℝ} {κ T : ℝ}
    (hy : ContinuousOn y (Icc 0 T))
    (hy' : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (y' t) (Ici t) t)
    (hdy : ∀ t ∈ Ico 0 T, y' t ≤ -κ * y t) :
    ∀ t ∈ Icc 0 T, y t ≤ y 0 * exp (-κ * t) := by
  intro t ht
  have h := le_gronwallBound_of_liminf_deriv_right_le
    (δ := y 0) (K := -κ) (ε := 0) (a := 0) (b := T) hy
    (fun x hx _r hr ↦ (hy' x hx).liminf_right_slope_le hr)
    (le_refl (y 0)) (fun x hx ↦ by simpa [neg_mul] using hdy x hx) t ht
  rw [gronwallBound_ε0] at h
  simpa [sub_zero, neg_mul] using h

/-- Constant-coefficient exponential lower bound:
if `-κ y ≤ y'`, then `y(0) exp(-κt) ≤ y(t)`. -/
theorem initial_mul_exp_neg_le_of_hasDerivWithinAt
    {y y' : ℝ → ℝ} {κ T : ℝ}
    (hy : ContinuousOn y (Icc 0 T))
    (hy' : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (y' t) (Ici t) t)
    (hdy : ∀ t ∈ Ico 0 T, -κ * y t ≤ y' t) :
    ∀ t ∈ Icc 0 T, y 0 * exp (-κ * t) ≤ y t := by
  have hneg : ∀ t ∈ Ico 0 T, -y' t ≤ -κ * (-y t) := by
    intro t ht
    nlinarith [hdy t ht]
  have hupper := le_initial_mul_exp_neg_of_hasDerivWithinAt
    (y := fun t ↦ -y t) (y' := fun t ↦ -y' t) (κ := κ) (T := T)
    hy.neg (fun t ht ↦ (hy' t ht).neg) hneg
  intro t ht
  nlinarith [hupper t ht]

/-- Grönwall with an additive forcing term, in the exact bound supplied by Mathlib. -/
theorem le_gronwall_with_forcing
    {y y' : ℝ → ℝ} {δ K ε a b : ℝ}
    (hy : ContinuousOn y (Icc a b))
    (hy' : ∀ t ∈ Ico a b, HasDerivWithinAt y (y' t) (Ici t) t)
    (ha : y a ≤ δ)
    (hdy : ∀ t ∈ Ico a b, y' t ≤ K * y t + ε) :
    ∀ t ∈ Icc a b, y t ≤ gronwallBound δ K ε (t - a) :=
  le_gronwallBound_of_liminf_deriv_right_le hy
    (fun x hx _r hr ↦ (hy' x hx).liminf_right_slope_le hr) ha hdy

end Gronwall
end BardosTartar
