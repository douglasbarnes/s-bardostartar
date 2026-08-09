import Mathlib

/-!
# Generic asymptotic helpers

Reusable asymptotic lemmas for the Bardos--Tartar formalisation.  This file deliberately contains
no paper-specific dynamical statement.
-/

open Filter
open scoped Topology

namespace BardosTartar
namespace Asymptotics

/-- On `ℕ`, filter-eventual statements at `atTop` are exactly explicit threshold statements. -/
theorem eventually_atTop_iff_exists_nat {P : ℕ → Prop} :
    (∀ᶠ n in atTop, P n) ↔ ∃ N : ℕ, ∀ n, N ≤ n → P n := by
  simpa using (Filter.eventually_atTop : (∀ᶠ n : ℕ in atTop, P n) ↔ _)

/-- Package an explicit threshold as a filter-eventual statement. -/
theorem eventually_atTop_of_threshold {P : ℕ → Prop} (N : ℕ)
    (h : ∀ n, N ≤ n → P n) : ∀ᶠ n in atTop, P n :=
  eventually_atTop_iff_exists_nat.2 ⟨N, h⟩

/-- Extract an explicit natural-number threshold from an eventual statement. -/
theorem threshold_of_eventually_atTop {P : ℕ → Prop} (h : ∀ᶠ n in atTop, P n) :
    ∃ N : ℕ, ∀ n, N ≤ n → P n :=
  eventually_atTop_iff_exists_nat.1 h

/-- A positive base has a strictly positive real power, for every real exponent. -/
theorem rpow_pos {x a : ℝ} (hx : 0 < x) : 0 < x ^ a :=
  Real.rpow_pos_of_pos hx a

/-- A nonnegative base has a nonnegative real power. -/
theorem rpow_nonneg {x a : ℝ} (hx : 0 ≤ x) : 0 ≤ x ^ a :=
  Real.rpow_nonneg hx a

/-- Positive real powers tend to `+∞` at `+∞`. -/
theorem tendsto_rpow_atTop_of_pos {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ ↦ x ^ a) atTop atTop :=
  tendsto_rpow_atTop ha

/-- Negative real powers tend to zero at `+∞`. -/
theorem tendsto_rpow_neg_atTop_of_pos {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ ↦ x ^ (-a)) atTop (𝓝 0) :=
  tendsto_rpow_neg_atTop ha

/-- A logarithm is negligible compared with any positive real power. -/
theorem tendsto_log_div_rpow_atTop {a : ℝ} (ha : 0 < a) :
    Tendsto (fun x : ℝ ↦ Real.log x / x ^ a) atTop (𝓝 0) :=
  (isLittleO_log_rpow_atTop ha).tendsto_div_nhds_zero

/-- Sequence version of `tendsto_log_div_rpow_atTop`. -/
theorem tendsto_log_div_rpow_sequence {lam : ℕ → ℝ} {a : ℝ}
    (hlam : Tendsto lam atTop atTop) (ha : 0 < a) :
    Tendsto (fun n ↦ Real.log (lam n) / (lam n) ^ a) atTop (𝓝 0) :=
  (tendsto_log_div_rpow_atTop ha).comp hlam

/-- A product of two convergent real sequences converges to the product of their limits. -/
theorem tendsto_mul {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 b)) :
    Tendsto (fun n ↦ f n * g n) atTop (𝓝 (a * b)) := by
  simpa using hf.mul hg

/-- In particular, a convergent factor times a vanishing factor vanishes. -/
theorem tendsto_mul_zero_right {f g : ℕ → ℝ} {a : ℝ}
    (hf : Tendsto f atTop (𝓝 a)) (hg : Tendsto g atTop (𝓝 0)) :
    Tendsto (fun n ↦ f n * g n) atTop (𝓝 0) := by
  simpa using hf.mul hg

/-- Constant multiples preserve convergence to zero. -/
theorem tendsto_const_mul_zero {f : ℕ → ℝ} {c : ℝ}
    (hf : Tendsto f atTop (𝓝 0)) :
    Tendsto (fun n ↦ c * f n) atTop (𝓝 0) := by
  simpa using (tendsto_const_nhds.mul hf)

/-- If `λₙ → ∞` and `a>0`, then `λₙ⁻ᵃ → 0`. -/
theorem tendsto_inv_rpow_sequence {lam : ℕ → ℝ} {a : ℝ}
    (hlam : Tendsto lam atTop atTop) (ha : 0 < a) :
    Tendsto (fun n ↦ (lam n) ^ (-a)) atTop (𝓝 0) :=
  (tendsto_rpow_neg_atTop ha).comp hlam

end Asymptotics
end BardosTartar
