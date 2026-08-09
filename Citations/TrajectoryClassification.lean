import Mathlib
import Citations.Interfaces

/-!
# CFKM backward-trajectory classification

This citation covers the mathematically substantive classification mentioned in the
introduction.  It is background only and is not needed by the paper's headline proofs.
-/

namespace BardosTartar.Citations

universe u

/-- `log f(t) = rate * t + o(|t|)` as `t → -∞`. -/
def HasLogRateAtBot (f : ℝ → ℝ) (rate : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, t < T →
    0 < f t ∧ |Real.log (f t) - rate * t| ≤ ε * |t|

/-- Growth faster than every exponential as `t → -∞`. -/
def GrowsSuperExponentiallyAtBot (f : ℝ → ℝ) : Prop :=
  ∀ c : ℝ, 0 < c → ∃ T : ℝ, ∀ t : ℝ, t < T →
    Real.exp (c * (-t)) ≤ f t

/-- **Citation: `cfkm` (classification theorem; no theorem number is supplied at this
paper use-site).**

Paper location: Introduction, main-results discussion immediately after Theorem
`BT for s>1`.

For a complete nontrivial trajectory of the 2D periodic NSE, either the trajectory is
on the global attractor, its `L²` norm has one of the Stokes exponential rates, or it
grows super-exponentially backward in time.  The paper says the same classification can
be proved for the hyperviscous system; that new adaptation is not included in this
citation axiom. -/
axiom cfkm_backwardTrajectory_classification
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) (ν : ℝ) (hν : 0 < ν)
    (attractor : Set H) (u : ℝ → H)
    (hcomplete : IsCompleteOrbit d u) (hnonzero : u 0 ≠ 0) :
    u 0 ∈ attractor ∨
      (∃ n : ℕ, 0 < n ∧
        HasLogRateAtBot (fun t : ℝ => d.energyNorm (u t)) (-ν * d.lambda n)) ∨
      GrowsSuperExponentiallyAtBot (fun t : ℝ => d.energyNorm (u t))

end BardosTartar.Citations
