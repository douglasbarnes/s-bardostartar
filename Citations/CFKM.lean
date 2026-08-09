import Mathlib
import BardosTartar.Citations.Interfaces

/-!
# Constantin--Foias--Kukavica--Majda weak-density input

This file contains only the result imported from external literature.  The paper later
specialises/adapts this input to its hyperviscous semigroup; those adaptations are not
axioms here.
-/

namespace BardosTartar.Citations

open Set

universe u

/-- Paper Condition `weakBTcon`, stated in the representation-neutral citation vocabulary.
The `enstrophyNorm` field is the norm defining the paper's `V` topology. -/
structure WeakBTConditions {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) : Prop where
  semigroup : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
    d.S (s + t) = fun u => d.S s (d.S t u)
  zero_time : d.S 0 = id

  c1_l2V_mem : ∀ u0 : H, ∀ T : ℝ, 0 < T →
    ∀ᵐ t ∂(MeasureTheory.volume.restrict (Ioo 0 T)), d.S t u0 ∈ d.V
  c1_l2V_integrable : ∀ u0 : H, ∀ T : ℝ, 0 < T →
    MeasureTheory.IntegrableOn
      (fun t : ℝ => d.enstrophyNorm (d.S t u0) ^ 2) (Ioo 0 T)
  c1_trajectory_continuous : ∀ u0 : H, ∀ T : ℝ, 0 < T →
    ContinuousOn (fun t : ℝ => d.S t u0) (Ioo 0 T)
  c1_trajectory_continuous_at_zero : ∀ u0 : H, u0 ∈ d.V → ∀ T : ℝ, 0 < T →
    ContinuousOn (fun t : ℝ => d.S t u0) (Icc 0 T)
  c1_time_map_continuous_H : ∀ T : ℝ, 0 < T → Continuous (d.S T)
  c1_maps_V : ∀ T : ℝ, 0 < T → Set.MapsTo (d.S T) d.V d.V
  c1_time_map_continuous_V : ∀ T : ℝ, 0 < T → ∀ u : H, u ∈ d.V →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v : H, v ∈ d.V →
      d.enstrophyNorm (v - u) < δ →
      d.enstrophyNorm (d.S T v - d.S T u) < ε

  c2_backwards_unique : ∀ T : ℝ, 0 < T → Function.Injective (d.S T)

  thresholds_positive : 0 < d.E1 ∧ 0 < d.E2 ∧ 0 < d.E3 ∧ 0 < d.E4
  c3_strong_dissipation : ∃ ζ : ℝ, 0 < ζ ∧
    (∀ u0 : H, u0 ∈ d.V → ∀ t : ℝ, 0 ≤ t →
      d.energyNorm (d.S t u0) ^ 2 > d.E1 →
      deriv (fun r : ℝ => d.energyNorm (d.S r u0) ^ 2) t < -ζ) ∧
    (∀ u0 : H, u0 ∈ d.V → ∀ t : ℝ, 0 ≤ t →
      d.energyNorm (d.S t u0) ^ 2 > d.lambda 1 * d.E2 →
      deriv (fun r : ℝ => d.enstrophyNorm (d.S r u0) ^ 2) t < -(d.lambda 1 * ζ))

  c4_dirichlet_barrier : ∀ n : ℕ, ∀ u0 : H, u0 ∈ d.V → ∀ T : ℝ, 0 ≤ T →
    dirichletQuotient d u0 ≤ midLambda d n →
    (∀ t : ℝ, t ∈ Icc 0 T → d.energyNorm (d.S t u0) ^ 2 > d.E3) →
    ∀ t : ℝ, t ∈ Icc 0 T → dirichletQuotient d (d.S t u0) ≤ midLambda d n

  c5_bounded_energy_dissipation : ∃ g : ℕ → ℝ → ℝ,
    (∀ n : ℕ, ∀ t : ℝ, 0 ≤ t → 0 < g n t ∧ g n t ≤ 1) ∧
    (∀ n : ℕ, ∀ s t : ℝ, 0 ≤ s → s ≤ t → g n t ≤ g n s) ∧
    ∀ n : ℕ, ∀ u0 : H, u0 ∈ d.V → ∀ T : ℝ, 0 ≤ T →
      dirichletQuotient d u0 ≤ midLambda d n →
      (∀ t : ℝ, t ∈ Icc 0 T → d.energyNorm (d.S t u0) ^ 2 > d.E4) →
      ∀ t : ℝ, t ∈ Icc 0 T →
        d.energyNorm (d.S t u0) ≥ d.energyNorm u0 * g n t

/-- **Citation: `cfkm`, Lemma 3.9 / Theorem 3.1.**

Paper location: Appendix, section `Regularity of the Hyperviscous NSE`, theorem
`weak density proposition` (and the introduction's weak-density discussion).

This is the paper-facing interface to the CFKM weak-density construction: prescribed
low modes admit a complete trajectory, with the stated backward Dirichlet-quotient
alternative and quantitative high-mode bound.  No proof of the CFKM construction is
reproduced here. -/
axiom cfkm_lemma3_9_theorem3_1
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) (hweak : WeakBTConditions d)
    (n : ℕ) (hn : 0 < n) (v : H) (hv : d.P n v = v) :
    ∃ u : ℝ → H,
      IsCompleteOrbit d u ∧
      d.P n (u 0) = v ∧
      (LimsupAtBotLE (fun t : ℝ => dirichletQuotient d (u t)) (midLambda d n) ∨
        (∀ t : ℝ, d.energyNorm (u t) ^ 2 ≤ d.E1)) ∧
      d.energyNorm (d.Q n (u 0)) ^ 2 ≤ paperTailBound d n v

end BardosTartar.Citations
