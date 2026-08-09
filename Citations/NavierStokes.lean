import Mathlib
import Citations.Interfaces

/-!
# Classical 2D periodic Navier--Stokes citation statements

The uploaded paper imports three classical ingredients as parts C1--C3 of Condition
`weakBTcon`.  At the start of Wave 1 the repository did not yet contain the concrete
periodic Navier--Stokes phase space or solution operator.  Consequently this file records
those three citation statements exactly as typed interfaces, but does not assert them as
axioms over an arbitrary `DynamicsData`: doing so would be stronger than the literature
and could be instantiated with non-Navier--Stokes dynamics.

Once the foundation/dynamics API exposes the concrete 2D periodic NSE semigroup, these
statement interfaces are the signatures to specialize into citation axioms in this file.
-/

namespace BardosTartar.Citations

open Set

universe u

/-- Condition C1 from the paper, with `enstrophyNorm` used as the norm defining `V`.
Existence is represented by the total forward solution operator `S`; the remaining
clauses record the trajectory and time-map regularity stated in C1. -/
def WellPosednessC1 {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) : Prop :=
  (∀ u0 : H, ∀ T : ℝ, 0 < T →
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Ioo 0 T)), d.S t u0 ∈ d.V) ∧
    MeasureTheory.IntegrableOn
      (fun t : ℝ => d.enstrophyNorm (d.S t u0) ^ 2) (Ioo 0 T) ∧
    ContinuousOn (fun t : ℝ => d.S t u0) (Ioo 0 T)) ∧
  (∀ u0 : H, u0 ∈ d.V → ∀ T : ℝ, 0 < T →
    ContinuousOn (fun t : ℝ => d.S t u0) (Icc 0 T)) ∧
  (∀ T : ℝ, 0 < T → Continuous (d.S T)) ∧
  (∀ T : ℝ, 0 < T → Set.MapsTo (d.S T) d.V d.V) ∧
  (∀ T : ℝ, 0 < T → ∀ u : H, u ∈ d.V →
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ v : H, v ∈ d.V →
      d.enstrophyNorm (v - u) < δ →
      d.enstrophyNorm (d.S T v - d.S T u) < ε)

/-- Condition C2 from the paper. -/
def BackwardsUniquenessC2 {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) : Prop :=
  ∀ T : ℝ, 0 < T → Function.Injective (d.S T)

/-- Condition C3 from the paper. -/
def StrongDissipationC3 {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) : Prop :=
  ∃ ζ : ℝ, 0 < ζ ∧
    (∀ u0 : H, u0 ∈ d.V → ∀ t : ℝ, 0 ≤ t →
      d.energyNorm (d.S t u0) ^ 2 > d.E1 →
      deriv (fun r : ℝ => d.energyNorm (d.S r u0) ^ 2) t < -ζ) ∧
    (∀ u0 : H, u0 ∈ d.V → ∀ t : ℝ, 0 ≤ t →
      d.energyNorm (d.S t u0) ^ 2 > d.lambda 1 * d.E2 →
      deriv (fun r : ℝ => d.enstrophyNorm (d.S r u0) ^ 2) t < -(d.lambda 1 * ζ))

/-- **Citation statement: `ConstantinFoias`, `Temam`, `TemamBook` (no theorem number
supplied by the paper).**

Paper locations: Introduction (well-posedness on the 2D torus) and Appendix,
`Regularity of the Hyperviscous NSE`, Condition C1 / proof of Proposition
`Property DNB for s-viscous`.

This declaration records the proposition to be asserted after `d` is identified with the
repository's concrete 2D periodic NSE dynamics. -/
def constantinFoias_temam_periodic2D_wellPosedness_statement
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) : Prop :=
  WellPosednessC1 d

/-- **Citation statement: `BardosTartar` (with `ConstantinFoias` also cited at the paper
use-site; no theorem number supplied).**

Paper location: Appendix, `Regularity of the Hyperviscous NSE`, Condition C2 and the
opening sentence of the proof of Proposition `Property DNB for s-viscous`.

This declaration records backward uniqueness for the concrete 2D periodic NSE dynamics;
it is not asserted for arbitrary dynamics. -/
def bardosTartar_periodic2D_backwardsUniqueness_statement
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) : Prop :=
  BackwardsUniquenessC2 d

/-- **Citation statement: `ConstantinFoias`, `BardosTartar` (no theorem number supplied).**

Paper location: Appendix, `Regularity of the Hyperviscous NSE`, Condition C3 and the
opening sentence of the proof of Proposition `Property DNB for s-viscous`.

The strong energy/enstrophy dissipation thresholds are kept separate from well-posedness
and backward uniqueness because the paper lists them as distinct hypotheses. -/
def constantinFoias_bardosTartar_periodic2D_strongDissipation_statement
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) : Prop :=
  StrongDissipationC3 d

end BardosTartar.Citations
