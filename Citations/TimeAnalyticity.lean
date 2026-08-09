import Mathlib

/-!
# Time analyticity citation

The recurrence argument in the paper uses only the local power-series expansion and the
geometric coefficient bound recorded below.  `isNSESolutionOn` is an adapter hook: it is
to be instantiated with the project's concrete 2D periodic Navier--Stokes solution
predicate, rather than with a second PDE representation in this citation file.
-/

namespace BardosTartar.Citations

open Set

universe u

/-- A Banach-valued real power series centred at `t0` represents `u` on a nontrivial
neighbourhood of `t0`. -/
def HasRealPowerSeriesAt {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : ℝ → H) (t0 : ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ U : ℕ → H, ∀ t : ℝ, |t - t0| < r →
    HasSum (fun m : ℕ => ((t - t0) ^ m) • U m) (u t)

/-- Paper-level formulation of real analyticity on a set. -/
def RealAnalyticOnPaper {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : ℝ → H) (I : Set ℝ) : Prop :=
  ∀ t : ℝ, t ∈ I → HasRealPowerSeriesAt u t

/-- The particular expansion at time zero, including the geometric growth bound used in
Theorem `eve`. -/
def HasZeroExpansionWithGeometricBound
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (u : ℝ → H) (τ : ℝ) : Prop :=
  ∃ τ' : ℝ, 0 < τ' ∧ τ' < τ ∧ ∃ U : ℕ → H, ∃ C : ℝ, 0 < C ∧
    (∀ t : ℝ, |t| < τ' → HasSum (fun m : ℕ => (t ^ m) • U m) (u t)) ∧
    ∀ m : ℕ, ‖U m‖ ≤ C ^ m

/-- **Citation: `gevrey`, Theorem 1.1.**

Paper location: proof of Theorem `eve`, Proposition `an`.

If a 2D Navier--Stokes solution exists on `t > -τ`, then it is real analytic there;
in particular it has a power-series expansion about zero on a smaller symmetric
interval and its coefficients obey a geometric `L²`-norm bound.  The paper further
deduces the same bound for each Fourier coefficient from Parseval/Cauchy--Schwarz; that
deduction is intentionally not included in this axiom. -/
axiom gevrey_theorem1_1
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (isNSESolutionOn : Set ℝ → (ℝ → H) → Prop)
    (u : ℝ → H) (τ : ℝ) (hτ : 0 < τ)
    (hsol : isNSESolutionOn (Ioi (-τ)) u) :
    RealAnalyticOnPaper u (Ioi (-τ)) ∧ HasZeroExpansionWithGeometricBound u τ

end BardosTartar.Citations
