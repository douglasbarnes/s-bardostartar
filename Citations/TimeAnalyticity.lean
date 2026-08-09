import Mathlib

/-!
# Time-analyticity citation statement

The recurrence argument in the paper uses the local power-series expansion and geometric
coefficient bound recorded below.  The repository did not yet contain the concrete 2D
periodic Navier--Stokes solution predicate when Wave 1 Agent C began, so the exact cited
result is recorded as a proposition-valued interface rather than asserted for an
arbitrary predicate.
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

/-- **Citation statement: `gevrey`, Theorem 1.1.**

Paper location: proof of Theorem `eve`, Proposition `an`.

For the concrete 2D periodic Navier--Stokes solution relation, a solution existing on
`t > -τ` is real analytic there; in particular it has a power-series expansion about
zero on a smaller symmetric interval and its coefficients obey a geometric `L²`-norm
bound.  The paper further derives the corresponding Fourier-coefficient bound from the
Hilbert/Fourier structure; that deduction is intentionally not part of this cited
statement.

`isNSESolutionOn` is an adapter parameter only.  This declaration does not assert the
proposition for arbitrary predicates; after the foundation API supplies the concrete NSE
solution predicate, Agent I/integration can specialize this proposition and add the
citation axiom without strengthening the source. -/
def gevrey_theorem1_1_statement
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (isNSESolutionOn : Set ℝ → (ℝ → H) → Prop) : Prop :=
  ∀ u : ℝ → H, ∀ τ : ℝ, 0 < τ →
    isNSESolutionOn (Ioi (-τ)) u →
    RealAnalyticOnPaper u (Ioi (-τ)) ∧ HasZeroExpansionWithGeometricBound u τ

end BardosTartar.Citations
