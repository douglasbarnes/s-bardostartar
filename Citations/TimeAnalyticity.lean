import Mathlib

/-!
# Time-analyticity citation statement

The paper cites `gevrey`, Theorem 1.1, for real analyticity of the Navier--Stokes
trajectory in time.  The later expansion about zero and coefficient-growth estimate are
consequences the paper draws from analyticity; they are deliberately not bundled into
the citation statement here.

The repository still does not contain the concrete 2D periodic Navier--Stokes solution
predicate, so the cited result remains a proposition-valued interface rather than an
axiom over an arbitrary adapter predicate.
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

/-- **Citation statement: `gevrey`, Theorem 1.1.**

Paper location: proof of Theorem `eve`, Proposition `an`.

For the concrete 2D periodic Navier--Stokes solution relation, a solution existing on
`t > -τ` is real analytic there.  The paper then specializes analyticity at `t=0` to
obtain a local power series and derives a geometric coefficient estimate by a
radius/ratio argument; those are project proof obligations, not part of this citation
interface.

`isNSESolutionOn` is an adapter parameter only.  This declaration does not assert the
proposition for arbitrary predicates; once the canonical NSE solution relation exists,
this proposition should be replaced by an individually named citation axiom specialized
to that relation. -/
def gevrey_theorem1_1_statement
    {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (isNSESolutionOn : Set ℝ → (ℝ → H) → Prop) : Prop :=
  ∀ u : ℝ → H, ∀ τ : ℝ, 0 < τ →
    isNSESolutionOn (Ioi (-τ)) u →
    RealAnalyticOnPaper u (Ioi (-τ))

end BardosTartar.Citations
