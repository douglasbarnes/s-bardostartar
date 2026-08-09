import Mathlib

/-!
# Erdős spectral-gap input

The periodic Stokes spectrum is reduced by the foundation layer to the increasing list
of positive integers representable as a sum of two squares.  This citation records only
the number-theoretic input that those gaps are unbounded.
-/

namespace BardosTartar.Citations

/-- An integer spectral value for the square two-torus: a natural number represented as
a sum of two integer squares. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℤ, a * a + b * b = (n : ℤ)

/-- `b` is the next sum-of-two-squares value strictly after `a`. -/
def IsConsecutiveSumTwoSquares (a b : ℕ) : Prop :=
  a < b ∧ IsSumOfTwoSquares a ∧ IsSumOfTwoSquares b ∧
    ∀ n : ℕ, a < n → n < b → ¬ IsSumOfTwoSquares n

/-- **Citation: `Erdos` (the paper supplies no theorem number).**

Paper location: Appendix, section `Notation`, in the sentence asserting
`limsup (λ_{n+1}-λ_n)=∞`.

Exact strength required by the paper: gaps between consecutive positive integers
representable as sums of two squares are unbounded.  Agent B should derive the stated
Stokes-eigenvalue `limsup` after identifying the concrete spectral enumeration with
these values. -/
axiom erdos_unbounded_sum_two_squares_gaps :
    ∀ M : ℕ, ∃ a b : ℕ,
      IsConsecutiveSumTwoSquares a b ∧ M < b - a

end BardosTartar.Citations
