import Mathlib.NumberTheory.SumTwoSquares

/-!
# Erdős spectral-gap input

The periodic Stokes spectrum is reduced by the foundation layer to the increasing list
of positive natural numbers representable as a sum of two squares.  Mathlib already
uses the witness form `n = a^2 + b^2` throughout `Mathlib.NumberTheory.SumTwoSquares`,
so the local predicate below merely packages that existing convention for the cited
gap statement; it does not create a competing number-theory representation.
-/

namespace BardosTartar.Citations

/-- A natural number represented as a sum of two natural squares, packaged in the form
used by Mathlib's `Nat.eq_sq_add_sq_iff` family. -/
def IsSumOfTwoSquares (n : ℕ) : Prop :=
  ∃ a b : ℕ, n = a ^ 2 + b ^ 2

/-- `b` is the next sum-of-two-squares value strictly after `a`. -/
def IsConsecutiveSumTwoSquares (a b : ℕ) : Prop :=
  a < b ∧ IsSumOfTwoSquares a ∧ IsSumOfTwoSquares b ∧
    ∀ n : ℕ, a < n → n < b → ¬ IsSumOfTwoSquares n

/-- **Citation: `Erdos` (the paper supplies no theorem number).**

Paper location: Appendix, section `Notation`, in the sentence asserting
`limsup (λ_{n+1}-λ_n)=∞`.

Exact non-elementary strength required by the paper: gaps between consecutive positive
integers representable as sums of two squares are unbounded.  Agent B should derive the
stated Stokes-eigenvalue `limsup` after identifying the concrete spectral enumeration
with these values. -/
axiom erdos_unbounded_sum_two_squares_gaps :
    ∀ M : ℕ, ∃ a b : ℕ,
      IsConsecutiveSumTwoSquares a b ∧ M < b - a

end BardosTartar.Citations
