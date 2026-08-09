import Mathlib

/-!
# Dudley / Remez-type polynomial inequality
-/

namespace BardosTartar.Citations

open Set

/-- Supremum of the absolute value of a real polynomial on a set. -/
noncomputable def polynomialSupAbsOn (E : Set ℝ) (P : Polynomial ℝ) : ℝ :=
  sSup ((fun x : ℝ => |P.eval x|) '' E)

/-- **Citation: `dudley`, Lemma 1.**

Paper location: Appendix, `Miscellaneous results`, inside the proof of the polynomial
coefficient bound `bigpoly`.

For a closed positive-measure subset `E` of a compact interval, the uniform norm of a
real polynomial of degree at most `d` on the whole interval is controlled by `C^d`
times its uniform norm on `E`.  The constant depends on the interval and `E`, not on
`d` or the polynomial. -/
axiom dudley_lemma1
    (a b : ℝ) (E : Set ℝ)
    (hclosed : IsClosed E) (hsub : E ⊆ Icc a b)
    (hmeasure : 0 < MeasureTheory.volume E) :
    ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, ∀ P : Polynomial ℝ,
      P.natDegree ≤ d →
      polynomialSupAbsOn (Icc a b) P ≤ C ^ d * polynomialSupAbsOn E P

end BardosTartar.Citations
