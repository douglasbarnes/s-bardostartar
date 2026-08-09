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

/-- Paper-facing spelling of Dudley Lemma 1 requested by the polynomial-bound layer.
This is only a theorem alias/unfolding of `dudley_lemma1`; it introduces no additional
assumption. -/
theorem dudley_polynomial_sup_bound
    (a b : ℝ) (E : Set ℝ)
    (hclosed : IsClosed E) (hsub : E ⊆ Icc a b)
    (hmeasure : 0 < MeasureTheory.volume E) :
    ∃ K : ℝ, 0 < K ∧ ∀ d : ℕ, ∀ P : Polynomial ℝ,
      P.natDegree ≤ d →
      sSup ((fun x : ℝ => |P.eval x|) '' Icc a b) ≤
        K ^ d * sSup ((fun x : ℝ => |P.eval x|) '' E) := by
  simpa [polynomialSupAbsOn] using dudley_lemma1 a b E hclosed hsub hmeasure

end BardosTartar.Citations
