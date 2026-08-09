# API requests — Wave 1 Agent E

## `Citations/PolynomialInequality.lean`

Agent E needs the cited Dudley/Remez lemma in a form that can instantiate the generic `DudleyControl` interface from `Nonextendable/PolynomialBound.lean`.

Requested semantic statement (name can follow the citation agent's established namespace):

```lean
/-- Dudley, Lemma 1, as cited in the paper's proof of Lemma `bigpoly`. -/
theorem dudley_polynomial_sup_bound
    (a b : ℝ) (E : Set ℝ)
    (hEclosed : IsClosed E) (hEsub : E ⊆ Set.Icc a b)
    (hEmeasure : 0 < MeasureTheory.volume E) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (d : ℕ) (P : ℝ[X]), P.natDegree ≤ d →
        sSup (|P.eval ·| '' Set.Icc a b) ≤ K ^ d * sSup (|P.eval ·| '' E)
```

An equivalent bounded-on formulation is preferable if the citation file already uses it. Agent E deliberately does not introduce any local assumption declaration.
