# Formalization issues — Wave 1 Agent C

## C-1 — canonical PDE bridge still missing

- **Paper location:** project-wide, not a paper statement.
- **Difficulty:** the repository was empty when Agent C began.  Wave 1 has since supplied and externally checked the citation files, and `Foundations/Spectrum.lean` / `Foundations/Projections.lean` now provide the canonical spectral enumeration and coefficient-level low/high masks.  However, the repository still has no canonical real mean-zero divergence-free `L²` phase space `H`, `H¹`/enstrophy space `V`, Fourier equivalence from that phase space to the coefficient representation, function-space `P_n/Q_n`, or concrete 2D NSE solution relation/semigroup.  Without those objects, a PDE citation axiom would still have to quantify over arbitrary adapter data and would be stronger than the source.
- **Lean statement attempted:** PDE-specific external assertions remain proposition-valued interfaces in `Citations/`; the active axioms are restricted to model-independent cited results.
- **Smallest correction/clarification:** complete the phase-space/Fourier bridge and dynamics API requested in `API_REQUESTS/agent-c.md`, then replace the relevant `..._statement` declarations by individually named citation axioms specialized to those canonical objects.  Do not introduce a second phase-space or spectral model.

## C-2 — missing `references.bib`

- **Paper location:** all `\cite{...}` commands; especially Proposition `an`, Lemma 1 in the proof of `bigpoly`, and the introduction background citations.
- **Difficulty:** the uploaded LaTeX names `references.bib` but that bibliography file was not supplied. Therefore bibliography keys such as `gevrey`, `dudley`, `attractor`, `attractor2`, and the grouped KdV/Kuramoto–Sivashinsky keys cannot be resolved from the supplied source to exact titles/authors/pages beyond what is literally named in the text. The theorem/lemma numbers explicitly printed in the paper have been preserved.
- **Lean statement attempted:** declarations are documented by the exact bibliography key and theorem/lemma number present in the paper.
- **Smallest correction/clarification:** supply `references.bib`. No mathematical signature should be changed solely from bibliographic guesswork; if the bibliography reveals materially different hypotheses, specialize the corresponding declaration to the exact source theorem.

## C-3 — Lions–Magenes citation is unfinished in the paper

- **Paper location:** Appendix, section `Regularity of the Hyperviscous NSE`, immediately before equation `hyperviscous enstrophy dynamics equation`.
- **Difficulty:** the paper says “Elementary energy estimates and the Lions-Magenes lemma imply” the energy/enstrophy identities, followed by the source comment `%TODO citation for lions magenes`. No exact lemma statement, function-space hypotheses, bibliography key, or theorem number is supplied. The standard Lions–Magenes energy-chain-rule theorem is plausible here, but choosing one formulation without the intended Gelfand triple and time-regularity hypotheses would silently change the argument.
- **Lean statement attempted:** none; no axiom was introduced.
- **Smallest correction/clarification:** this cannot remain a permanent hole. Resolve it in one of two ways: (a) supply the intended Lions–Magenes/Temam reference and exact hypotheses, then add one narrowly scoped citation axiom; or (b) prove the two displayed energy/enstrophy differentiation identities directly from the concrete solution regularity available in the project, eliminating the external citation dependency altogether.

## C-4 — Dirichlet-boundary linear-span density has no attached citation

- **Paper location:** Introduction, paragraph immediately after the Bardos–Tartar conjecture.
- **Difficulty:** the sentence states that under Dirichlet boundary conditions the linear span of `G_T` is dense in `H`, but no `\cite{...}` is attached. A close literature match is Fernández-Cara--González-Burgos, *A Result Concerning Controllability for the Navier–Stokes Equations*, SIAM J. Control Optim. 33 (1995), 1061–1070, DOI 10.1137/S0363012993253819: its main result says the linear space spanned by final states is dense in the admissible `L²` space when boundary trace is used as control. The uploaded paper does not identify this source, and an equivalence between that controllability formulation and the paper's `G_T` statement with the intended Dirichlet setup has not been established.
- **Lean statement attempted:** none; it remains catalogued but is not an axiom.
- **Smallest correction/clarification:** either identify the intended source and prove that its final-state set is the paper's `G_T` in the stated boundary-value problem, or treat the sentence as an uncited paper assertion and prove it in the project. It must not be left as an untracked mathematical claim.

## C-5 — CFKM source theorem versus the paper's abstract `weakBTcon` formulation

- **Paper location:** Appendix theorem `weak density proposition` and the sentence immediately after it.
- **Difficulty:** the paper states an abstract theorem for any semigroup satisfying Condition `weakBTcon`, then says “The previous theorem is `\cite[Lemma 3.9/Theorem 3.1]{cfkm}` in the specific case of the 2D NSE.” Thus the cited literature result is specific, while the paper uses an abstract adaptation of its argument. The uploaded paper does not separately prove every topological step of that adaptation.
- **Lean statement attempted:** `BardosTartar.Citations.cfkm_lemma3_9_theorem3_1_statement` records the paper-facing conclusion and `WeakBTConditions` records the contract, but no axiom asserts the abstract implication.
- **Smallest correction/clarification:** after the canonical periodic NSE model exists, add an axiom only for the exact 2D-NSE CFKM theorem. Separately prove the abstract `WeakBTConditions → weak-density conclusion` implication (or the exact hyperviscous specialization) inside the project.

## C-6 — introduction grouping does not identify individual KdV/KS source roles

- **Paper location:** Introduction, main-results paragraph citing `GuoTiti, Bourgain, BabinIlyinTiti, Kukavica` in one group.
- **Difficulty:** the prose makes distinct assertions—global extendability of periodic KdV, and nonexistence of complete trajectories outside the global attractor for viscous/Kuramoto–Sivashinsky models—but the grouped citation does not map each assertion to a theorem number in a specific reference.
- **Lean statement attempted:** the assertions are separated into `periodicKdV_globalExtendability_statement`, `guoTiti_kbs_globalTrajectory_mem_attractor_statement`, and `kuramotoSivashinsky_globalTrajectory_mem_attractor_statement`; their docstrings preserve only the source keys supportable from the paper text.
- **Smallest correction/clarification:** recover `references.bib` and attach each assertion to its intended reference/theorem number. These introduction-only statements need not become dependencies of the headline proofs, but they still require source-complete coverage.

## C-7 — generic adapter axioms would silently strengthen PDE citations

- **Paper location:** all PDE-specific citations, especially C1/C2/C3, CFKM weak density, Proposition `an`, and the introduction-only trajectory statements.
- **Difficulty:** an axiom quantified over arbitrary `DynamicsData`, arbitrary `isNSESolutionOn`, or arbitrary attractor predicates would say much more than a theorem about one concrete PDE and could be instantiated with unrelated dynamics.
- **Lean statement attempted:** these items remain proposition-valued `..._statement` declarations.  `Foundations/Spectrum.lean` and coefficient-level `P/Q` no longer block integration; the remaining blocker is the canonical phase-space/Fourier and NSE dynamics bridge.
- **Smallest correction/clarification:** once that bridge exists, replace the relevant statement interfaces with individually documented axioms on the concrete project objects. Remove or demote obsolete adapter vocabulary after downstream users migrate.

## C-8 — Gevrey citation versus the paper's coefficient-growth consequence

- **Paper location:** proof of Theorem `eve`, Proposition `an`, immediately after the power-series representation.
- **Difficulty:** the paper cites `\cite[Theorem 1.1]{gevrey}` for real analyticity, then obtains coefficient growth from the radius/ratio argument. The former Agent C interface incorrectly bundled the geometric coefficient estimate into the cited statement. In addition, the printed form `‖U^m‖ ≤ C^m` for every `m ≥ 0` forces `‖U^0‖ ≤ 1` because `C^0 = 1`, which is not available for arbitrary initial data.
- **Lean statement attempted:** `gevrey_theorem1_1_statement` has been narrowed to real analyticity only. The coefficient-growth estimate is no longer a citation assumption.
- **Smallest correction/clarification:** prove a mathematically valid geometric bound from the local Banach-valued power series inside the project, for example `‖U^m‖ ≤ A * R^{-m}` or an equivalent `C^(m+1)` envelope, and then derive the Fourier-coefficient estimate. If the exact printed `C^m` form is required, state the additional normalization or restrict the exponent range needed by the later recurrence argument.


# Formalization issues — Wave 1 Agent E

## Appendix, Lemma `poly` (Polynomial coefficient bound)

**Paper location:** Appendix, “Miscellaneous results”, Lemma `poly` and its proof (the interpolation grid `x_i = a + i(b-a)/d`).

**Exact difficulty:** The printed statement quantifies over arbitrary `a,b ∈ ℝ`, but the claimed bound is false on the degenerate interval `a=b`: a polynomial can vanish at the single point `a` while having an arbitrarily large nonconstant coefficient. The printed proof also divides by `b-a`. Separately, the displayed interpolation grid divides by `d`, so the proof as written does not cover the degree-zero case.

**Lean statement attempted:**

```lean
theorem polynomial_coefficient_bound_interval (a b : ℝ) (hab : a < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (P : ℝ[X]) (M : ℝ), P.natDegree ≤ d → 0 ≤ M →
        PolynomialBoundedOn (Set.Icc a b) P M →
        ∀ k : ℕ, |P.coeff k| ≤ C ^ d * M
```

**Smallest proposed correction / clarification:** Add the nondegeneracy hypothesis `a < b` (equivalently `a ≠ b` after ordering the endpoints), and split `d=0` before defining the equally spaced interpolation grid. This does not alter Lemma `bigpoly`: a compact set of positive Lebesgue measure cannot be a singleton and can be enclosed in a nondegenerate compact interval.
