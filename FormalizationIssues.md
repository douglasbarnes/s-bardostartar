# Formalization issues — Wave 1 Agent C

## C-1 — repository integration/build unavailable at start of wave

- **Paper location:** project-wide, not a paper statement.
- **Difficulty:** the connected `douglasbarnes/s-bardostartar` repository was empty when Agent C began: there was no `lakefile`, `lean-toolchain`, foundation namespace, Fourier model, or existing `PaperIndex.lean`. The execution environment also has no `lean` or `lake` executable. Consequently the citation layer can be written and audited textually, but cannot yet be checked against the pinned project or connected to the final concrete phase-space types.
- **Lean statement attempted:** citation vocabulary is representation-neutral in `Citations/Interfaces.lean`; PDE-specific external assertions are recorded as proposition-valued statement interfaces rather than universally quantified axioms over arbitrary dynamics.
- **Smallest correction/clarification:** once the project skeleton and Wave 1 foundation APIs exist, identify `DynamicsData`, its norms/projections/spectrum, and the time-analyticity solution predicate with those concrete definitions; specialize the PDE citation interfaces to those definitions; then run the required `lake build` target. No alternative Fourier representation should be introduced.

## C-2 — missing `references.bib`

- **Paper location:** all `\cite{...}` commands; especially Proposition `an`, Lemma 1 in the proof of `bigpoly`, and the introduction background citations.
- **Difficulty:** the uploaded LaTeX names `references.bib` but that bibliography file was not supplied. Therefore bibliography keys such as `gevrey`, `dudley`, `attractor`, `attractor2`, and the grouped KdV/Kuramoto–Sivashinsky keys cannot be resolved from the source material to exact titles/authors/pages beyond what is literally named in the text. The theorem/lemma numbers explicitly printed in the paper have been preserved.
- **Lean statement attempted:** declarations are documented by the exact bibliography key and theorem/lemma number present in the paper.
- **Smallest correction/clarification:** supply `references.bib`. No mathematical signature needs changing solely for this metadata issue unless the bibliography reveals materially different hypotheses.

## C-3 — Lions–Magenes citation is unfinished in the paper

- **Paper location:** Appendix, section `Regularity of the Hyperviscous NSE`, immediately before equation `hyperviscous enstrophy dynamics equation`.
- **Difficulty:** the paper says “Elementary energy estimates and the Lions-Magenes lemma imply” the energy/enstrophy identities, followed by the source comment `%TODO citation for lions magenes`. No exact lemma statement, function-space hypotheses, bibliography key, or theorem number is supplied. Several inequivalent Lions–Magenes lemmas exist, and replacing the missing source by a convenient chain rule would silently change the regularity assumptions.
- **Lean statement attempted:** none; no axiom was introduced because an exact external statement cannot be recovered from the uploaded source alone.
- **Smallest correction/clarification:** give the intended Lions–Magenes reference and precise Gelfand-triple/time-regularity hypotheses. Then add one narrowly scoped citation axiom for that lemma only.

## C-4 — Dirichlet-boundary linear-span density has no attached citation

- **Paper location:** Introduction, paragraph immediately after the Bardos–Tartar conjecture.
- **Difficulty:** the sentence states that under Dirichlet boundary conditions the linear span of `G_T` is dense in `H`, but no `\cite{...}` is attached to that assertion in the uploaded source. It is mathematically substantive, but its source and exact boundary/solution-space hypotheses are not identifiable from the paper text.
- **Lean statement attempted:** none; it is catalogued in `FormalizationManifest.md` but not made an axiom.
- **Smallest correction/clarification:** add the intended bibliography citation and theorem number/hypotheses, or explicitly mark the statement as an uncited background observation.

## C-5 — CFKM source theorem versus the paper's abstract `weakBTcon` formulation

- **Paper location:** Appendix theorem `weak density proposition` and the sentence immediately after it.
- **Difficulty:** the paper states an abstract theorem for any semigroup satisfying Condition `weakBTcon`, then says “The previous theorem is `\cite[Lemma 3.9/Theorem 3.1]{cfkm}` in the specific case of the 2D NSE.” Thus the cited literature result is specific, while the paper uses an abstract adaptation of its argument. The uploaded paper does not separately prove every topological step of that adaptation.
- **Lean statement attempted:** `BardosTartar.Citations.cfkm_lemma3_9_theorem3_1_statement` records the paper-facing conclusion and `WeakBTConditions` records the contract, but no axiom asserts the abstract implication.
- **Smallest correction/clarification:** either (a) explicitly state/prove the abstract adaptation in the paper/project, or (b) after the concrete periodic NSE model exists, add a citation axiom only for the exact source theorem and derive the abstract/hyperviscous uses separately.

## C-6 — introduction grouping does not identify individual KdV/KS source roles

- **Paper location:** Introduction, main-results paragraph citing `GuoTiti, Bourgain, BabinIlyinTiti, Kukavica` in one group.
- **Difficulty:** the prose makes distinct assertions—global extendability of periodic KdV, and nonexistence of complete trajectories outside the global attractor for viscous/Kuramoto–Sivashinsky models—but the grouped citation does not map each assertion to a theorem number in a specific reference.
- **Lean statement attempted:** the assertions are separated into `periodicKdV_globalExtendability_statement`, `guoTiti_kbs_globalTrajectory_mem_attractor_statement`, and `kuramotoSivashinsky_globalTrajectory_mem_attractor_statement`; their docstrings preserve only the source keys supportable from the paper text.
- **Smallest correction/clarification:** attach each assertion to its intended reference/theorem number in the bibliography.

## C-7 — generic adapter axioms would silently strengthen PDE citations

- **Paper location:** all PDE-specific citations, especially C1/C2/C3, CFKM weak density, Proposition `an`, and the introduction-only trajectory statements.
- **Difficulty:** before the concrete phase-space/solution APIs exist, an axiom quantified over an arbitrary `DynamicsData`, arbitrary `isNSESolutionOn`, or arbitrary attractor predicate would say much more than the cited theorem and can be instantiated with objects unrelated to the cited PDE. This violates the project's rule against silently strengthening or reinterpreting source statements.
- **Lean statement attempted:** these items are therefore proposition-valued `..._statement` declarations only. The only active citation axioms at this wave boundary are the model-independent `dudley_lemma1` and `erdos_unbounded_sum_two_squares_gaps`.
- **Smallest correction/clarification:** expose the concrete periodic 2D NSE types/solution relation/projections/spectrum from the foundation and dynamics layers, then replace each relevant statement interface by one individually documented axiom specialized to those concrete objects. Introduction-only KdV/KS statements need not become project assumptions unless later coverage policy requires executable declarations.
