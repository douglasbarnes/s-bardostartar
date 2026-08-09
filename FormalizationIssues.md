# Formalization issues — Wave 1 Agent C

## C-1 — repository integration/build unavailable at start of wave

- **Paper location:** project-wide, not a paper statement.
- **Difficulty:** the connected `douglasbarnes/s-bardostartar` repository was empty when Agent C began: there was no `lakefile`, `lean-toolchain`, foundation namespace, Fourier model, or existing `PaperIndex.lean`.  The local execution environment also has no `lean`/`lake` executable.  Consequently the citation layer could be written but cannot yet be checked against the pinned project or connected to the final concrete phase-space types.
- **Lean statement attempted:** citation declarations use representation-neutral interfaces in `Citations/Interfaces.lean`; PDE-specific theorem statements expose explicit adapter hooks where a concrete solution predicate is not yet available.
- **Smallest correction/clarification:** once the project skeleton and Wave 1 foundation APIs exist, identify `DynamicsData`, its norms/projections/spectrum, and the time-analyticity solution predicate with those concrete definitions, then run the required `lake build` target.  No alternative Fourier representation should be introduced.

## C-2 — missing `references.bib`

- **Paper location:** all `\cite{...}` commands; especially Proposition `an`, Lemma 1 in the proof of `bigpoly`, and the introduction background citations.
- **Difficulty:** the uploaded LaTeX names `references.bib` but that bibliography file was not supplied.  Therefore bibliography keys such as `gevrey`, `dudley`, `attractor`, `attractor2`, and the grouped KdV/Kuramoto–Sivashinsky keys cannot be resolved from the source material to exact titles/authors/pages beyond what is literally named in the text.  The theorem/lemma numbers explicitly printed in the paper have been preserved.
- **Lean statement attempted:** declarations are documented by the exact bibliography key and theorem/lemma number present in the paper.
- **Smallest correction/clarification:** supply `references.bib`.  No mathematical signature needs changing solely for this metadata issue unless the bibliography reveals that the cited source has materially different hypotheses.

## C-3 — Lions–Magenes citation is unfinished in the paper

- **Paper location:** Appendix, section `Regularity of the Hyperviscous NSE`, immediately before equation `hyperviscous enstrophy dynamics equation`.
- **Difficulty:** the paper says “Elementary energy estimates and the Lions-Magenes lemma imply” the energy/enstrophy identities, followed by the source comment `%TODO citation for lions magenes`.  No exact lemma statement, function-space hypotheses, bibliography key, or theorem number is supplied.  Several inequivalent Lions–Magenes lemmas exist, and replacing the missing source by a convenient chain rule would silently change the regularity assumptions.
- **Lean statement attempted:** none; no axiom was introduced because an exact external statement cannot be recovered from the uploaded source alone.
- **Smallest correction/clarification:** give the intended Lions–Magenes reference and precise Gelfand-triple/time-regularity hypotheses.  Then add one narrowly scoped citation axiom for that lemma only.

## C-4 — Dirichlet-boundary linear-span density has no attached citation

- **Paper location:** Introduction, paragraph immediately after the Bardos–Tartar conjecture.
- **Difficulty:** the sentence states that under Dirichlet boundary conditions the linear span of `G_T` is dense in `H`, but no `\cite{...}` is attached to that assertion in the uploaded source.  It is mathematically substantive, but its source and exact boundary/solution-space hypotheses are not identifiable from the paper text.
- **Lean statement attempted:** none; it is catalogued in `FormalizationManifest.md` but not made an axiom.
- **Smallest correction/clarification:** add the intended bibliography citation and theorem number/hypotheses, or explicitly mark the statement as an uncited background observation.

## C-5 — CFKM source theorem versus the paper's abstract `weakBTcon` formulation

- **Paper location:** Appendix theorem `weak density proposition` and the sentence immediately after it.
- **Difficulty:** the paper states an abstract theorem for any semigroup satisfying Condition `weakBTcon`, then says “The previous theorem is `\cite[Lemma 3.9/Theorem 3.1]{cfkm}` in the specific case of the 2D NSE.”  Thus the cited literature theorem is specific, while the paper uses an abstract adaptation of its argument.  The uploaded paper does not separately prove every topological step of that adaptation.
- **Lean statement attempted:** `BardosTartar.Citations.cfkm_lemma3_9_theorem3_1` is a paper-facing citation interface whose hypothesis is the explicitly formalized `WeakBTConditions` contract.  It does **not** assume any hyperviscous DNB/BEDR beyond those contract fields and does not include the later barren-data deductions.
- **Smallest correction/clarification:** either (a) explicitly state in the paper that the abstract theorem is being imported as a verbatim adaptation of CFKM, or (b) supply a proof of the abstract adaptation, in which case the Lean axiom should be narrowed to the exact 2D NSE CFKM theorem and the abstract theorem should be proved downstream.

## C-6 — introduction grouping does not identify individual KdV/KS source roles

- **Paper location:** Introduction, main-results paragraph citing `GuoTiti, Bourgain, BabinIlyinTiti, Kukavica` in one group.
- **Difficulty:** the prose makes two distinct assertions—global extendability of periodic KdV, and nonexistence of complete trajectories outside the global attractor for viscous/Kuramoto–Sivashinsky models—but the grouped citation does not map each assertion to a theorem number in a specific reference.
- **Lean statement attempted:** the assertions are separated into `periodicKdV_globalExtendability`, `guoTiti_kbs_globalTrajectory_mem_attractor`, and `kuramotoSivashinsky_globalTrajectory_mem_attractor`; their docstrings preserve only the source keys supportable from the paper text.
- **Smallest correction/clarification:** attach each assertion to its intended reference/theorem number in the bibliography.
