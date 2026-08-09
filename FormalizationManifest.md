# Formalization manifest — Wave 1 Agent C

This table covers every externally sourced mathematical assertion identified in the uploaded paper. Physical motivation, numerical-method motivation, and conjectures are listed separately because they are not theorem assumptions.

**Status convention.** `AXIOM` means the exact cited result is asserted in `Citations/`. `STATEMENT` means the source assertion has been typed and documented, but is deliberately not asserted yet because the repository did not contain the concrete PDE model needed to state the literature result without quantifying over arbitrary adapter data. Such entries must be specialized to the foundation API before they can become citation axioms.

| Paper location | Imported mathematical assertion | Source key(s) in paper | Lean declaration / disposition |
|---|---|---|---|
| Introduction, first paragraph; Appendix C1 use-site | Global forward well-posedness/solution-operator regularity for the 2D periodic NSE | `ConstantinFoias`, `Temam`, `TemamBook` | **STATEMENT:** `BardosTartar.Citations.constantinFoias_temam_periodic2D_wellPosedness_statement` |
| Appendix, Condition C2 and proof of `Property DNB for s-viscous` | Backward uniqueness / injectivity of every positive-time map of the 2D periodic NSE | `BardosTartar` (with `ConstantinFoias` at the use-site) | **STATEMENT:** `BardosTartar.Citations.bardosTartar_periodic2D_backwardsUniqueness_statement` |
| Appendix, Condition C3 and proof of `Property DNB for s-viscous` | Strong energy and enstrophy dissipation thresholds for the 2D periodic NSE | `ConstantinFoias`, `BardosTartar` | **STATEMENT:** `BardosTartar.Citations.constantinFoias_bardosTartar_periodic2D_strongDissipation_statement` |
| Introduction and Appendix theorem `weak density proposition` | CFKM weak-density / prescribed-low-mode complete-trajectory construction with tail control | `cfkm`, explicitly identified as Lemma 3.9 / Theorem 3.1 | **STATEMENT:** `BardosTartar.Citations.cfkm_lemma3_9_theorem3_1_statement`; abstract `weakBTcon` adaptation is not silently axiomatized |
| Introduction, main-results discussion | Backward classification of complete 2D periodic NSE trajectories: attractor / Stokes exponential rate / super-exponential growth | `cfkm` | **STATEMENT:** `BardosTartar.Citations.cfkm_backwardTrajectory_classification_statement` |
| Proof of Theorem `eve`, Proposition `an` | Time real-analyticity and a local power-series expansion with geometric coefficient growth | `gevrey`, Theorem 1.1 | **STATEMENT:** `BardosTartar.Citations.gevrey_theorem1_1_statement` |
| Appendix, proof of polynomial coefficient bound `bigpoly` | Remez/Dudley inequality comparing polynomial suprema on an interval and a closed positive-measure subset | `dudley`, Lemma 1 | **AXIOM:** `BardosTartar.Citations.dudley_lemma1` |
| Appendix, `Notation` | Unbounded gaps between consecutive Stokes spectral values, reduced to gaps between integers representable as sums of two squares | `Erdos` | **AXIOM:** `BardosTartar.Citations.erdos_unbounded_sum_two_squares_gaps` |
| Introduction, paragraph after Bardos–Tartar conjecture | Global attractor has finite Hausdorff dimension in the `L²` metric | `attractor`, `attractor2` | **STATEMENT:** `BardosTartar.Citations.nse_globalAttractor_finiteHausdorffDimension_statement` |
| Introduction, backward-behaviour paragraph | Periodic KdV is globally extendable / globally well posed | `Bourgain`, `BabinIlyinTiti` | **STATEMENT:** `BardosTartar.Citations.periodicKdV_globalExtendability_statement` |
| Introduction, backward-behaviour paragraph | For the cited viscous KdV/KdV–Burgers–Sivashinsky setting, a complete trajectory must lie in the global attractor | `GuoTiti` | **STATEMENT:** `BardosTartar.Citations.guoTiti_kbs_globalTrajectory_mem_attractor_statement` |
| Introduction, same paragraph | A complete Kuramoto–Sivashinsky trajectory lies in its global attractor | `Kukavica` (grouped at the paper use-site) | **STATEMENT:** `BardosTartar.Citations.kuramotoSivashinsky_globalTrajectory_mem_attractor_statement` |
| Appendix, energy/enstrophy identities in hyperviscous regularity section | Lions–Magenes weak-time-regularity lemma used to justify differentiating the squared norms | Named but bibliography citation is explicitly left as a TODO in the paper | **UNRESOLVED:** no axiom or guessed statement; exact source/hypotheses missing, recorded in `FormalizationIssues.md` |
| Introduction | For Dirichlet boundary conditions, the linear span of `G_T` is dense in `H` | No citation is attached to this sentence in the uploaded source | **UNRESOLVED:** no axiom; attribution/source hypotheses missing, recorded in `FormalizationIssues.md` |

## Cited material deliberately not made into citation axioms

| Paper material | Disposition |
|---|---|
| Definitions of homogeneous Sobolev spaces, Leray projection, Stokes operator, Fourier eigenspaces, `λ_n → ∞`, and the elementary lower spectral-gap bound | Foundational mathematics; Wave 1 Agents A/B must formalize/prove these in the repository representation. Only the non-elementary unbounded-gap input is a citation axiom. |
| CFKM Lemma 3.2 mentioned while proving DNB | The paper follows/adapts its proof but genuinely derives the hyperviscous DNB using new convexity estimates. The hyperviscous DNB is therefore **not** a citation axiom. |
| The hyperviscous extensions of C1/C2/C3 | The paper says their arguments are the same as in the 2D NSE literature. The cited sources establish classical NSE facts; the hyperviscous specialization is a downstream proof/adaptation obligation, not a blanket literature axiom. |
| The sum-of-two-squares representation-count/divisor bound used in `partition set bounds'` | The uploaded paper gives no literature citation. Per the assignment, Agent B must prove the exact required estimate from Mathlib/number theory rather than treating the phrase “divisor bound” as an assumption. |
| Bardos–Tartar density statement | It is explicitly a conjecture, not an imported theorem. |
| Bardos–Tartar-type hyperviscous question attributed to `GuoTiti` | It is background/conjectural motivation, not a theorem assumption. |
| Hyperviscous torque-stress and numerical-regularisation claims (`vijay`, `numerical`) | Physical/numerical motivation only; no formal mathematical assertion is needed by this development. |
| Claims about atmosphere/oceans/turbulence/real-life flows | Motivational/physical prose, not formalized. |

## Citation dependency rule

No declaration in `Citations/` stands in for a theorem that the uploaded paper proves itself. In particular, the hyperviscous Dirichlet barrier, BEDR, barren-data deductions, nonlinear transfer bounds, recurrence/growth arguments, and measure contradiction remain proof obligations for later agents.

At this wave boundary the only asserted project-specific citation axioms are the model-independent Dudley inequality and Erdős spectral-gap input. PDE citations remain typed statement interfaces until the concrete foundation API exists, because asserting them against arbitrary adapter predicates or arbitrary `DynamicsData` would silently strengthen the literature result.
