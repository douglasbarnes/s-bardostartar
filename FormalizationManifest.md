# Formalization manifest — Wave 1 Agent C

This table covers every externally sourced mathematical assertion identified in the uploaded paper.  Physical motivation, numerical-method motivation, and conjectures are listed separately at the end because they are not theorem assumptions.

| Paper location | Imported mathematical assertion | Source key(s) in paper | Lean declaration / disposition |
|---|---|---|---|
| Introduction, first paragraph | Global forward well-posedness/solution-operator regularity for the 2D periodic NSE | `ConstantinFoias`, `Temam`, `TemamBook` | `BardosTartar.Citations.constantinFoias_temam_periodic2D_wellPosedness` |
| Appendix, Condition C2 and proof of `Property DNB for s-viscous` | Backward uniqueness / injectivity of every positive-time map | `BardosTartar` (with `ConstantinFoias` at the use-site) | `BardosTartar.Citations.bardosTartar_periodic2D_backwardsUniqueness` |
| Appendix, Condition C3 and proof of `Property DNB for s-viscous` | Strong energy and enstrophy dissipation thresholds | `ConstantinFoias`, `BardosTartar` | `BardosTartar.Citations.constantinFoias_bardosTartar_periodic2D_strongDissipation` |
| Introduction and Appendix theorem `weak density proposition` | CFKM weak-density / prescribed-low-mode complete-trajectory construction with tail control | `cfkm`, explicitly identified as Lemma 3.9 / Theorem 3.1 | `BardosTartar.Citations.cfkm_lemma3_9_theorem3_1` |
| Introduction, main-results discussion | Backward classification of complete 2D periodic NSE trajectories: attractor / Stokes exponential rate / super-exponential growth | `cfkm` | `BardosTartar.Citations.cfkm_backwardTrajectory_classification` |
| Proof of Theorem `eve`, Proposition `an` | Time real-analyticity and a local power-series expansion with geometric coefficient growth | `gevrey`, Theorem 1.1 | `BardosTartar.Citations.gevrey_theorem1_1` |
| Appendix, proof of polynomial coefficient bound `bigpoly` | Remez/Dudley inequality comparing polynomial suprema on an interval and a closed positive-measure subset | `dudley`, Lemma 1 | `BardosTartar.Citations.dudley_lemma1` |
| Appendix, `Notation` | Unbounded gaps between consecutive Stokes spectral values, reduced to gaps between sums of two squares | `Erdos` | `BardosTartar.Citations.erdos_unbounded_sum_two_squares_gaps` |
| Introduction, paragraph after Bardos–Tartar conjecture | Global attractor has finite Hausdorff dimension in the `L²` metric | `attractor`, `attractor2` | `BardosTartar.Citations.nse_globalAttractor_finiteHausdorffDimension` |
| Introduction, backward-behaviour paragraph | Periodic KdV is globally extendable / globally well posed | `Bourgain`, `BabinIlyinTiti` | `BardosTartar.Citations.periodicKdV_globalExtendability` |
| Introduction, backward-behaviour paragraph | For the cited viscous KdV/KdV–Burgers–Sivashinsky setting, a complete trajectory must lie in the global attractor | `GuoTiti` | `BardosTartar.Citations.guoTiti_kbs_globalTrajectory_mem_attractor` |
| Introduction, same paragraph | A complete Kuramoto–Sivashinsky trajectory lies in the global attractor | `Kukavica` (grouped at the paper use-site) | `BardosTartar.Citations.kuramotoSivashinsky_globalTrajectory_mem_attractor` |
| Appendix, energy/enstrophy identities in hyperviscous regularity section | Lions–Magenes weak-time-regularity lemma used to justify differentiating the squared norms | Named but bibliography citation is explicitly left as a TODO in the paper | **Not axiomatized:** exact source and hypotheses are missing; recorded in `FormalizationIssues.md` rather than inventing a statement. |
| Introduction | For Dirichlet boundary conditions, the linear span of `G_T` is dense in `H` | No citation is attached to this sentence in the uploaded source | **Not axiomatized:** attribution/source statement is missing; recorded in `FormalizationIssues.md`. |

## Cited material deliberately not made into citation axioms

| Paper material | Disposition |
|---|---|
| Definitions of homogeneous Sobolev spaces, Leray projection, Stokes operator, Fourier eigenspaces, `λ_n → ∞`, and the elementary lower spectral-gap bound | Foundational mathematics; Wave 1 Agents A/B must formalize/prove these in the repository representation. Only the non-elementary unbounded-gap input is in `Citations/`. |
| CFKM Lemma 3.2 mentioned while proving DNB | The paper follows/adapts its proof but genuinely derives the hyperviscous DNB using new convexity estimates. The hyperviscous DNB is therefore **not** a citation axiom. |
| The sum-of-two-squares representation-count/divisor bound used in `partition set bounds'` | The uploaded paper gives no literature citation. Per the assignment, Agent B must prove the exact required estimate from Mathlib/number theory rather than treating the phrase “divisor bound” as an assumption. |
| Bardos–Tartar density statement | It is explicitly a conjecture, not an imported theorem. |
| Bardos–Tartar-type hyperviscous question attributed to `GuoTiti` | It is background/conjectural motivation, not a theorem assumption. |
| Hyperviscous torque-stress and numerical-regularisation claims (`vijay`, `numerical`) | Physical/numerical motivation only; no formal mathematical assertion needed by this development. |
| Claims about atmosphere/oceans/turbulence/real-life flows | Motivational/physical prose, not formalized. |

## Citation dependency rule

No declaration in `Citations/` is intended to stand in for a theorem that the uploaded paper proves itself.  In particular, the hyperviscous Dirichlet barrier, BEDR, barren-data deductions, nonlinear transfer bounds, recurrence/growth arguments, and measure contradiction remain proof obligations for later agents.
