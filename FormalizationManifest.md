# Formalization manifest — Wave 1 Agent C

This table covers every externally sourced mathematical assertion identified in the
uploaded paper. Physical motivation, numerical-method motivation, and conjectures are
listed separately because they are not theorem assumptions.

**Status convention.** `AXIOM` means the exact cited result is asserted in `Citations/`.
`STATEMENT / API-BLOCKED` means the source assertion is typed and documented, but is not
yet asserted because the repository still lacks the canonical PDE object needed to state
the literature theorem without quantifying over arbitrary adapter data.  These entries
are not considered the final citation-policy boundary: once the canonical phase-space and
dynamics bridge lands, they must be replaced by individually named assumptions on those
objects.

| Paper location | Imported mathematical assertion | Source key(s) in paper | Lean declaration / disposition |
|---|---|---|---|
| Introduction, first paragraph; Appendix C1 use-site | Global forward well-posedness/solution-operator regularity for the 2D periodic NSE | `ConstantinFoias`, `Temam`, `TemamBook` | **STATEMENT / API-BLOCKED:** `BardosTartar.Citations.constantinFoias_temam_periodic2D_wellPosedness_statement` |
| Appendix, Condition C2 and proof of `Property DNB for s-viscous` | Backward uniqueness / injectivity of every positive-time map of the 2D periodic NSE | `BardosTartar` (with `ConstantinFoias` at the use-site) | **STATEMENT / API-BLOCKED:** `BardosTartar.Citations.bardosTartar_periodic2D_backwardsUniqueness_statement` |
| Appendix, Condition C3 and proof of `Property DNB for s-viscous` | Strong energy and enstrophy dissipation thresholds for the 2D periodic NSE | `ConstantinFoias`, `BardosTartar` | **STATEMENT / API-BLOCKED:** `BardosTartar.Citations.constantinFoias_bardosTartar_periodic2D_strongDissipation_statement` |
| Introduction and Appendix theorem `weak density proposition` | CFKM weak-density / prescribed-low-mode complete-trajectory construction with tail control | `cfkm`, explicitly identified as Lemma 3.9 / Theorem 3.1 | **STATEMENT / API-BLOCKED:** `BardosTartar.Citations.cfkm_lemma3_9_theorem3_1_statement`; the abstract `weakBTcon` adaptation is not silently axiomatized |
| Introduction, main-results discussion | Backward classification of complete 2D periodic NSE trajectories: attractor / Stokes exponential rate / super-exponential growth | `cfkm` | **STATEMENT / API-BLOCKED:** `BardosTartar.Citations.cfkm_backwardTrajectory_classification_statement` |
| Proof of Theorem `eve`, Proposition `an` | Real analyticity in time of a backward-extendable 2D periodic NSE trajectory | `gevrey`, Theorem 1.1 | **STATEMENT / API-BLOCKED:** `BardosTartar.Citations.gevrey_theorem1_1_statement` now contains analyticity only |
| Appendix, proof of polynomial coefficient bound `bigpoly` | Remez/Dudley inequality comparing polynomial suprema on an interval and a closed positive-measure subset | `dudley`, Lemma 1 | **AXIOM:** `BardosTartar.Citations.dudley_lemma1`; API alias `dudley_polynomial_sup_bound` introduces no new assumption |
| Appendix, `Notation` | Unbounded gaps between consecutive Stokes spectral values, reduced to gaps between integers representable as sums of two squares | `Erdos` | **AXIOM:** `BardosTartar.Citations.erdos_unbounded_sum_two_squares_gaps` |
| Introduction, paragraph after Bardos–Tartar conjecture | Global attractor has finite Hausdorff dimension in the `L²` metric | `attractor`, `attractor2` | **STATEMENT / API-BLOCKED:** `BardosTartar.Citations.nse_globalAttractor_finiteHausdorffDimension_statement` |
| Introduction, backward-behaviour paragraph | Periodic KdV is globally extendable / globally well posed | `Bourgain`, `BabinIlyinTiti` | **STATEMENT:** `BardosTartar.Citations.periodicKdV_globalExtendability_statement`; no canonical KdV model is part of this project |
| Introduction, backward-behaviour paragraph | For the cited viscous KdV/KdV–Burgers–Sivashinsky setting, a complete trajectory must lie in the global attractor | `GuoTiti` | **STATEMENT:** `BardosTartar.Citations.guoTiti_kbs_globalTrajectory_mem_attractor_statement` |
| Introduction, same paragraph | A complete Kuramoto–Sivashinsky trajectory lies in its global attractor | `Kukavica` (grouped at the paper use-site) | **STATEMENT:** `BardosTartar.Citations.kuramotoSivashinsky_globalTrajectory_mem_attractor_statement` |
| Appendix, energy/enstrophy identities in hyperviscous regularity section | Lions–Magenes weak-time-regularity lemma used to justify differentiating the squared norms | Named but bibliography citation is explicitly left as a TODO in the paper | **SOURCE-BLOCKED:** no axiom or guessed statement; resolution options are recorded in `FormalizationIssues.md` |
| Introduction | For Dirichlet boundary conditions, the linear span of `G_T` is dense in `H` | No citation is attached to this sentence in the uploaded source | **SOURCE-BLOCKED:** no axiom; resolution options are recorded in `FormalizationIssues.md` |

## Paper deductions deliberately excluded from citation axioms

| Paper material | Disposition |
|---|---|
| Local power-series expansion at `t=0` from Proposition `an` | Must be derived from the cited time-analyticity result after the canonical NSE solution relation is available. |
| Geometric norm bound on the power-series coefficients, and the corresponding Fourier-coefficient bound | Must be proved inside the project from convergence/analyticity plus the Fourier norm estimate. It is **not** part of `gevrey_theorem1_1_statement`; see issue C-8 concerning the printed `C^m` normalization. |
| Definitions of homogeneous Sobolev spaces, Leray projection, Stokes operator, Fourier eigenspaces, `λ_n → ∞`, and the elementary lower spectral-gap bound | Foundational mathematics. `Foundations/Spectrum.lean` now supplies the canonical `lambda` sequence and `Foundations/Projections.lean` supplies coefficient-level `P/Q`; the remaining citation blocker is the canonical function-space bridge and dynamics API. Only the non-elementary unbounded-gap input is a citation axiom. |
| CFKM Lemma 3.2 mentioned while proving DNB | The paper follows/adapts its proof but genuinely derives the hyperviscous DNB using new convexity estimates. The hyperviscous DNB is therefore **not** a citation axiom. |
| The hyperviscous extensions of C1/C2/C3 | The paper says their arguments are the same as in the 2D NSE literature. The cited sources establish classical NSE facts; the hyperviscous specialization is a downstream proof/adaptation obligation, not a blanket literature axiom. |
| The sum-of-two-squares representation-count/divisor bound used in `partition set bounds'` | The uploaded paper gives no literature citation. Agent B must prove the exact required estimate rather than treating the phrase “divisor bound” as an assumption. |
| Bardos–Tartar density statement | It is explicitly a conjecture, not an imported theorem. |
| Bardos–Tartar-type hyperviscous question attributed to `GuoTiti` | It is background/conjectural motivation, not a theorem assumption. |
| Hyperviscous torque-stress and numerical-regularisation claims (`vijay`, `numerical`) | Physical/numerical motivation only; no formal mathematical assertion is needed by this development. |
| Claims about atmosphere/oceans/turbulence/real-life flows | Motivational/physical prose, not formalized. |

## Current citation-policy boundary

The Wave 1 citation layer is **not yet at the final policy boundary**.  The active
project-specific citation axioms are currently the model-independent Dudley inequality and
Erdős spectral-gap input.  The 2D periodic NSE citations must become exact assumptions on
the canonical project phase space/solution semigroup once the missing Agent A/dynamics
bridge is available.  `API_REQUESTS/agent-c.md` records only that remaining bridge; it no
longer requests spectrum or coefficient-level projection infrastructure that has already
landed.

No declaration in `Citations/` stands in for a theorem that the uploaded paper proves
itself.  In particular, the hyperviscous Dirichlet barrier, BEDR, abstract CFKM adaptation,
barren-data deductions, nonlinear transfer bounds, recurrence/growth arguments, analytic
coefficient-growth consequence, and measure contradiction remain proof obligations for
later agents.
