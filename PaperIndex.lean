import Citations.Interfaces
import Citations.NavierStokes
import Citations.CFKM
import Citations.TimeAnalyticity
import Citations.PolynomialInequality
import Citations.SpectralGap
import Citations.TrajectoryClassification
import Citations.Background

/-!
# Paper index — citation portion

Wave 1 Agent C owns only this citation index.  Later integration agents may append
paper-original declarations, but externally cited assumptions must continue to live in
`Citations/` only.

The final citation-policy boundary is: each imported theorem becomes an individually
named assumption on the canonical project objects.  At present the model-independent
Dudley and Erdős inputs satisfy that boundary.  PDE-specific citations remain typed
statement interfaces only because the repository still lacks the canonical `H`/`V`
phase-space bridge and NSE solution semigroup; `API_REQUESTS/agent-c.md` records that
remaining dependency.
-/

namespace BardosTartar.PaperIndex

-- Classical periodic NSE citation statements: must become concrete axioms after the
-- canonical phase-space/dynamics bridge lands.
#check BardosTartar.Citations.constantinFoias_temam_periodic2D_wellPosedness_statement
#check BardosTartar.Citations.bardosTartar_periodic2D_backwardsUniqueness_statement
#check BardosTartar.Citations.constantinFoias_bardosTartar_periodic2D_strongDissipation_statement

-- CFKM citation statements.  The exact source theorem is 2D-NSE-specific; the paper's
-- abstract `weakBTcon` adaptation remains a project proof obligation.
#check BardosTartar.Citations.cfkm_lemma3_9_theorem3_1_statement
#check BardosTartar.Citations.cfkm_backwardTrajectory_classification_statement

-- Gevrey Theorem 1.1 interface: analyticity only.  The zero-centred expansion and its
-- coefficient-growth estimate are downstream deductions, not citation assumptions.
#check BardosTartar.Citations.gevrey_theorem1_1_statement

-- Exact, model-independent citation axioms.
#check BardosTartar.Citations.dudley_lemma1
#check BardosTartar.Citations.dudley_polynomial_sup_bound
#check BardosTartar.Citations.erdos_unbounded_sum_two_squares_gaps

-- Introduction-only mathematical background statements.
#check BardosTartar.Citations.nse_globalAttractor_finiteHausdorffDimension_statement
#check BardosTartar.Citations.periodicKdV_globalExtendability_statement
#check BardosTartar.Citations.guoTiti_kbs_globalTrajectory_mem_attractor_statement
#check BardosTartar.Citations.kuramotoSivashinsky_globalTrajectory_mem_attractor_statement

end BardosTartar.PaperIndex
