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

At this wave boundary, only model-independent citations whose exact mathematical objects
are already available are asserted as axioms (`dudley_lemma1` and
`erdos_unbounded_sum_two_squares_gaps`).  PDE-specific citations are indexed as typed
statement interfaces pending the concrete periodic Navier--Stokes foundation API; this
avoids asserting literature results for arbitrary adapter predicates/dynamics.
-/

namespace BardosTartar.PaperIndex

-- Classical periodic NSE citation statements.
#check BardosTartar.Citations.constantinFoias_temam_periodic2D_wellPosedness_statement
#check BardosTartar.Citations.bardosTartar_periodic2D_backwardsUniqueness_statement
#check BardosTartar.Citations.constantinFoias_bardosTartar_periodic2D_strongDissipation_statement

-- CFKM citation statements.
#check BardosTartar.Citations.cfkm_lemma3_9_theorem3_1_statement
#check BardosTartar.Citations.cfkm_backwardTrajectory_classification_statement

-- Time analyticity statement; to be specialized to the concrete NSE solution relation.
#check BardosTartar.Citations.gevrey_theorem1_1_statement

-- Exact, model-independent citation axioms.
#check BardosTartar.Citations.dudley_lemma1
#check BardosTartar.Citations.erdos_unbounded_sum_two_squares_gaps

-- Introduction-only mathematical background statements.
#check BardosTartar.Citations.nse_globalAttractor_finiteHausdorffDimension_statement
#check BardosTartar.Citations.periodicKdV_globalExtendability_statement
#check BardosTartar.Citations.guoTiti_kbs_globalTrajectory_mem_attractor_statement
#check BardosTartar.Citations.kuramotoSivashinsky_globalTrajectory_mem_attractor_statement

end BardosTartar.PaperIndex
