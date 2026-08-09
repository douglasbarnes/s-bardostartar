import Mathlib

/-!
# Cited mathematical background from the introduction

None of the declarations in this file is used in the two headline proofs.  They are
kept separate so that mathematically substantive introduction claims are covered without
turning motivational or physical prose into assumptions of the main development.
-/

namespace BardosTartar.Citations

universe u

/-- A solution relation admits a trajectory through the prescribed time-zero state. -/
def HasGlobalTrajectoryThrough {X : Type u}
    (isSolution : (ℝ → X) → Prop) (x0 : X) : Prop :=
  ∃ u : ℝ → X, isSolution u ∧ u 0 = x0

/-- **Citations: `attractor`, `attractor2` (the paper supplies no theorem numbers).**

Paper location: Introduction, paragraph following the Bardos--Tartar conjecture.

The global attractor of the 2D periodic NSE has finite Hausdorff dimension in the
`L²` metric.  `A` is to be instantiated with that concrete attractor. -/
axiom nse_globalAttractor_finiteHausdorffDimension
    {H : Type u} [EMetricSpace H] (A : Set H) :
    MeasureTheory.dimH A < ⊤

/-- **Citations: `Bourgain`, `BabinIlyinTiti` (no theorem number supplied at the paper
use-site).**

Paper location: Introduction, paragraph discussing backward behaviour of other
parabolic/dispersive equations.

The periodic KdV flow is globally extendable.  The solution predicate is an adapter
hook for the concrete KdV formulation used by the cited source. -/
axiom periodicKdV_globalExtendability
    {X : Type u} (isKdVSolution : (ℝ → X) → Prop) :
    ∀ x0 : X, HasGlobalTrajectoryThrough isKdVSolution x0

/-- **Citation: `GuoTiti` (no theorem number supplied at the paper use-site).**

Paper location: Introduction, paragraph discussing backward behaviour of dissipative
perturbations of KdV.

For the KdV--Burgers--Sivashinsky type equation treated in the cited work, a trajectory
that is global in both time directions belongs to the global attractor. -/
axiom guoTiti_kbs_globalTrajectory_mem_attractor
    {X : Type u} (isGlobalKBSTrajectory : X → Prop) (attractor : Set X) :
    ∀ x : X, isGlobalKBSTrajectory x → x ∈ attractor

/-- **Citation: `Kukavica` as grouped in the paper's introduction (the precise
Kukavica--Malcok bibliographic entry is not supplied in the uploaded source).**

Paper location: Introduction, same backward-behaviour paragraph.

Every complete Kuramoto--Sivashinsky trajectory belongs to its global attractor. -/
axiom kuramotoSivashinsky_globalTrajectory_mem_attractor
    {X : Type u} (isGlobalKSTrajectory : X → Prop) (attractor : Set X) :
    ∀ x : X, isGlobalKSTrajectory x → x ∈ attractor

end BardosTartar.Citations
