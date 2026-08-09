import Mathlib
import Mathlib.Topology.MetricSpace.HausdorffDimension

/-!
# Cited mathematical background from the introduction

These statements are not used in the two headline proofs.  Because the uploaded source
does not supply `references.bib`, theorem numbers, or the concrete KdV/KS phase-space
APIs, this file records the mathematical propositions named in the introduction without
asserting unsafe axioms over arbitrary predicates or arbitrary attractor sets.
-/

namespace BardosTartar.Citations

universe u

/-- A solution relation admits a trajectory through the prescribed time-zero state. -/
def HasGlobalTrajectoryThrough {X : Type u}
    (isSolution : (ℝ → X) → Prop) (x0 : X) : Prop :=
  ∃ u : ℝ → X, isSolution u ∧ u 0 = x0

/-- **Citation statement: `attractor`, `attractor2` (the paper supplies no theorem
numbers).**

Paper location: Introduction, paragraph following the Bardos--Tartar conjecture.

The concrete global attractor of the 2D periodic NSE has finite Hausdorff dimension in
the `L²` metric.  `A` is a placeholder only for recording the proposition's shape; no
assertion is made for arbitrary sets. -/
def nse_globalAttractor_finiteHausdorffDimension_statement
    {H : Type u} [EMetricSpace H] (A : Set H) : Prop :=
  dimH A < ⊤

/-- **Citation statement: `Bourgain`, `BabinIlyinTiti` (no theorem number supplied at
the paper use-site).**

Paper location: Introduction, paragraph discussing backward behaviour of other
parabolic/dispersive equations.

The periodic KdV flow is globally extendable.  The solution predicate remains an adapter
parameter until a concrete KdV formalization is supplied; this proposition is not
asserted for arbitrary predicates. -/
def periodicKdV_globalExtendability_statement
    {X : Type u} (isKdVSolution : (ℝ → X) → Prop) : Prop :=
  ∀ x0 : X, HasGlobalTrajectoryThrough isKdVSolution x0

/-- **Citation statement: `GuoTiti`, Theorem 1.1(ii).**

Paper location: Introduction, paragraph discussing backward behaviour of dissipative
perturbations of KdV.

Guo--Titi Theorem 1.1(ii) states, for the dissipative KdV--Burgers--Sivashinsky case,
that a solution outside the global attractor cannot be extended globally backward in
time.  Equivalently, every complete trajectory lies in the global attractor.  The
concrete KBS phase space is not part of this project, so this remains a typed background
statement rather than an axiom over an arbitrary model. -/
def guoTiti_kbs_globalTrajectory_mem_attractor_statement
    {X : Type u} (isGlobalKBSTrajectory : X → Prop) (attractor : Set X) : Prop :=
  ∀ x : X, isGlobalKBSTrajectory x → x ∈ attractor

/-- **Citation statement: `Kukavica` as grouped in the paper's introduction (the exact
bibliographic mapping is not supplied in the uploaded source).**

Paper location: Introduction, same backward-behaviour paragraph.

Every complete Kuramoto--Sivashinsky trajectory belongs to its global attractor. -/
def kuramotoSivashinsky_globalTrajectory_mem_attractor_statement
    {X : Type u} (isGlobalKSTrajectory : X → Prop) (attractor : Set X) : Prop :=
  ∀ x : X, isGlobalKSTrajectory x → x ∈ attractor

end BardosTartar.Citations
