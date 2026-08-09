import Mathlib

/-!
# Citation interfaces

Representation-neutral vocabulary used only to state results imported by the paper from
external literature.  The concrete Fourier/Navier--Stokes model is supplied by the
foundation layers; these definitions deliberately do not introduce a competing model.
-/

namespace BardosTartar.Citations

universe u

/-- Data named in the paper's abstract weak-density statement.  The two norm-valued
functions are kept explicit so that a later adapter can identify them with the project's
`L²` and `H¹` norms without imposing a second function-space representation here. -/
structure DynamicsData (H : Type u) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  S : ℝ → H → H
  V : Set H
  P : ℕ → H →L[ℝ] H
  Q : ℕ → H →L[ℝ] H
  lambda : ℕ → ℝ
  energyNorm : H → ℝ
  enstrophyNorm : H → ℝ
  E1 : ℝ
  E2 : ℝ
  E3 : ℝ
  E4 : ℝ

/-- The paper's Dirichlet quotient `Φ(u)=‖u‖²/|u|²`. -/
noncomputable def dirichletQuotient {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) (u : H) : ℝ :=
  d.enstrophyNorm u ^ 2 / d.energyNorm u ^ 2

/-- `\tilde λ_n=(λ_n+λ_{n+1})/2` from the paper. -/
noncomputable def midLambda {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) (n : ℕ) : ℝ :=
  (d.lambda n + d.lambda (n + 1)) / 2

/-- `γ_n=(λ_{n+1}+λ_n)/(λ_{n+1}-λ_n)` from the paper. -/
noncomputable def spectralGamma {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) (n : ℕ) : ℝ :=
  (d.lambda (n + 1) + d.lambda n) / (d.lambda (n + 1) - d.lambda n)

/-- A complete trajectory for the forward solution operators. -/
def IsCompleteOrbit {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) (u : ℝ → H) : Prop :=
  ∀ s t : ℝ, 0 ≤ t → d.S t (u s) = u (s + t)

/-- Representation-neutral form of global backward extendability. -/
def GloballyExtendable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) (u0 : H) : Prop :=
  ∃ u : ℝ → H, IsCompleteOrbit d u ∧ u 0 = u0

/-- Operational form of `limsup_{t→-∞} f(t) ≤ L`, avoiding a commitment to a
particular filter API in downstream files. -/
def LimsupAtBotLE (f : ℝ → ℝ) (L : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, t < T → f t ≤ L + ε

/-- The tail bound appearing in the paper's CFKM-derived weak-density theorem. -/
noncomputable def paperTailBound {H : Type u} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (d : DynamicsData H) (n : ℕ) (v : H) : ℝ :=
  max d.E1 (max d.E2 (max d.E3 (max d.E4
    (spectralGamma d n * d.energyNorm v ^ 2))))

end BardosTartar.Citations
