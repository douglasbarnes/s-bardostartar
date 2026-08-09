import Foundations.Torus
import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic

/-!
# Fourier coefficients and divergence-free trigonometric polynomials

The coefficient model is primary for later finite-dimensional arguments.  Its interpretation as a
function on the torus is kept explicit through `TrigPoly.eval`.  Because the basis already points
in the `kᗮ` direction, mean-zero and incompressibility reduce to the zero-mode condition; realness
is exactly the paper relation `μₖ = -conj(μ₋ₖ)`.
-/

namespace BardosTartar

noncomputable section

open Complex
open scoped ComplexConjugate ENNReal

/-- Componentwise complex conjugation on complexified planar vectors. -/
def vecConj (v : CVec2) : CVec2 := (conj v.1, conj v.2)

/-- Paper §2, Fourier notation display following the definition of `D_k`: the
repository-normalised divergence-free Fourier basis.

This is the total extension (with value `0` at the zero mode) of the paper direction after
pulling back to the unit torus and multiplying physical velocity by `2π`:
`ψₖ(y) = (kᗮ/|k|) exp(2π i k·y)`.  The paper only indexes its `φ_ℓ` by nonzero modes.
-/
def phi (k : WaveVec) (x : Torus2) : CVec2 :=
  (((-(k.2 : ℂ)) / (waveNorm k : ℂ)) * monomial k x,
   (((k.1 : ℂ)) / (waveNorm k : ℂ)) * monomial k x)

/-- Componentwise complex bilinear dot product. -/
def cdot (v w : CVec2) : ℂ := v.1 * w.1 + v.2 * w.2

/-- A wave vector regarded as a complex planar vector. -/
def modeC (k : WaveVec) : CVec2 := ((k.1 : ℂ), (k.2 : ℂ))

/-- Paper Appendix equation `trigpoly`: every basis mode is transverse to its wave vector, the
coefficient-level form of incompressibility. -/
theorem modeC_cdot_phi (k : WaveVec) (x : Torus2) : cdot (modeC k) (phi k x) = 0 := by
  simp [cdot, modeC, phi]
  ring

/-- The total extension of the divergence-free basis vanishes at the zero mode. -/
@[simp] theorem phi_zero (x : Torus2) : phi 0 x = 0 := by
  simp [phi, waveNorm, sqNorm, sqNormZ, dotZ]

/-- The sign in the paper's coefficient reality condition comes from
`φ₋ₖ = -conj(φₖ)`. -/
theorem phi_neg (k : WaveVec) (x : Torus2) : phi (-k) x = -vecConj (phi k x) := by
  apply Prod.ext <;> simp [phi, vecConj, waveNorm_neg]

/-- Paper §2, Fourier notation display: paper-normalised basis on `[0,2π]²`,
`φₖ(x) = kᗮ/(2π |k|) exp(i k·x)`.

The exponential is represented through `paperToUnit`, so no second Fourier convention is created.
-/
def paperPhi (k : WaveVec) (x : PaperPoint) : CVec2 :=
  (((paperPeriod : ℂ)⁻¹) * (phi k (paperToUnit x)).1,
   ((paperPeriod : ℂ)⁻¹) * (phi k (paperToUnit x)).2)

/-- The repository and paper basis differ exactly by the displayed `2π` scaling. -/
theorem paperPhi_eq_inv_period_mul (k : WaveVec) (x : PaperPoint) :
    paperPhi k x =
      (((paperPeriod : ℂ)⁻¹) * (phi k (paperToUnit x)).1,
       ((paperPeriod : ℂ)⁻¹) * (phi k (paperToUnit x)).2) := rfl

/-- Fourier monomials indexed by pair-valued modes remain orthonormal in Mathlib's scalar `L²`
space.  This is the scalar orthogonality input behind the vector-valued Parseval identities. -/
theorem orthonormal_monomial :
    Orthonormal ℂ
      (fun k : WaveVec => UnitAddTorus.mFourierLp (d := SpatialIndex) 2 (waveIndex k)) := by
  rw [orthonormal_iff_ite]
  intro k l
  have h :=
    (orthonormal_iff_ite.mp (UnitAddTorus.orthonormal_mFourier (d := SpatialIndex)))
      (waveIndex k) (waveIndex l)
  by_cases hkl : k = l
  · subst l
    simpa using h
  · have hidx : waveIndex k ≠ waveIndex l := fun h' => hkl (waveIndex_injective h')
    simpa [hkl, hidx] using h

/-- Fourier coefficient of a scalar torus function, using Mathlib's probability-Haar
multidimensional Fourier convention and the repository pair-valued wave index. -/
def scalarFourierCoeff (f : Torus2 → ℂ) (k : WaveVec) : ℂ :=
  UnitAddTorus.mFourierCoeff f (waveIndex k)

/-- Fourier coefficient of a complex planar torus field, componentwise through Mathlib's
vector-valued multidimensional Fourier coefficient. -/
def vectorFourierCoeff (f : Torus2 → CVec2) (k : WaveVec) : CVec2 :=
  UnitAddTorus.mFourierCoeff f (waveIndex k)

/-- Finitely supported scalar coefficients in the normalised divergence-free basis. -/
abbrev FourierCoeff := WaveVec →₀ ℂ

/-- Paper Appendix, equation `trigpoly`, expressed in the divergence-free scalar basis: a
finitely supported coefficient family with zero mean mode and the paper reality condition
`μ₋ₖ = -conj μₖ`.  The explicit function-space realization is `TrigPoly.eval`.
-/
structure TrigPoly where
  coeff : FourierCoeff
  mean_zero : coeff 0 = 0
  reality : ∀ k : WaveVec, coeff (-k) = -conj (coeff k)

namespace TrigPoly

/-- Paper §2 Fourier notation: coefficient `μₖ` of a trigonometric polynomial in the
normalised divergence-free basis. -/
def fourierCoeff (u : TrigPoly) (k : WaveVec) : ℂ := u.coeff k

@[simp] theorem fourierCoeff_zero (u : TrigPoly) : u.fourierCoeff 0 = 0 := u.mean_zero

@[simp] theorem fourierCoeff_neg (u : TrigPoly) (k : WaveVec) :
    u.fourierCoeff (-k) = -conj (u.fourierCoeff k) := u.reality k

/-- Paper Appendix equation `trigpoly`: explicit function-space interpretation of the finite
coefficient model on the repository unit torus. -/
def eval (u : TrigPoly) (x : Torus2) : CVec2 :=
  u.coeff.sum fun k μ => μ • phi k x

/-- Paper Appendix equation `trigpoly`: explicit interpretation in the paper's
`[0,2π]²` normalisation. -/
def evalPaper (u : TrigPoly) (x : PaperPoint) : CVec2 :=
  u.coeff.sum fun k μ => μ • paperPhi k x

/-- Finite Fourier support. -/
def support (u : TrigPoly) : Finset WaveVec := u.coeff.support

@[simp] theorem not_mem_support_iff (u : TrigPoly) (k : WaveVec) :
    k ∉ u.support ↔ u.fourierCoeff k = 0 := by
  simp [support, fourierCoeff]

/-- The zero mode never occurs in the support of a mean-zero trigonometric polynomial. -/
theorem mem_support_ne_zero {u : TrigPoly} {k : WaveVec} (hk : k ∈ u.support) : k ≠ 0 := by
  intro hk0
  subst k
  exact ((not_mem_support_iff u 0).2 u.fourierCoeff_zero) hk

/-- Paper §2 coefficient Parseval display: coefficient form of the energy `|u|²`.  With the
paper-normalised basis this is exactly
`∑ |μₖ|²`; the scalar orthogonality theorem above is the analytic Parseval input. -/
def energySq (u : TrigPoly) : ℝ :=
  u.coeff.sum fun _ μ => ‖μ‖ ^ 2

/-- Paper §2 coefficient Parseval display: coefficient form of the homogeneous `H¹` norm /
enstrophy `‖u‖²`. -/
def enstrophySq (u : TrigPoly) : ℝ :=
  u.coeff.sum fun k μ => sqNorm k * ‖μ‖ ^ 2

/-- Paper §2 coefficient Parseval display: Parseval identity for energy in the finite coefficient
model. -/
theorem energySq_eq_sum (u : TrigPoly) :
    u.energySq = ∑ k ∈ u.support, ‖u.fourierCoeff k‖ ^ 2 := by
  rfl

/-- Paper §2 coefficient Parseval display: Parseval identity for enstrophy / homogeneous `H¹`. -/
theorem enstrophySq_eq_sum (u : TrigPoly) :
    u.enstrophySq = ∑ k ∈ u.support, sqNorm k * ‖u.fourierCoeff k‖ ^ 2 := by
  rfl

end TrigPoly

end

end BardosTartar
