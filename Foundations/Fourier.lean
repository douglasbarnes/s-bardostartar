import Foundations.Torus
import Mathlib.Data.Finsupp.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Algebra.Module.ClosedSubmodule
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.RestrictScalars
import Mathlib.Tactic

/-!
# Fourier coefficients and divergence-free trigonometric polynomials

The coefficient model is primary for later finite-dimensional arguments.  Generic analytic
infrastructure is delegated to Mathlib wherever available: `ℓ²` provides completion,
`UnitAddTorus.mFourierLp` / `mFourierBasis` provide scalar torus Fourier analysis and Parseval,
`PiLp 2` provides the two-component `L²` velocity space, and Mathlib's Hilbert-sum construction
provides Fourier synthesis.  The project-specific layer contains only the divergence-free
direction, the zero/reality constraints, and the homogeneous `H¹` weight.

The finite pointwise interpretation remains explicit through `TrigPoly.eval`.  Because the basis
already points in the `kᗮ` direction, mean-zero and incompressibility reduce to the zero-mode
condition; realness is exactly the paper relation `μₖ = -conj(μ₋ₖ)`.
-/

namespace BardosTartar

noncomputable section

open Complex
open MeasureTheory
open scoped ComplexConjugate ENNReal lp BigOperators

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
  apply Prod.ext <;> simp [phi, vecConj, waveNorm_neg] <;> ring

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


/-! ## Completed phase spaces and the torus Fourier bridge -/

/-- Ambient complex Hilbert space of square-summable coefficients on nonzero modes. -/
abbrev HCoeffL2 := ℓ²(NonzeroMode, ℂ)

/-- Negation preserves the nonzero-mode index set. -/
def negMode (k : NonzeroMode) : NonzeroMode := ⟨-k.1, by simpa using k.2⟩

@[simp] theorem negMode_val (k : NonzeroMode) : (negMode k).1 = -k.1 := rfl

@[simp] theorem negMode_negMode (k : NonzeroMode) : negMode (negMode k) = k := by
  apply Subtype.ext
  simp [negMode]

/-- Coordinate evaluation on `ℓ²`, viewed as a continuous real-linear map. -/
def coeffEvalReal (k : NonzeroMode) : HCoeffL2 →L[ℝ] ℂ where
  toFun := fun a => a k
  map_add' := by intro a b; rfl
  map_smul' := by intro r a; rfl
  cont := (lp.lipschitzWith_one_eval
    (E := fun _ : NonzeroMode => ℂ) (p := (2 : ℝ≥0∞)) k).continuous

@[simp] theorem coeffEvalReal_apply (k : NonzeroMode) (a : HCoeffL2) :
    coeffEvalReal k a = a k := rfl

/-- Complex conjugation, bundled as a real continuous-linear map. -/
def conjRealCLM : ℂ →L[ℝ] ℂ :=
  LinearMap.mkContinuous
    { toFun := conj
      map_add' := by intro z w; simp
      map_smul' := by intro r z; simp }
    1
    (fun z => by simp)

@[simp] theorem conjRealCLM_apply (z : ℂ) : conjRealCLM z = conj z := rfl

/-- Real-linear defect measuring `μ_{-k} + conj μ_k`. -/
def realityDefect (k : NonzeroMode) : HCoeffL2 →L[ℝ] ℂ :=
  coeffEvalReal (negMode k) + conjRealCLM.comp (coeffEvalReal k)

@[simp] theorem realityDefect_apply (k : NonzeroMode) (a : HCoeffL2) :
    realityDefect k a = a (negMode k) + conj (a k) := by
  rfl

/-- Closed real subspace imposing the paper's reality condition. -/
def HClosed : ClosedSubmodule ℝ HCoeffL2 :=
  ⨅ k : NonzeroMode, ClosedSubmodule.comap (realityDefect k) ⊥

/-- The same space as an ordinary submodule, so standard subtype norm/module instances apply. -/
def HSubmodule : Submodule ℝ HCoeffL2 := HClosed.toSubmodule

/-- Paper Appendix §Notation: completed energy Hilbert space `H`. -/
abbrev H : Type := ↥HSubmodule

instance : CompleteSpace H := by
  apply IsComplete.completeSpace_coe
  change IsComplete (HSubmodule : Set HCoeffL2)
  simpa [HSubmodule] using HClosed.isClosed.isComplete

theorem mem_HClosed_iff (a : HCoeffL2) :
    a ∈ HClosed ↔ ∀ k : NonzeroMode, a (negMode k) = -conj (a k) := by
  simp [HClosed, realityDefect_apply, add_eq_zero_iff_eq_neg]

theorem mem_HSubmodule_iff (a : HCoeffL2) :
    a ∈ HSubmodule ↔ ∀ k : NonzeroMode, a (negMode k) = -conj (a k) := by
  simpa [HSubmodule] using mem_HClosed_iff a

namespace H

/-- Nonzero Fourier coefficient of an element of completed `H`. -/
def coeffNZ (u : H) (k : NonzeroMode) : ℂ := (u : HCoeffL2) k

/-- Fourier coefficient on all of `ℤ²`, with the mean mode set to zero. -/
def coeff (u : H) (k : WaveVec) : ℂ :=
  if hk : k = 0 then 0 else u.coeffNZ ⟨k, hk⟩

@[simp] theorem coeff_zero (u : H) : u.coeff 0 = 0 := by
  simp [coeff]

@[simp] theorem coeff_nonzero (u : H) (k : NonzeroMode) :
    u.coeff k.1 = u.coeffNZ k := by
  rw [coeff]
  simp only [dif_neg k.2]

/-- Paper coefficient reality condition on the completed phase space. -/
theorem coeff_neg (u : H) (k : WaveVec) :
    u.coeff (-k) = -conj (u.coeff k) := by
  by_cases hk : k = 0
  · subst k
    simp [coeff]
  · have hnk : -k ≠ 0 := by simpa using hk
    have hu := (mem_HSubmodule_iff (u : HCoeffL2)).mp u.2 ⟨k, hk⟩
    rw [coeff, coeff]
    simp only [dif_neg hnk, dif_neg hk]
    unfold coeffNZ
    simpa [negMode] using hu

/-- Parseval identity for the completed energy norm. -/
theorem norm_sq_eq_tsum (u : H) :
    ‖u‖ ^ 2 = ∑' k : NonzeroMode, ‖u.coeffNZ k‖ ^ 2 := by
  change ‖(u : HCoeffL2)‖ ^ 2 = ∑' k : NonzeroMode, ‖(u : HCoeffL2) k‖ ^ 2
  simpa using
    (lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num) (u : HCoeffL2))

end H

/-- Paper Appendix §Notation: homogeneous `H¹` domain `V`, expressed by weighted Fourier
square-summability. -/
def V : Set H :=
  {u | Summable fun k : NonzeroMode => sqNorm k.1 * ‖u.coeffNZ k‖ ^ 2}

/-- Squared homogeneous `H¹` norm / enstrophy. -/
def enstrophySqH (u : H) : ℝ :=
  ∑' k : NonzeroMode, sqNorm k.1 * ‖u.coeffNZ k‖ ^ 2

/-- Homogeneous `H¹` norm on the completed coefficient space. -/
def enstrophyNormH (u : H) : ℝ := Real.sqrt (enstrophySqH u)

theorem enstrophySqH_nonneg (u : H) : 0 ≤ enstrophySqH u := by
  unfold enstrophySqH
  apply tsum_nonneg
  intro k
  exact mul_nonneg (sqNorm_nonneg k.1) (sq_nonneg _)

theorem enstrophyNormH_sq (u : H) :
    enstrophyNormH u ^ 2 = enstrophySqH u := by
  exact Real.sq_sqrt (enstrophySqH_nonneg u)

/-- A finitely-supported complex family canonically belongs to `ℓ²`. -/
def finsuppToL2 {ι : Type*} (f : ι →₀ ℂ) : ℓ²(ι, ℂ) :=
  ⟨(fun i => f i), by
    apply memℓp_gen
    apply summable_of_ne_finset_zero (s := f.support)
    intro i hi
    have hfi : f i = 0 := by
      simpa [Finsupp.mem_support_iff] using hi
    simp [hfi]⟩

@[simp] theorem finsuppToL2_apply {ι : Type*} (f : ι →₀ ℂ) (i : ι) :
    finsuppToL2 f i = f i := rfl

namespace TrigPoly

/-- Restriction of trigonometric-polynomial coefficients to nonzero modes. -/
def nonzeroCoeff (u : TrigPoly) : NonzeroMode →₀ ℂ :=
  u.coeff.subtypeDomain (fun k : WaveVec => k ≠ 0)

@[simp] theorem nonzeroCoeff_apply (u : TrigPoly) (k : NonzeroMode) :
    u.nonzeroCoeff k = u.fourierCoeff k.1 := by
  simp [nonzeroCoeff, fourierCoeff]

/-- Canonical inclusion of paper trigonometric polynomials into completed `H`. -/
def toH (u : TrigPoly) : H := by
  refine ⟨finsuppToL2 u.nonzeroCoeff, ?_⟩
  rw [mem_HSubmodule_iff]
  intro k
  simp only [finsuppToL2_apply]
  rw [nonzeroCoeff_apply, nonzeroCoeff_apply]
  simpa [negMode] using u.reality k.1

@[simp] theorem toH_coeffNZ (u : TrigPoly) (k : NonzeroMode) :
    u.toH.coeffNZ k = u.fourierCoeff k.1 := by
  simp [H.coeffNZ, toH, nonzeroCoeff, fourierCoeff]

@[simp] theorem toH_coeff (u : TrigPoly) (k : WaveVec) :
    u.toH.coeff k = u.fourierCoeff k := by
  by_cases hk : k = 0
  · subst k
    simp
  · rw [H.coeff]
    simp only [dif_neg hk]
    rw [toH_coeffNZ]

/-- Trigonometric polynomials belong to the completed homogeneous `H¹` domain. -/
theorem toH_mem_V (u : TrigPoly) : u.toH ∈ V := by
  change Summable (fun k : NonzeroMode => sqNorm k.1 * ‖u.toH.coeffNZ k‖ ^ 2)
  apply summable_of_ne_finset_zero (s := u.nonzeroCoeff.support)
  intro k hk
  have hcoeff : u.nonzeroCoeff k = 0 := by
    simpa [Finsupp.mem_support_iff] using hk
  have hzero : u.fourierCoeff k.1 = 0 := by
    simpa using hcoeff
  simp [toH_coeffNZ, hzero]

/-- Actual completed-space Parseval theorem for trigonometric polynomials. -/
theorem norm_toH_sq_eq_energySq (u : TrigPoly) :
    ‖u.toH‖ ^ 2 = u.energySq := by
  rw [H.norm_sq_eq_tsum]
  simp_rw [toH_coeffNZ, ← nonzeroCoeff_apply]
  rw [tsum_eq_sum (s := u.nonzeroCoeff.support) (fun k hk => by
    have hzero : u.nonzeroCoeff k = 0 := by
      simpa [Finsupp.mem_support_iff] using hk
    simp [hzero])]
  unfold energySq
  change
    u.nonzeroCoeff.sum (fun (_ : NonzeroMode) (μ : ℂ) => ‖μ‖ ^ 2) =
      u.coeff.sum (fun (_ : WaveVec) (μ : ℂ) => ‖μ‖ ^ 2)
  have hsupport : ∀ k ∈ u.coeff.support, k ≠ 0 := by
    intro k hk
    exact mem_support_ne_zero (u := u) hk
  simpa [nonzeroCoeff] using
    (Finsupp.sum_subtypeDomain_index
      (v := u.coeff) (p := fun k : WaveVec => k ≠ 0)
      (h := fun (_ : WaveVec) (μ : ℂ) => ‖μ‖ ^ 2) hsupport)

/-- Actual homogeneous `H¹` Parseval theorem on the completed phase-space model. -/
theorem enstrophySqH_toH_eq (u : TrigPoly) :
    enstrophySqH u.toH = u.enstrophySq := by
  unfold enstrophySqH
  simp_rw [toH_coeffNZ, ← nonzeroCoeff_apply]
  rw [tsum_eq_sum (s := u.nonzeroCoeff.support) (fun k hk => by
    have hzero : u.nonzeroCoeff k = 0 := by
      simpa [Finsupp.mem_support_iff] using hk
    simp [hzero])]
  unfold enstrophySq
  change
    u.nonzeroCoeff.sum (fun (k : NonzeroMode) (μ : ℂ) => sqNorm k.1 * ‖μ‖ ^ 2) =
      u.coeff.sum (fun (k : WaveVec) (μ : ℂ) => sqNorm k * ‖μ‖ ^ 2)
  have hsupport : ∀ k ∈ u.coeff.support, k ≠ 0 := by
    intro k hk
    exact mem_support_ne_zero (u := u) hk
  simpa [nonzeroCoeff] using
    (Finsupp.sum_subtypeDomain_index
      (v := u.coeff) (p := fun k : WaveVec => k ≠ 0)
      (h := fun (k : WaveVec) (μ : ℂ) => sqNorm k * ‖μ‖ ^ 2) hsupport)

end TrigPoly

/-! ### Concrete torus realization delegated to Mathlib's scalar Fourier `L²` theory -/

/-- Use exactly the probability-Haar measure-space instance chosen internally by Mathlib's
`UnitAddTorus.mFourierLp` / `mFourierBasis`.  This makes the project aliases definitionally share
Mathlib's scalar Fourier `L²` space rather than transporting between equal measures. -/
local instance mathlibUnitCircleMeasureSpace : MeasureSpace UnitAddCircle :=
  ⟨AddCircle.haarAddCircle⟩


/-- Scalar `L²` on the repository torus.  Mathlib's `UnitAddTorus.mFourierBasis` is a Hilbert
basis of this space, with `repr` equal to the actual torus Fourier coefficients.  The local
measure instance above is intentionally identical to Mathlib's own Fourier-file normalization. -/
abbrev ScalarTorusL2 :=
  MeasureTheory.Lp ℂ 2 (volume : Measure Torus2)

/-- Two-component velocity `L²`, represented as the finite `L²` product of two scalar torus
`L²` spaces.  This delegates the normed/Hilbert-space product construction to `PiLp`. -/
abbrev TorusVectorL2 :=
  PiLp 2 (fun _ : SpatialIndex => ScalarTorusL2)

/-- Mathlib's scalar Fourier mode, with the repository's pair-valued wave-vector index. -/
def scalarModeL2 (k : WaveVec) : ScalarTorusL2 :=
  UnitAddTorus.mFourierLp (d := SpatialIndex) 2 (waveIndex k)

/-- Unit divergence-free direction `k⊥ / |k|`, living only in the finite Euclidean coefficient
space.  All infinite-dimensional Fourier analysis is delegated to Mathlib. -/
def modeDirection (k : NonzeroMode) : EuclideanSpace ℂ SpatialIndex :=
  !₂[
    (-(k.1.2 : ℂ)) / (waveNorm k.1 : ℂ),
    ((k.1.1 : ℂ)) / (waveNorm k.1 : ℂ)
  ]

theorem modeDirection_norm_sq (k : NonzeroMode) :
    ‖modeDirection k‖ ^ 2 = 1 := by
  rw [EuclideanSpace.norm_sq_eq]
  simp only [Fin.sum_univ_two]
  simp [modeDirection]
  have hw := waveNorm_sq k.1
  have hn := waveNorm_ne_zero k.2
  field_simp [hn]
  norm_num [sqNorm, sqNormZ, dotZ] at hw ⊢
  nlinarith

@[simp] theorem modeDirection_norm (k : NonzeroMode) :
    ‖modeDirection k‖ = 1 := by
  have h := modeDirection_norm_sq k
  nlinarith [norm_nonneg (modeDirection k)]

/-- The paper's normalized divergence-free Fourier mode, assembled componentwise from Mathlib's
already-normalized scalar torus Fourier mode. -/
def divergenceFreeModeL2 (k : NonzeroMode) : TorusVectorL2 :=
  !₂[
    (modeDirection k 0) • scalarModeL2 k.1,
    (modeDirection k 1) • scalarModeL2 k.1
  ]

/-- Inner product of two divergence-free modes factors into Mathlib's scalar Fourier inner
product and the finite-dimensional direction inner product. -/
theorem inner_divergenceFreeModeL2 (k l : NonzeroMode) :
    inner ℂ (divergenceFreeModeL2 k) (divergenceFreeModeL2 l) =
      inner ℂ (scalarModeL2 k.1) (scalarModeL2 l.1) *
        inner ℂ (modeDirection k) (modeDirection l) := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [Fin.sum_univ_two]
  simp [divergenceFreeModeL2, scalarModeL2, inner_smul_left, inner_smul_right]
  ring

/-- The normalized divergence-free Fourier modes are orthonormal.  The infinite-dimensional
orthogonality is exactly Mathlib's `UnitAddTorus.orthonormal_mFourier`; only the two-dimensional
coefficient normalization remains project-specific. -/
theorem orthonormal_divergenceFreeModeL2 :
    Orthonormal ℂ divergenceFreeModeL2 := by
  rw [orthonormal_iff_ite]
  intro k l
  rw [inner_divergenceFreeModeL2]
  have hs :=
    (orthonormal_iff_ite.mp orthonormal_monomial) k.1 l.1
  by_cases hkl : k = l
  · subst l
    have hs' : inner ℂ (scalarModeL2 k.1) (scalarModeL2 k.1) = 1 := by
      simpa [scalarModeL2] using hs
    rw [hs']
    simp [inner_self_eq_norm_sq_to_K, modeDirection_norm]
  · have hval : k.1 ≠ l.1 := by
      intro h
      exact hkl (Subtype.ext h)
    have hs' : inner ℂ (scalarModeL2 k.1) (scalarModeL2 l.1) = 0 := by
      simpa [scalarModeL2, hval] using hs
    rw [hs']
    simp [hkl]

/-- Fourier synthesis from square-summable scalar divergence-free coefficients into the actual
two-component torus `L²` space.  Mathlib's Hilbert-sum construction supplies convergence,
linearity and isometry. -/
def complexFourierRealization : HCoeffL2 →ₗᵢ[ℂ] TorusVectorL2 :=
  orthonormal_divergenceFreeModeL2.orthogonalFamily.linearIsometry

/-- Real-linear isometric realization of completed paper `H` in torus `L²`; scalar restriction is
delegated to Mathlib. -/
def fourierToTorus : H →ₗᵢ[ℝ] TorusVectorL2 where
  toLinearMap :=
    (complexFourierRealization.toLinearMap.restrictScalars ℝ).comp HSubmodule.subtype
  norm_map' u := complexFourierRealization.norm_map (u : HCoeffL2)

/-- Closed torus range of the completed paper phase space. -/
def TorusHClosed : ClosedSubmodule ℝ TorusVectorL2 where
  toSubmodule := LinearMap.range fourierToTorus.toLinearMap
  isClosed' := fourierToTorus.isometry.isUniformInducing.isComplete_range.isClosed

/-- Ordinary submodule underlying the concrete torus phase space. -/
def TorusHSubmodule : Submodule ℝ TorusVectorL2 := TorusHClosed.toSubmodule

/-- Concrete torus realization of paper `H`. -/
abbrev TorusH : Type := ↥TorusHSubmodule

instance : CompleteSpace TorusH := by
  apply IsComplete.completeSpace_coe
  change IsComplete (TorusHSubmodule : Set TorusVectorL2)
  simpa [TorusHSubmodule] using TorusHClosed.isClosed.isComplete

/-- Isometric embedding from coefficient `H` to its torus range. -/
def fourierBridgeIsometry : H →ₗᵢ[ℝ] TorusH where
  toFun u := ⟨fourierToTorus u, by
    change fourierToTorus u ∈ TorusHClosed
    exact ⟨u, rfl⟩⟩
  map_add' u v := by
    apply Subtype.ext
    exact fourierToTorus.map_add u v
  map_smul' r u := by
    apply Subtype.ext
    exact fourierToTorus.map_smul r u
  norm_map' u := by
    change ‖fourierToTorus u‖ = ‖u‖
    exact fourierToTorus.norm_map u

/-- Explicit real-linear isometric Fourier equivalence between completed scalar coefficients and
the concrete divergence-free torus `L²` range. -/
def fourierBridge : H ≃ₗᵢ[ℝ] TorusH :=
  LinearIsometryEquiv.ofSurjective (σ₁₂ := RingHom.id ℝ) fourierBridgeIsometry (by
    intro y
    have hy : (y : TorusVectorL2) ∈ TorusHClosed := by
      simpa [TorusHSubmodule] using y.2
    rcases hy with ⟨u, hu⟩
    refine ⟨u, ?_⟩
    apply Subtype.ext
    exact hu)

/-- Transported homogeneous `H¹` domain on the concrete torus phase space. -/
def TorusV : Set TorusH := {u | fourierBridge.symm u ∈ V}

/-- Homogeneous `H¹` norm transported through the Fourier isometry. -/
def torusEnstrophyNorm (u : TorusH) : ℝ :=
  enstrophyNormH (fourierBridge.symm u)

namespace TrigPoly

/-- Canonical concrete torus `L²` realization of a trigonometric polynomial. -/
def toTorusH (u : TrigPoly) : TorusH := fourierBridge u.toH

/-- Actual `L²` Parseval identity for the concrete torus realization. -/
theorem norm_toTorusH_sq_eq_energySq (u : TrigPoly) :
    ‖u.toTorusH‖ ^ 2 = u.energySq := by
  simpa [toTorusH] using norm_toH_sq_eq_energySq u

/-- The concrete trigonometric polynomial lies in the transported `H¹` domain. -/
theorem toTorusH_mem_TorusV (u : TrigPoly) :
    u.toTorusH ∈ TorusV := by
  simpa [toTorusH, TorusV] using u.toH_mem_V

/-- Actual homogeneous `H¹` Parseval identity on the concrete torus realization. -/
theorem torusEnstrophyNorm_sq_toTorusH (u : TrigPoly) :
    torusEnstrophyNorm u.toTorusH ^ 2 = u.enstrophySq := by
  rw [torusEnstrophyNorm, enstrophyNormH_sq]
  simpa [toTorusH] using enstrophySqH_toH_eq u

end TrigPoly

end

end BardosTartar
