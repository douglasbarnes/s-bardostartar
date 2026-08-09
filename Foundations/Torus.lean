import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Two-dimensional periodic Fourier conventions

This file fixes the geometric conventions used by the Bardos--Tartar formalisation.
The repository model is Mathlib's unit additive two-torus.  A paper coordinate
`x ∈ [0,2π]²` is sent to the unit torus by `x ↦ x/(2π)` coordinatewise.  Thus
Mathlib's monomial `exp(2π i k·y)` pulls back to the paper monomial `exp(i k·x)`.

The paper uses unnormalised Lebesgue measure on `[0,2π]²`.  The repository uses
probability Haar measure on the unit torus and compensates for this by using the
unit-length divergence-free direction `kᗮ/|k|`; the paper basis is obtained by
multiplying the pulled-back basis by `(2π)⁻¹`.
-/

namespace BardosTartar

noncomputable section

open Complex
open scoped ComplexConjugate ENNReal

/-- Spatial coordinate index in dimension two. -/
abbrev SpatialIndex := Fin 2

/-- Repository torus: Mathlib's probability-normalised two-dimensional unit additive torus. -/
abbrev Torus2 := UnitAddTorus SpatialIndex

/-- Paper Appendix equation `trigpoly`: integer Fourier wave vector, with components `(k₁,k₂)`. -/
abbrev WaveVec := ℤ × ℤ

/-- Complexified two-dimensional vector. -/
abbrev CVec2 := ℂ × ℂ

/-- Real paper coordinate on the universal cover. -/
abbrev PaperPoint := ℝ × ℝ

/-- Paper Appendix §Notation (`prelim`): the physical period `2π`. -/
def paperPeriod : ℝ := 2 * Real.pi

@[simp] theorem paperPeriod_pos : 0 < paperPeriod := by
  unfold paperPeriod
  positivity

@[simp] theorem paperPeriod_ne_zero : paperPeriod ≠ 0 := ne_of_gt paperPeriod_pos

/-- Convert a pair-valued wave vector to Mathlib's `Fin 2 → ℤ` multi-index. -/
def waveIndex (k : WaveVec) : SpatialIndex → ℤ := ![k.1, k.2]

@[simp] theorem waveIndex_zero : waveIndex (0 : WaveVec) = 0 := by
  ext i
  fin_cases i <;> simp [waveIndex]

@[simp] theorem waveIndex_neg (k : WaveVec) : waveIndex (-k) = -waveIndex k := by
  ext i
  fin_cases i <;> simp [waveIndex]

@[simp] theorem waveIndex_add (k l : WaveVec) : waveIndex (k + l) = waveIndex k + waveIndex l := by
  ext i
  fin_cases i <;> simp [waveIndex]

@[simp] theorem waveIndex_sub (k l : WaveVec) : waveIndex (k - l) = waveIndex k - waveIndex l := by
  ext i
  fin_cases i <;> simp [waveIndex]

/-- The pair-to-multi-index conversion loses no information. -/
theorem waveIndex_injective : Function.Injective waveIndex := by
  intro k l h
  apply Prod.ext
  · simpa [waveIndex] using congrFun h (0 : SpatialIndex)
  · simpa [waveIndex] using congrFun h (1 : SpatialIndex)

/-- Paper §2 Fourier notation: quarter-turn `kᗮ = (-k₂,k₁)`. -/
def perp (k : WaveVec) : WaveVec := (-k.2, k.1)

@[simp] theorem perp_zero : perp (0 : WaveVec) = 0 := by simp [perp]

@[simp] theorem perp_neg (k : WaveVec) : perp (-k) = -perp k := by
  ext <;> simp [perp]

@[simp] theorem perp_add (k l : WaveVec) : perp (k + l) = perp k + perp l := by
  ext <;> simp [perp, add_comm]

/-- Integer bilinear dot product. -/
def dotZ (k l : WaveVec) : ℤ := k.1 * l.1 + k.2 * l.2

/-- Integer determinant / oriented area. -/
def crossZ (k l : WaveVec) : ℤ := k.1 * l.2 - k.2 * l.1

@[simp] theorem dotZ_comm (k l : WaveVec) : dotZ k l = dotZ l k := by
  simp [dotZ]
  ring

@[simp] theorem crossZ_self (k : WaveVec) : crossZ k k = 0 := by
  simp [crossZ]
  ring

theorem crossZ_swap (k l : WaveVec) : crossZ l k = -crossZ k l := by
  simp [crossZ]
  ring

@[simp] theorem crossZ_neg_neg (k l : WaveVec) : crossZ (-k) (-l) = crossZ k l := by
  simp [crossZ]

@[simp] theorem dotZ_perp_left (k l : WaveVec) : dotZ (perp k) l = crossZ k l := by
  simp [dotZ, perp, crossZ]
  ring

@[simp] theorem dotZ_perp_perp (k l : WaveVec) : dotZ (perp k) (perp l) = dotZ k l := by
  simp [dotZ, perp]
  ring

/-- Squared Euclidean length, still integer-valued. -/
def sqNormZ (k : WaveVec) : ℤ := dotZ k k

/-- Squared Euclidean length as a real number. -/
def sqNorm (k : WaveVec) : ℝ := (sqNormZ k : ℝ)

/-- Euclidean length of a wave vector. -/
def waveNorm (k : WaveVec) : ℝ := Real.sqrt (sqNorm k)

/-- Squared wave-vector length is nonnegative. -/
theorem sqNorm_nonneg (k : WaveVec) : 0 ≤ sqNorm k := by
  norm_num [sqNorm, sqNormZ, dotZ]
  nlinarith [sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ)]

/-- A wave vector has zero squared length exactly when it is the zero mode. -/
theorem sqNorm_eq_zero_iff (k : WaveVec) : sqNorm k = 0 ↔ k = 0 := by
  constructor
  · intro h
    have h' : (k.1 : ℝ) ^ 2 + (k.2 : ℝ) ^ 2 = 0 := by
      norm_num [sqNorm, sqNormZ, dotZ] at h ⊢
      simpa [pow_two] using h
    have h1 : (k.1 : ℝ) = 0 := by
      nlinarith [h', sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ)]
    have h2 : (k.2 : ℝ) = 0 := by
      nlinarith [h', sq_nonneg (k.1 : ℝ), sq_nonneg (k.2 : ℝ)]
    apply Prod.ext
    · exact_mod_cast h1
    · exact_mod_cast h2
  · rintro rfl
    simp [sqNorm, sqNormZ, dotZ]

/-- Nonzero modes have strictly positive Euclidean length. -/
theorem waveNorm_pos {k : WaveVec} (hk : k ≠ 0) : 0 < waveNorm k := by
  apply Real.sqrt_pos.2
  have hnonneg := sqNorm_nonneg k
  have hne : sqNorm k ≠ 0 := fun h => hk ((sqNorm_eq_zero_iff k).mp h)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Nonzero modes have nonzero Euclidean length. -/
theorem waveNorm_ne_zero {k : WaveVec} (hk : k ≠ 0) : waveNorm k ≠ 0 :=
  ne_of_gt (waveNorm_pos hk)

/-- Squaring `waveNorm` recovers the squared length. -/
theorem waveNorm_sq (k : WaveVec) : waveNorm k ^ 2 = sqNorm k := by
  exact Real.sq_sqrt (sqNorm_nonneg k)

@[simp] theorem sqNormZ_neg (k : WaveVec) : sqNormZ (-k) = sqNormZ k := by
  simp [sqNormZ, dotZ]

@[simp] theorem sqNorm_neg (k : WaveVec) : sqNorm (-k) = sqNorm k := by
  simp [sqNorm]

@[simp] theorem waveNorm_neg (k : WaveVec) : waveNorm (-k) = waveNorm k := by
  simp [waveNorm]

@[simp] theorem sqNormZ_perp (k : WaveVec) : sqNormZ (perp k) = sqNormZ k := by
  simp [sqNormZ, dotZ, perp]
  ring

@[simp] theorem sqNorm_perp (k : WaveVec) : sqNorm (perp k) = sqNorm k := by
  simp [sqNorm]

@[simp] theorem waveNorm_perp (k : WaveVec) : waveNorm (perp k) = waveNorm k := by
  simp [waveNorm]

/-- Real dot product of integer modes. -/
def dotR (k l : WaveVec) : ℝ := (dotZ k l : ℝ)

/-- Real cross product / determinant of integer modes. -/
def crossR (k l : WaveVec) : ℝ := (crossZ k l : ℝ)

@[simp] theorem dotR_comm (k l : WaveVec) : dotR k l = dotR l k := by
  simp [dotR]

theorem crossR_swap (k l : WaveVec) : crossR l k = -crossR k l := by
  unfold crossR
  rw [crossZ_swap]
  norm_num

@[simp] theorem crossR_neg_neg (k l : WaveVec) : crossR (-k) (-l) = crossR k l := by
  unfold crossR
  rw [crossZ_neg_neg]

@[simp] theorem dotR_perp_perp (k l : WaveVec) : dotR (perp k) (perp l) = dotR k l := by
  unfold dotR
  rw [dotZ_perp_perp]

/-- Paper §2 Fourier notation (`D_ℕ = ℤ² \ {0}`): nonzero Fourier mode. -/
abbrev NonzeroMode := {k : WaveVec // k ≠ 0}

/-- Paper Appendix equation `trigpoly`: scalar Fourier monomial, represented by Mathlib's
multidimensional unit-torus monomial. -/
def monomial (k : WaveVec) : C(Torus2, ℂ) := UnitAddTorus.mFourier (waveIndex k)

@[simp] theorem monomial_zero : monomial 0 = 1 := by
  simpa [monomial] using (UnitAddTorus.mFourier_zero (d := SpatialIndex))

@[simp] theorem monomial_neg_apply (k : WaveVec) (x : Torus2) :
    monomial (-k) x = conj (monomial k x) := by
  simpa [monomial] using
    (UnitAddTorus.mFourier_neg (n := waveIndex k) (x := x))

@[simp] theorem monomial_add_apply (k l : WaveVec) (x : Torus2) :
    monomial (k + l) x = monomial k x * monomial l x := by
  simpa [monomial] using
    (UnitAddTorus.mFourier_add (n := waveIndex l) (m := waveIndex k) (x := x))

@[simp] theorem monomial_norm (k : WaveVec) : ‖monomial k‖ = 1 := by
  simpa [monomial] using (UnitAddTorus.mFourier_norm (d := SpatialIndex) (n := waveIndex k))

/-- Paper Appendix §Notation (`prelim`): coordinate rescaling from the paper cover `[0,2π]²`
to the repository unit torus.

Mathlib's monomial has phase `2π k·y`; substituting `y=x/(2π)` gives exactly
`k·x`, so this is the explicit bridge to the paper's `exp(i k·x)` convention.
-/
def paperToUnit (x : PaperPoint) : Torus2 :=
  ![((x.1 / paperPeriod : ℝ) : UnitAddCircle),
    ((x.2 / paperPeriod : ℝ) : UnitAddCircle)]

/-- Paper Appendix equation `trigpoly`: scalar exponential `e^{i k·x}`, represented through the
unit-torus monomial and the explicit coordinate rescaling. -/
def paperMonomial (k : WaveVec) (x : PaperPoint) : ℂ := monomial k (paperToUnit x)

/-- Scaling factor converting probability-Haar area on the unit torus to the paper's
unnormalised Lebesgue area on `[0,2π]²`. -/
def paperArea : ℝ := paperPeriod ^ 2

@[simp] theorem paperArea_pos : 0 < paperArea := by
  unfold paperArea paperPeriod
  positivity

end

end BardosTartar
