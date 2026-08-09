import Foundations.Fourier
import Mathlib.Tactic

/-!
# Coefficient-level Navier--Stokes interaction

For a basis pair `(p,q)`, `orderedInteractionR p q` is the coefficient obtained before
symmetrising the two ordered contributions to `(u·∇)u`: differentiating the `q`-mode contributes
`q`, contraction with the `pᗮ` direction contributes `pᗮ·q`, and Leray projection onto the
`(p+q)ᗮ` direction contributes `q·(p+q)`.  The factor `1/(2π)` is exactly the paper basis
normalisation.

The paper's `β(p,q)` is then proved by symmetrising the ordered pair.  No nonlinear Fourier
formula is postulated as an assumption.

Source note: in the proof of the paper lemma `expression to upper bound P_NB(u,u)^2`, one
intermediate displayed numerator has the opposite sign from the subsequently declared `β`.
`betaR_formula` below derives the declared `β` sign directly by averaging the two ordered
contributions; no sign is imported from that intermediate display.
-/

namespace BardosTartar

noncomputable section

open Complex
open scoped ComplexConjugate

/-- Real planar vector used to expose the geometry of the divergence-free basis. -/
abbrev RVec2 := ℝ × ℝ

/-- Bilinear Euclidean dot product on real planar vectors. -/
def rdot (v w : RVec2) : ℝ := v.1 * w.1 + v.2 * w.2

/-- A wave vector regarded as a real planar vector. -/
def modeR (k : WaveVec) : RVec2 := ((k.1 : ℝ), (k.2 : ℝ))

/-- Unit divergence-free direction `kᗮ/|k|` of the repository basis. -/
def unitPerpR (k : WaveVec) : RVec2 :=
  (-((k.2 : ℝ) / waveNorm k), (k.1 : ℝ) / waveNorm k)

/-- Contracting the `p` basis direction with the derivative wave vector `q` gives
`(pᗮ·q)/|p|`. -/
theorem unitPerpR_dot_modeR (p q : WaveVec) :
    rdot (unitPerpR p) (modeR q) = crossR p q / waveNorm p := by
  norm_num [rdot, unitPerpR, modeR, crossR, crossZ]
  ring

/-- Projecting the `qᗮ` direction onto the output divergence-free direction turns
`(p+q)ᗮ·qᗮ` into `(p+q)·q`. -/
theorem unitPerpR_dot_unitPerpR (ell q : WaveVec) :
    rdot (unitPerpR ell) (unitPerpR q) =
      dotR ell q / (waveNorm ell * waveNorm q) := by
  norm_num [rdot, unitPerpR, dotR, dotZ]
  ring

/-- Interaction factor obtained directly from: derivative of the `q` monomial, contraction with
the `p` basis direction, Leray projection onto the `(p+q)` divergence-free direction, and the
paper's single residual `1/(2π)` basis-normalisation factor. -/
def basisDerivedInteractionR (p q : WaveVec) : ℝ :=
  rdot (unitPerpR p) (modeR q) *
    rdot (unitPerpR (p + q)) (unitPerpR q) / paperPeriod

/-- Common geometric denominator in a two-mode interaction. -/
def interactionDenom (p q : WaveVec) : ℝ :=
  waveNorm p * waveNorm q * waveNorm (p + q)

@[simp] theorem interactionDenom_swap (p q : WaveVec) :
    interactionDenom q p = interactionDenom p q := by
  simp [interactionDenom, add_comm, mul_comm, mul_left_comm, mul_assoc]

/-- Unsymmetrised real interaction factor coming from the direct Fourier computation of
`P((φ_p · ∇) φ_q)` in the paper-normalised basis. -/
def orderedInteractionR (p q : WaveVec) : ℝ :=
  crossR p q * dotR q (p + q) / (paperPeriod * interactionDenom p q)

/-- The geometric basis computation above simplifies to the unsymmetrised coefficient used in
the Fourier convolution.  The nonzero hypotheses are exactly the modes for which the paper basis
`kᗮ/|k|` is defined. -/
theorem basisDerivedInteractionR_eq_orderedInteractionR
    {p q : WaveVec} (hp : p ≠ 0) (hq : q ≠ 0) (hout : p + q ≠ 0) :
    basisDerivedInteractionR p q = orderedInteractionR p q := by
  rw [basisDerivedInteractionR, unitPerpR_dot_modeR, unitPerpR_dot_unitPerpR]
  rw [dotR_comm (p + q) q]
  unfold orderedInteractionR interactionDenom
  field_simp [paperPeriod_ne_zero, waveNorm_ne_zero hp, waveNorm_ne_zero hq,
    waveNorm_ne_zero hout]
  ring

/-- Complex unsymmetrised interaction coefficient. -/
def orderedInteraction (p q : WaveVec) : ℂ :=
  Complex.I * (orderedInteractionR p q : ℂ)

/-- Real scalar underlying the symmetric paper interaction coefficient. -/
def betaR (p q : WaveVec) : ℝ :=
  (orderedInteractionR p q + orderedInteractionR q p) / 2

/-- Paper §2, definition immediately after equation `chonvolution`: interaction coefficient
`β(p,q) = i/(4π) * (pᗮ·q) (|q|²-|p|²) / (|p||q||p+q|)`.
-/
def beta (p q : WaveVec) : ℂ := Complex.I * (betaR p q : ℂ)

/-- Elementary vector identity used in the symmetrisation. -/
theorem dot_difference_eq_sqNorm_difference (p q : WaveVec) :
    dotR q (p + q) - dotR p (p + q) = sqNorm q - sqNorm p := by
  norm_num [dotR, dotZ, sqNorm, sqNormZ]
  ring

/-- Paper §2, definition immediately after equation `chonvolution`: the symmetrised real
coefficient has exactly the closed form printed in the definition of
`β` in the paper. -/
theorem betaR_formula (p q : WaveVec) :
    betaR p q =
      crossR p q * (sqNorm q - sqNorm p) /
        (2 * paperPeriod * interactionDenom p q) := by
  by_cases hD : interactionDenom p q = 0
  · simp [betaR, orderedInteractionR, hD]
  · have hP : paperPeriod ≠ 0 := paperPeriod_ne_zero
    have hswap : interactionDenom q p = interactionDenom p q := interactionDenom_swap p q
    rw [betaR, orderedInteractionR, orderedInteractionR, hswap, crossR_swap]
    rw [← dot_difference_eq_sqNorm_difference p q]
    field_simp [hP, hD]
    ring

/-- Paper §2, definition immediately after equation `chonvolution`: explicit closed formula
for the complex interaction coefficient, with `2 * paperPeriod = 4π`. -/
theorem beta_formula (p q : WaveVec) :
    beta p q =
      Complex.I *
        ((crossR p q * (sqNorm q - sqNorm p) /
          (2 * paperPeriod * interactionDenom p q) : ℝ) : ℂ) := by
  rw [beta, betaR_formula]

/-- Unsymmetrised ordered contributions add to twice the paper coefficient. -/
theorem orderedInteraction_add_swap (p q : WaveVec) :
    orderedInteraction p q + orderedInteraction q p = 2 * beta p q := by
  simp [orderedInteraction, beta, betaR]
  push_cast
  ring

/-- `β` is symmetric in its two input modes. -/
@[simp] theorem beta_swap (p q : WaveVec) : beta q p = beta p q := by
  simp [beta, betaR]
  ring

/-- Simultaneous sign reversal leaves the ordered real interaction unchanged. -/
@[simp] theorem orderedInteractionR_neg_neg (p q : WaveVec) :
    orderedInteractionR (-p) (-q) = orderedInteractionR p q := by
  have hsum : (-p) + (-q) = -(p + q) := by abel
  rw [orderedInteractionR, orderedInteractionR, hsum]
  simp [interactionDenom, dotR, dotZ, crossR, crossZ]
  ring

/-- Simultaneous sign reversal leaves `β` unchanged. -/
@[simp] theorem beta_neg_neg (p q : WaveVec) : beta (-p) (-q) = beta p q := by
  simp [beta, betaR]

/-- `β` is purely imaginary, as is evident from its real scalar factor. -/
@[simp] theorem conj_beta (p q : WaveVec) : conj (beta p q) = -beta p q := by
  simp [beta]

/-- Two modes are parallel exactly when their planar determinant vanishes. -/
def ModesParallel (p q : WaveVec) : Prop := crossZ p q = 0

/-- Two modes lie on the same spectral shell. -/
def EqualMagnitude (p q : WaveVec) : Prop := sqNormZ p = sqNormZ q

/-- `β` vanishes for parallel modes. -/
theorem beta_eq_zero_of_parallel {p q : WaveVec} (h : ModesParallel p q) : beta p q = 0 := by
  have hz : crossZ p q = 0 := h
  rw [beta, betaR_formula]
  simp [crossR, hz]

/-- `β` vanishes for equal-magnitude modes. -/
theorem beta_eq_zero_of_equalMagnitude {p q : WaveVec} (h : EqualMagnitude p q) : beta p q = 0 := by
  rw [beta, betaR_formula]
  have hz : sqNormZ p = sqNormZ q := h
  have hs : sqNorm p = sqNorm q := by
    simp [sqNorm, hz]
  simp [hs]

/-- In particular, opposite modes do not interact into the zero mode. -/
@[simp] theorem beta_add_neg (p : WaveVec) : beta p (-p) = 0 := by
  apply beta_eq_zero_of_parallel
  unfold ModesParallel crossZ
  ring

/-- Paper lemma `expression to upper bound P_NB(u,u)^2`: a single contribution obtained
directly from the Fourier differentiation/contraction/Leray-projection computation before the
ordered pair is symmetrised. -/
def directBasisTerm (u : TrigPoly) (ell p q : WaveVec) : ℂ :=
  if p + q = ell then
    Complex.I * (basisDerivedInteractionR p q : ℂ) * u.fourierCoeff p * u.fourierCoeff q
  else 0

/-- A single ordered contribution to the Fourier coefficient at output mode `ell`. -/
def orderedTerm (u : TrigPoly) (ell p q : WaveVec) : ℂ :=
  if p + q = ell then
    orderedInteraction p q * u.fourierCoeff p * u.fourierCoeff q
  else 0

/-- The same contribution written with the paper's symmetric `β`. -/
def betaTerm (u : TrigPoly) (ell p q : WaveVec) : ℂ :=
  if p + q = ell then beta p q * u.fourierCoeff p * u.fourierCoeff q else 0

/-- Paper lemma `expression to upper bound P_NB(u,u)^2`: finite Fourier coefficient obtained
from the direct basis-level differentiation/contraction/projection computation. -/
def directBasisNonlinearCoeff (u : TrigPoly) (ell : WaveVec) : ℂ :=
  ∑ p ∈ u.support, ∑ q ∈ u.support, directBasisTerm u ell p q

/-- Fourier coefficient obtained from the direct ordered expansion of `(u·∇)u` followed by Leray
projection.  Both input sums are finite because `u` is a trigonometric polynomial. -/
def orderedNonlinearCoeff (u : TrigPoly) (ell : WaveVec) : ℂ :=
  ∑ p ∈ u.support, ∑ q ∈ u.support, orderedTerm u ell p q

/-- On a nonzero output mode, the direct basis computation agrees term-by-term with the
unsymmetrised interaction coefficient. -/
theorem directBasisTerm_eq_orderedTerm (u : TrigPoly) {ell p q : WaveVec}
    (hp : p ≠ 0) (hq : q ≠ 0) (hell : ell ≠ 0) :
    directBasisTerm u ell p q = orderedTerm u ell p q := by
  by_cases hsum : p + q = ell
  · have hout : p + q ≠ 0 := by simpa [hsum] using hell
    simp only [directBasisTerm, orderedTerm, hsum, if_true]
    rw [basisDerivedInteractionR_eq_orderedInteractionR hp hq hout]
    simp [orderedInteraction]
  · simp [directBasisTerm, orderedTerm, hsum]

/-- Paper lemma `expression to upper bound P_NB(u,u)^2`: the coefficient obtained from the
basis-level calculation equals the ordered Fourier coefficient on every nonzero output mode. -/
theorem directBasisNonlinearCoeff_eq_ordered (u : TrigPoly) {ell : WaveVec} (hell : ell ≠ 0) :
    directBasisNonlinearCoeff u ell = orderedNonlinearCoeff u ell := by
  classical
  rw [directBasisNonlinearCoeff, orderedNonlinearCoeff]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  exact directBasisTerm_eq_orderedTerm u (TrigPoly.mem_support_ne_zero hp)
    (TrigPoly.mem_support_ne_zero hq) hell

/-- Paper lemma `expression to upper bound P_NB(u,u)^2`: Fourier coefficient in the compact
convolution form used throughout the paper. -/
def nonlinearCoeff (u : TrigPoly) (ell : WaveVec) : ℂ :=
  ∑ p ∈ u.support, ∑ q ∈ u.support, betaTerm u ell p q

/-- Finite double sums may be symmetrised by averaging with the transposed summand. -/
theorem sum_pair_symmetrize {α : Type*} [DecidableEq α]
    (s : Finset α) (f : α → α → ℂ) :
    (∑ p ∈ s, ∑ q ∈ s, f p q) =
      (1 / 2 : ℂ) * ∑ p ∈ s, ∑ q ∈ s, (f p q + f q p) := by
  classical
  have hswap :
      (∑ p ∈ s, ∑ q ∈ s, f q p) = (∑ p ∈ s, ∑ q ∈ s, f p q) := by
    rw [Finset.sum_comm]
  have hsplit :
      (∑ p ∈ s, ∑ q ∈ s, (f p q + f q p)) =
        (∑ p ∈ s, ∑ q ∈ s, f p q) + (∑ p ∈ s, ∑ q ∈ s, f q p) := by
    simp_rw [Finset.sum_add_distrib]
  rw [hsplit, hswap]
  ring

/-- Pointwise symmetrisation of an ordered interaction term. -/
theorem orderedTerm_add_swap (u : TrigPoly) (ell p q : WaveVec) :
    orderedTerm u ell p q + orderedTerm u ell q p = 2 * betaTerm u ell p q := by
  by_cases h : p + q = ell
  · have h' : q + p = ell := by simpa [add_comm] using h
    simp only [orderedTerm, betaTerm, h, h', if_true]
    rw [orderedInteraction_add_swap]
    ring
  · have h' : q + p ≠ ell := by simpa [add_comm] using h
    simp [orderedTerm, betaTerm, h, h']

/-- Paper lemma `expression to upper bound P_NB(u,u)^2` and Lemma `expansion`: Fourier
coefficient formula for the nonlinear term on trigonometric polynomials.

This theorem is obtained from the ordered Fourier expansion and the proved two-mode
symmetrisation; it is not an assumption.  It is the coefficient-level form underlying the paper's
convolution estimate for `P_N B(u,u)` and the later power-series recurrence.
-/
theorem orderedNonlinearCoeff_eq_beta (u : TrigPoly) (ell : WaveVec) :
    orderedNonlinearCoeff u ell = nonlinearCoeff u ell := by
  classical
  rw [orderedNonlinearCoeff, nonlinearCoeff]
  rw [sum_pair_symmetrize]
  simp_rw [orderedTerm_add_swap]
  have hfactor :
      (∑ p ∈ u.support, ∑ q ∈ u.support, 2 * betaTerm u ell p q) =
        2 * (∑ p ∈ u.support, ∑ q ∈ u.support, betaTerm u ell p q) := by
    simp_rw [Finset.mul_sum]
  rw [hfactor]
  ring

/-- Paper lemma `expression to upper bound P_NB(u,u)^2`: the Fourier coefficient calculated
directly from the basis differentiation/contraction/projection rules is the paper `β` convolution
on every nonzero output mode. -/
theorem directBasisNonlinearCoeff_eq_beta (u : TrigPoly) {ell : WaveVec} (hell : ell ≠ 0) :
    directBasisNonlinearCoeff u ell = nonlinearCoeff u ell := by
  rw [directBasisNonlinearCoeff_eq_ordered u hell, orderedNonlinearCoeff_eq_beta]

end

end BardosTartar
