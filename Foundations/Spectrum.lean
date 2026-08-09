import Foundations.Torus
import Mathlib

/-!
# Spectrum and lattice shells for the two-dimensional periodic problem

Wave 1 / Agent B.

The paper works on `[0,2π]²`, so the Fourier/Stokes eigenvalue attached to
`k = (k₁,k₂) ∈ ℤ²` is `|k|² = k₁² + k₂²`.  We construct the distinct positive
spectral values explicitly from the integer lattice instead of invoking a
general spectral theorem.

Indexing convention:

* `lambda 0 = 0` is an auxiliary value;
* `lambda 1 < lambda 2 < ...` are exactly the distinct positive represented
  values of `|k|²`.

This revision incorporates the diagnostics from the first external Lean run.
It was prepared without running Lean locally, as requested.
-/

open Filter
open scoped BigOperators

namespace BardosTartar

/-- Agent B name for the repository's canonical integer Fourier mode type. -/
abbrev WaveVector := WaveVec

/-- Paper quantity `|k|²`. -/
def waveSqNorm (k : WaveVector) : ℕ :=
  k.1.natAbs ^ 2 + k.2.natAbs ^ 2

@[simp]
theorem waveSqNorm_zero : waveSqNorm (0, 0) = 0 := by
  simp [waveSqNorm]

/-- `|k|² = 0` exactly for the zero Fourier mode. -/
theorem waveSqNorm_eq_zero_iff (k : WaveVector) :
    waveSqNorm k = 0 ↔ k = (0, 0) := by
  rcases k with ⟨k₁, k₂⟩
  simp [waveSqNorm, Prod.ext_iff]

/-- Every nonzero lattice mode has positive squared norm. -/
theorem waveSqNorm_pos {k : WaveVector} (hk : k ≠ (0, 0)) :
    0 < waveSqNorm k := by
  exact Nat.pos_of_ne_zero (mt (waveSqNorm_eq_zero_iff k).mp hk)

/-- Predicate defining a positive spectral value of the periodic Stokes operator. -/
def IsSpectralValue (m : ℕ) : Prop :=
  0 < m ∧ ∃ k : WaveVector, k ≠ (0, 0) ∧ waveSqNorm k = m

theorem isSpectralValue_iff (m : ℕ) :
    IsSpectralValue m ↔ ∃ k : WaveVector, k ≠ (0, 0) ∧ waveSqNorm k = m := by
  constructor
  · rintro ⟨_, k, hk, rfl⟩
    exact ⟨k, hk, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨waveSqNorm_pos hk, k, hk, rfl⟩

/-- Every positive square occurs as a spectral value, using the mode `(n+1,0)`. -/
theorem square_succ_isSpectralValue (n : ℕ) :
    IsSpectralValue ((n + 1) ^ 2) := by
  refine ⟨by positivity, ?_⟩
  refine ⟨((((n + 1 : ℕ) : ℤ), 0) : WaveVector), ?_, ?_⟩
  · intro h
    have hfst : ((n + 1 : ℕ) : ℤ) = 0 := congrArg Prod.fst h
    have hpos : (0 : ℤ) < ((n + 1 : ℕ) : ℤ) := by
      exact_mod_cast Nat.succ_pos n
    exact (ne_of_gt hpos) hfst
  · have hnonneg : (0 : ℤ) ≤ ((n + 1 : ℕ) : ℤ) := by
      positivity
    have habs : (((n + 1 : ℕ) : ℤ).natAbs) = n + 1 := by
      exact_mod_cast Int.natAbs_of_nonneg hnonneg
    change (((((n + 1 : ℕ) : ℤ).natAbs) ^ 2) + 0) = (n + 1) ^ 2
    simpa [habs]

/-- The set of positive spectral values is infinite. -/
theorem spectralValues_infinite :
    (Set.ofPred IsSpectralValue).Infinite := by
  let f : ℕ → ℕ := fun n => (n + 1) ^ 2
  have hf : Function.Injective f := by
    intro a b hab
    dsimp [f] at hab
    have hab' : a + 1 = b + 1 := by
      exact (Nat.pow_left_strictMono (by decide : (2 : ℕ) ≠ 0)).injective hab
    omega
  have hrange : (Set.range f).Infinite := Set.infinite_range_of_injective hf
  refine hrange.mono ?_
  rintro m ⟨n, rfl⟩
  exact square_succ_isSpectralValue n

/-- Zero-indexed enumeration of the distinct positive spectral values. -/
noncomputable def lambda0 (n : ℕ) : ℕ :=
  Nat.nth IsSpectralValue n

/-- Paper eigenvalue sequence, extended by `lambda 0 = 0`. -/
noncomputable def lambda (N : ℕ) : ℕ :=
  if N = 0 then 0 else lambda0 (N - 1)

@[simp]
theorem lambda_zero : lambda 0 = 0 := by
  simp [lambda]

theorem lambda_of_pos {N : ℕ} (hN : 0 < N) :
    lambda N = Nat.nth IsSpectralValue (N - 1) := by
  simp [lambda, lambda0, Nat.ne_of_gt hN]

/-- Every positive-indexed eigenvalue is represented by a nonzero lattice mode. -/
theorem lambda_isSpectralValue {N : ℕ} (hN : 0 < N) :
    IsSpectralValue (lambda N) := by
  rw [lambda_of_pos hN]
  exact Nat.nth_mem_of_infinite spectralValues_infinite (N - 1)

/-- Positivity of `lambda N` at every paper index. -/
theorem lambda_pos {N : ℕ} (hN : 0 < N) :
    0 < lambda N :=
  (lambda_isSpectralValue hN).1

/-- The first positive spectral value is `1`. -/
theorem lambda_one : lambda 1 = 1 := by
  rw [lambda_of_pos (by decide : 0 < (1 : ℕ))]
  have hmem : IsSpectralValue (Nat.nth IsSpectralValue 0) :=
    Nat.nth_mem_of_infinite spectralValues_infinite 0
  have hleast := Nat.isLeast_nth_of_infinite spectralValues_infinite 0
  have hone : IsSpectralValue 1 := by
    simpa using square_succ_isSpectralValue 0
  have hle : Nat.nth IsSpectralValue 0 ≤ 1 := by
    apply hleast.2
    exact ⟨hone, by intro k hk; omega⟩
  have hpos : 0 < Nat.nth IsSpectralValue 0 := hmem.1
  exact le_antisymm hle (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos))

/-- The extended eigenvalue sequence is strictly increasing, including `0 < lambda 1`. -/
theorem lambda_strictMono : StrictMono lambda := by
  intro a b hab
  by_cases ha : a = 0
  · subst a
    rw [lambda_zero]
    exact lambda_pos (by omega)
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha
    have hbPos : 0 < b := lt_of_lt_of_le haPos hab.le
    rw [lambda_of_pos haPos, lambda_of_pos hbPos]
    apply Nat.nth_strictMono spectralValues_infinite
    omega

/-- Paper-facing restriction of strict monotonicity to positive indices. -/
theorem lambda_strictMonoOn :
    StrictMonoOn lambda (Set.Ici 1) := by
  intro a _ b _ hab
  exact lambda_strictMono hab

/-- Monotonicity of the spectral enumeration. -/
theorem lambda_monotone : Monotone lambda :=
  lambda_strictMono.monotone

/-- Consecutive paper eigenvalues are strictly increasing. -/
theorem lambda_lt_lambda_succ {N : ℕ} (_hN : 0 < N) :
    lambda N < lambda (N + 1) := by
  exact lambda_strictMono (Nat.lt_succ_self N)

/-- The distinct spectral values tend to infinity. -/
theorem lambda_tendsto_atTop :
    Tendsto lambda atTop atTop :=
  lambda_strictMono.tendsto_atTop

/-- Explicit threshold form of `lambda N → ∞`. -/
theorem exists_lambda_gt (B : ℕ) :
    ∃ N ≥ 1, B < lambda N := by
  have hev : ∀ᶠ N : ℕ in atTop, B + 1 ≤ lambda N :=
    (tendsto_atTop.1 lambda_tendsto_atTop) (B + 1)
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hev
  let N := max N0 1
  refine ⟨N, le_max_right _ _, ?_⟩
  have hle : B + 1 ≤ lambda N := hN0 N (le_max_left _ _)
  omega

/-- Paper spectral gap `d_N = lambda (N+1) - lambda N`. -/
noncomputable def d (N : ℕ) : ℕ :=
  lambda (N + 1) - lambda N

/-- Paper midpoint `tildeLambda N = (lambda N + lambda (N+1))/2`. -/
noncomputable def tildeLambda (N : ℕ) : ℝ :=
  ((lambda N : ℝ) + (lambda (N + 1) : ℝ)) / 2

/-- Positive spectral gaps for positive indices. -/
theorem d_pos {N : ℕ} (hN : 0 < N) :
    0 < d N := by
  exact Nat.sub_pos_iff_lt.mpr (lambda_lt_lambda_succ hN)

/-- Every positive spectral gap is at least one. -/
theorem one_le_d {N : ℕ} (hN : 0 < N) :
    1 ≤ d N := d_pos hN

/-- Paper form `lambda 1 ≤ d N`. -/
theorem lambda_one_le_d {N : ℕ} (hN : 0 < N) :
    lambda 1 ≤ d N := by
  simpa [lambda_one] using one_le_d hN

/-- Recover the next spectral value from the current one and the gap. -/
theorem lambda_add_d {N : ℕ} (hN : 0 < N) :
    lambda N + d N = lambda (N + 1) := by
  rw [d, Nat.add_sub_of_le]
  exact (lambda_lt_lambda_succ hN).le

/-- The midpoint lies strictly above `lambda N`. -/
theorem lambda_lt_tildeLambda {N : ℕ} (hN : 0 < N) :
    (lambda N : ℝ) < tildeLambda N := by
  have hreal : (lambda N : ℝ) < (lambda (N + 1) : ℝ) := by
    exact_mod_cast lambda_lt_lambda_succ hN
  unfold tildeLambda
  linarith

/-- The midpoint lies strictly below `lambda (N+1)`. -/
theorem tildeLambda_lt_lambda_succ {N : ℕ} (hN : 0 < N) :
    tildeLambda N < (lambda (N + 1) : ℝ) := by
  have hreal : (lambda N : ℝ) < (lambda (N + 1) : ℝ) := by
    exact_mod_cast lambda_lt_lambda_succ hN
  unfold tildeLambda
  linarith

/-! ## Concrete lattice shells -/

/-- Integer interval `[-R,R]`.  This is noncomputable because Mathlib's
locally-finite-order finset instance for `ℤ` is noncomputable. -/
noncomputable def intBox (R : ℕ) : Finset ℤ :=
  Finset.Icc (-(R : ℤ)) (R : ℤ)

/-- Convert an absolute-value bound into membership in the finite integer box. -/
theorem mem_intBox_of_natAbs_le {R : ℕ} {z : ℤ} (hz : z.natAbs ≤ R) :
    z ∈ intBox R := by
  cases z <;> simp [intBox] at hz ⊢ <;> omega

/-- Membership in the finite integer box implies the corresponding absolute-value bound. -/
theorem natAbs_le_of_mem_intBox {R : ℕ} {z : ℤ} (hz : z ∈ intBox R) :
    z.natAbs ≤ R := by
  cases z <;> simp [intBox] at hz ⊢ <;> omega

/-- Each coordinate absolute value is bounded by the squared norm. -/
theorem natAbs_fst_le_waveSqNorm (k : WaveVector) :
    k.1.natAbs ≤ waveSqNorm k := by
  by_cases h : k.1.natAbs = 0
  · simp [h]
  have h1 : 1 ≤ k.1.natAbs := Nat.one_le_iff_ne_zero.mpr h
  dsimp [waveSqNorm]
  nlinarith [Nat.zero_le k.2.natAbs]

/-- Same bound for the second coordinate. -/
theorem natAbs_snd_le_waveSqNorm (k : WaveVector) :
    k.2.natAbs ≤ waveSqNorm k := by
  by_cases h : k.2.natAbs = 0
  · simp [h, waveSqNorm]
  have h1 : 1 ≤ k.2.natAbs := Nat.one_le_iff_ne_zero.mpr h
  dsimp [waveSqNorm]
  nlinarith [Nat.zero_le k.1.natAbs]

/-- Finite lattice shell at arbitrary squared radius `m`. -/
noncomputable def latticeShell (m : ℕ) : Finset WaveVector :=
  (intBox m ×ˢ intBox m).filter fun k => waveSqNorm k = m

/-- Membership in `latticeShell m` is exactly the sum-of-two-squares equation. -/
theorem mem_latticeShell_iff {m : ℕ} {k : WaveVector} :
    k ∈ latticeShell m ↔ waveSqNorm k = m := by
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hk⟩
    · apply mem_intBox_of_natAbs_le
      exact (natAbs_fst_le_waveSqNorm k).trans_eq hk
    · apply mem_intBox_of_natAbs_le
      exact (natAbs_snd_le_waveSqNorm k).trans_eq hk

/-- Paper shell `D_N = {k : |k|² = lambda N}`. -/
noncomputable def D (N : ℕ) : Finset WaveVector :=
  latticeShell (lambda N)

/-- Paper finite low-mode set `D_{≤N}`. -/
noncomputable def DLE (N : ℕ) : Finset WaveVector :=
  (intBox (lambda N) ×ˢ intBox (lambda N)).filter fun k =>
    k ≠ (0, 0) ∧ waveSqNorm k ≤ lambda N

/-- Paper high-mode set `D_{>N}`. -/
noncomputable def DGT (N : ℕ) : Set WaveVector :=
  {k | k ≠ (0, 0) ∧ lambda N < waveSqNorm k}

/-- All nonzero Fourier modes. -/
def DNat : Set WaveVector :=
  {k | k ≠ (0, 0)}

theorem mem_D_iff {N : ℕ} {k : WaveVector} :
    k ∈ D N ↔ waveSqNorm k = lambda N := by
  simpa [D] using (mem_latticeShell_iff (m := lambda N) (k := k))

theorem mem_DLE_iff {N : ℕ} {k : WaveVector} :
    k ∈ DLE N ↔ k ≠ (0, 0) ∧ waveSqNorm k ≤ lambda N := by
  constructor
  · intro hk
    exact (Finset.mem_filter.mp hk).2
  · intro hk
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hk⟩
    · apply mem_intBox_of_natAbs_le
      exact (natAbs_fst_le_waveSqNorm k).trans hk.2
    · apply mem_intBox_of_natAbs_le
      exact (natAbs_snd_le_waveSqNorm k).trans hk.2

theorem mem_DGT_iff {N : ℕ} {k : WaveVector} :
    k ∈ DGT N ↔ k ≠ (0, 0) ∧ lambda N < waveSqNorm k :=
  Iff.rfl

/-- Positive-indexed shells contain no zero mode. -/
theorem zero_not_mem_D {N : ℕ} (hN : 0 < N) :
    (0, 0) ∉ D N := by
  rw [mem_D_iff, waveSqNorm_zero]
  exact ne_of_lt (lambda_pos hN)

/-- Shell `D_N` sits inside the first `N` eigenspaces. -/
theorem D_subset_DLE {N : ℕ} (hN : 0 < N) :
    D N ⊆ DLE N := by
  intro k hk
  rw [mem_DLE_iff]
  have hsq : waveSqNorm k = lambda N := mem_D_iff.mp hk
  refine ⟨?_, hsq.le⟩
  intro hk0
  subst k
  have hzero : 0 = lambda N := by simpa using hsq
  exact (ne_of_lt (lambda_pos hN)) hzero

/-- Distinct positive spectral shells are disjoint. -/
theorem D_disjoint {M N : ℕ} (_hM : 0 < M) (_hN : 0 < N) (hMN : M ≠ N) :
    Disjoint (D M) (D N) := by
  rw [Finset.disjoint_left]
  intro k hkM hkN
  apply hMN
  apply lambda_strictMono.injective
  calc
    lambda M = waveSqNorm k := (mem_D_iff.mp hkM).symm
    _ = lambda N := mem_D_iff.mp hkN

/-- Low-mode sets are nested with the cutoff. -/
theorem DLE_mono {M N : ℕ} (hMN : M ≤ N) :
    DLE M ⊆ DLE N := by
  intro k hk
  rw [mem_DLE_iff] at hk ⊢
  exact ⟨hk.1, hk.2.trans (lambda_monotone hMN)⟩

/-- Every nonzero mode occurs in exactly one positive shell. -/
theorem exists_unique_shell {k : WaveVector} (hk : k ≠ (0, 0)) :
    ∃! N : ℕ, 0 < N ∧ k ∈ D N := by
  have hs : IsSpectralValue (waveSqNorm k) :=
    ⟨waveSqNorm_pos hk, k, hk, rfl⟩
  have hs' : waveSqNorm k ∈ Set.ofPred IsSpectralValue := hs
  obtain ⟨n, hn⟩ :=
    (Nat.subset_range_nth (p := IsSpectralValue)) hs'
  refine ⟨n + 1, ?_, ?_⟩
  · constructor
    · omega
    · rw [mem_D_iff, lambda_of_pos (by omega)]
      exact hn.symm
  · intro M hM
    rcases hM with ⟨hMpos, hkM⟩
    apply lambda_strictMono.injective
    calc
      lambda M = waveSqNorm k := (mem_D_iff.mp hkM).symm
      _ = Nat.nth IsSpectralValue n := hn.symm
      _ = lambda (n + 1) := by
        rw [lambda_of_pos (by omega)]
        simp

/-! ## Elementary finite cardinality facts

The first external run showed that the previous draft incorrectly invoked a
nonexistent Gaussian-integer representation-count theorem.  That shortcut has
been removed.  The exact paper estimate `#latticeShell n = O(n^ε)` is a genuine
number-theory obligation and is intentionally **not** replaced here by an
assumption or by the weaker square-box estimate below.

The declarations in this section are genuine elementary bounds and are useful
for debugging the shell model, but they are not advertised as a substitute for
the paper's divisor bound.
-/

/-- Number of ordered signed lattice representations of `m` as a sum of two squares. -/
noncomputable def twoSquaresRepCount (m : ℕ) : ℕ :=
  (latticeShell m).card

/-- Every shell is a subset of its defining finite box. -/
theorem latticeShell_card_le_box (m : ℕ) :
    (latticeShell m).card ≤ (intBox m ×ˢ intBox m).card := by
  unfold latticeShell
  exact Finset.card_filter_le _ _

/-- Corresponding paper-shell finite-box bound. -/
theorem D_card_le_box (N : ℕ) :
    (D N).card ≤ (intBox (lambda N) ×ˢ intBox (lambda N)).card := by
  simpa [D] using latticeShell_card_le_box (lambda N)

/-- The entire low-mode set is contained in its defining finite box. -/
theorem DLE_card_le_box (N : ℕ) :
    (DLE N).card ≤ (intBox (lambda N) ×ˢ intBox (lambda N)).card := by
  unfold DLE
  exact Finset.card_filter_le _ _

end BardosTartar
