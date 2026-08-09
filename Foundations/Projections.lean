import Foundations.Spectrum

/-!
# Explicit spectral projections

Wave 1 / Agent B.

The Fourier-side Stokes operator is diagonal, so the finite-dimensional
spectral projections are represented here as coefficient masks.  The concrete
function-space projections can later be obtained by conjugating these maps with
Agent A's Fourier coefficient equivalence.

This revision was prepared from the first external compiler diagnostics without
running Lean locally, as requested.
-/

namespace BardosTartar

-- `lambda` is noncomputable, so propositions comparing a mode against a spectral
-- cutoff do not receive a computational Decidable instance automatically.
-- The projections are mathematical (not executable) masks, so classical
-- proposition decidability is exactly the appropriate local instance.
attribute [local instance] Classical.propDecidable

section Coefficients

variable {E : Type*}

/-- Generic coefficient family used only for pointwise spectral-mask lemmas.
This is deliberately not named `FourierCoeff`, which is Agent A's canonical finitely-supported type. -/
abbrev SpectralCoeff (E : Type*) := WaveVector → E

/-- Predicate for the first `N` positive spectral shells. -/
noncomputable def IsLowMode (N : ℕ) (k : WaveVector) : Prop :=
  k ≠ (0, 0) ∧ waveSqNorm k ≤ lambda N

/-- Predicate for the strict high-frequency complement. -/
noncomputable def IsHighMode (N : ℕ) (k : WaveVector) : Prop :=
  k ≠ (0, 0) ∧ lambda N < waveSqNorm k

theorem isLowMode_iff_mem_DLE {N : ℕ} {k : WaveVector} :
    IsLowMode N k ↔ k ∈ DLE N := by
  simpa [IsLowMode] using (mem_DLE_iff (N := N) (k := k)).symm

theorem isHighMode_iff_mem_DGT {N : ℕ} {k : WaveVector} :
    IsHighMode N k ↔ k ∈ DGT N := by
  rfl

/-- Low-mode membership is monotone in the cutoff. -/
theorem IsLowMode.mono {M N : ℕ} (hMN : M ≤ N) {k : WaveVector}
    (hk : IsLowMode M k) : IsLowMode N k := by
  exact ⟨hk.1, hk.2.trans (lambda_monotone hMN)⟩

/-- A nonzero mode cannot be simultaneously below and strictly above the same cutoff. -/
theorem not_low_and_high (N : ℕ) (k : WaveVector) :
    ¬ (IsLowMode N k ∧ IsHighMode N k) := by
  rintro ⟨hlow, hhigh⟩
  exact (not_lt_of_ge hlow.2) hhigh.2

variable [Zero E]

/-- Paper projection `P_N`, expressed as a coefficient mask. -/
noncomputable def P (N : ℕ) (a : SpectralCoeff E) : SpectralCoeff E :=
  fun k => if IsLowMode N k then a k else 0

/-- Strict high-mode mask. -/
noncomputable def Qmask (N : ℕ) (a : SpectralCoeff E) : SpectralCoeff E :=
  fun k => if IsHighMode N k then a k else 0

@[simp]
theorem P_apply_of_low {N : ℕ} {a : SpectralCoeff E} {k : WaveVector}
    (hk : IsLowMode N k) :
    P N a k = a k := by
  simp [P, hk]

@[simp]
theorem P_apply_of_not_low {N : ℕ} {a : SpectralCoeff E} {k : WaveVector}
    (hk : ¬ IsLowMode N k) :
    P N a k = 0 := by
  simp [P, hk]

@[simp]
theorem Qmask_apply_of_high {N : ℕ} {a : SpectralCoeff E} {k : WaveVector}
    (hk : IsHighMode N k) :
    Qmask N a k = a k := by
  simp [Qmask, hk]

@[simp]
theorem Qmask_apply_of_not_high {N : ℕ} {a : SpectralCoeff E} {k : WaveVector}
    (hk : ¬ IsHighMode N k) :
    Qmask N a k = 0 := by
  simp [Qmask, hk]

/-- `P_N` is idempotent. -/
@[simp]
theorem P_idem (N : ℕ) (a : SpectralCoeff E) :
    P N (P N a) = P N a := by
  funext k
  by_cases hk : IsLowMode N k <;> simp [P, hk]

/-- The high-mode mask is idempotent. -/
@[simp]
theorem Qmask_idem (N : ℕ) (a : SpectralCoeff E) :
    Qmask N (Qmask N a) = Qmask N a := by
  funext k
  by_cases hk : IsHighMode N k <;> simp [Qmask, hk]

/-- Nested low-mode projections compose to the smaller cutoff. -/
theorem P_comp_of_le {M N : ℕ} (hMN : M ≤ N) (a : SpectralCoeff E) :
    P M (P N a) = P M a := by
  funext k
  by_cases hkM : IsLowMode M k
  · have hkN : IsLowMode N k := hkM.mono hMN
    simp [P, hkM, hkN]
  · simp [P, hkM]

/-- Applying the larger projection after the smaller one changes nothing. -/
theorem P_comp_of_le' {M N : ℕ} (hMN : M ≤ N) (a : SpectralCoeff E) :
    P N (P M a) = P M a := by
  funext k
  by_cases hkM : IsLowMode M k
  · have hkN : IsLowMode N k := hkM.mono hMN
    simp [P, hkM, hkN]
  · by_cases hkN : IsLowMode N k <;> simp [P, hkM, hkN]

/-- A low projection kills a strict-high-mode mask. -/
theorem P_Qmask_zero (N : ℕ) (a : SpectralCoeff E) :
    P N (Qmask N a) = 0 := by
  funext k
  by_cases hl : IsLowMode N k
  · have hh : ¬ IsHighMode N k := by
      intro hh
      exact not_low_and_high N k ⟨hl, hh⟩
    simp [P, Qmask, hl, hh]
  · simp [P, hl]

end Coefficients

section Additive

variable {E : Type*} [AddCommGroup E]

/-- Paper complementary projection `Q_N = 1 - P_N`. -/
noncomputable def Q (N : ℕ) (a : SpectralCoeff E) : SpectralCoeff E :=
  a - P N a

/-- Paper band projection `P_{N,n} = P_N - P_n`. -/
noncomputable def PBetween (N n : ℕ) (a : SpectralCoeff E) : SpectralCoeff E :=
  P N a - P n a

@[simp]
theorem Q_apply (N : ℕ) (a : SpectralCoeff E) (k : WaveVector) :
    Q N a k = if IsLowMode N k then 0 else a k := by
  by_cases hk : IsLowMode N k <;> simp [Q, P, hk]

/-- For mean-zero coefficients, `Q_N` is exactly the strict high-mode mask. -/
theorem Q_eq_Qmask_of_zero_mode
    (N : ℕ) (a : SpectralCoeff E) (h0 : a (0, 0) = 0) :
    Q N a = Qmask N a := by
  funext k
  by_cases hk0 : k = (0, 0)
  · subst k
    simp [Q, Qmask, P, IsLowMode, IsHighMode, h0]
  · by_cases hle : waveSqNorm k ≤ lambda N
    · have hl : IsLowMode N k := ⟨hk0, hle⟩
      have hh : ¬ IsHighMode N k := by
        intro hh
        exact (not_lt_of_ge hle) hh.2
      simp [Q, Qmask, P, hl, hh]
    · have hh : IsHighMode N k := ⟨hk0, lt_of_not_ge hle⟩
      have hl : ¬ IsLowMode N k := by
        intro hl
        exact hle hl.2
      simp [Q, Qmask, P, hl, hh]

/-- Exact low/high decomposition. -/
theorem P_add_Q (N : ℕ) (a : SpectralCoeff E) :
    P N a + Q N a = a := by
  funext k
  simp [Q]

/-- Equivalent decomposition with the complementary term first. -/
theorem Q_add_P (N : ℕ) (a : SpectralCoeff E) :
    Q N a + P N a = a := by
  funext k
  simp [Q]

/-- The complementary projection is idempotent. -/
@[simp]
theorem Q_idem (N : ℕ) (a : SpectralCoeff E) :
    Q N (Q N a) = Q N a := by
  funext k
  by_cases hk : IsLowMode N k <;> simp [Q, P, hk]

/-- `P_N Q_N = 0`. -/
@[simp]
theorem P_Q_zero (N : ℕ) (a : SpectralCoeff E) :
    P N (Q N a) = 0 := by
  funext k
  by_cases hk : IsLowMode N k <;> simp [Q, P, hk]

/-- `Q_N P_N = 0`. -/
@[simp]
theorem Q_P_zero (N : ℕ) (a : SpectralCoeff E) :
    Q N (P N a) = 0 := by
  funext k
  by_cases hk : IsLowMode N k <;> simp [Q, P, hk]

/-- Pointwise form of the paper band projection. -/
theorem PBetween_apply_of_le {n N : ℕ} (hnN : n ≤ N)
    (a : SpectralCoeff E) (k : WaveVector) :
    PBetween N n a k =
      if k ≠ (0, 0) ∧ lambda n < waveSqNorm k ∧ waveSqNorm k ≤ lambda N
      then a k else 0 := by
  unfold PBetween P IsLowMode
  by_cases hk0 : k = (0, 0)
  · subst k
    simp
  by_cases hkn : waveSqNorm k ≤ lambda n
  · have hkN : waveSqNorm k ≤ lambda N :=
      hkn.trans (lambda_monotone hnN)
    simp [hk0, hkn, hkN, not_lt_of_ge hkn]
  · have hlt : lambda n < waveSqNorm k := lt_of_not_ge hkn
    by_cases hkN : waveSqNorm k ≤ lambda N
    · simp [hk0, hkn, hlt, hkN]
    · simp [hk0, hkn, hlt, hkN]

/-- If `n ≤ N`, the band projection is idempotent. -/
@[simp]
theorem PBetween_idem {n N : ℕ} (hnN : n ≤ N) (a : SpectralCoeff E) :
    PBetween N n (PBetween N n a) = PBetween N n a := by
  funext k
  by_cases hk :
      k ≠ (0, 0) ∧ lambda n < waveSqNorm k ∧ waveSqNorm k ≤ lambda N
  · simp [PBetween_apply_of_le hnN, hk]
  · simp [PBetween_apply_of_le hnN, hk]

/-- `P_n` kills the band `P_{N,n}`. -/
theorem P_small_PBetween_zero {n N : ℕ} (hnN : n ≤ N)
    (a : SpectralCoeff E) :
    P n (PBetween N n a) = 0 := by
  funext k
  by_cases hkn : IsLowMode n k
  · have hkN : IsLowMode N k := hkn.mono hnN
    simp [PBetween, P, hkn, hkN]
  · simp [PBetween, P, hkn]

/-- `P_N` acts as the identity on the `P_{N,n}` band. -/
theorem P_large_PBetween {n N : ℕ} (hnN : n ≤ N)
    (a : SpectralCoeff E) :
    P N (PBetween N n a) = PBetween N n a := by
  funext k
  by_cases hk :
      k ≠ (0, 0) ∧ lambda n < waveSqNorm k ∧ waveSqNorm k ≤ lambda N
  · have hkN : IsLowMode N k := ⟨hk.1, hk.2.2⟩
    simp [PBetween_apply_of_le hnN, P, hk, hkN]
  · by_cases hkN : IsLowMode N k
    · simp [PBetween_apply_of_le hnN, P, hk, hkN]
    · simp [PBetween_apply_of_le hnN, P, hk, hkN]

/-- Support of `P_N a` is contained in `D_{≤N}`. -/
theorem support_P_subset_DLE (N : ℕ) (a : SpectralCoeff E) :
    Function.support (P N a) ⊆ ↑(DLE N) := by
  intro k hk
  have hlow : IsLowMode N k := by
    by_contra hnot
    exact hk (P_apply_of_not_low hnot)
  exact (isLowMode_iff_mem_DLE (N := N) (k := k)).mp hlow

/-- Support of `P_{N,n}` lies in the expected spectral annulus. -/
theorem support_PBetween_subset {n N : ℕ} (hnN : n ≤ N)
    (a : SpectralCoeff E) :
    Function.support (PBetween N n a) ⊆
      {k : WaveVector |
        k ≠ (0, 0) ∧ lambda n < waveSqNorm k ∧ waveSqNorm k ≤ lambda N} := by
  intro k hk
  by_contra hnot
  have hnot' :
      ¬ (k ≠ (0, 0) ∧ lambda n < waveSqNorm k ∧ waveSqNorm k ≤ lambda N) := by
    simpa only [Set.mem_setOf_eq] using hnot
  apply hk
  rw [PBetween_apply_of_le hnN]
  simp [hnot']

end Additive

section Linear

variable {𝕜 E : Type*}
variable [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]

/-- `P_N` bundled as a linear map on coefficient fields. -/
noncomputable def PLinear (N : ℕ) :
    SpectralCoeff E →ₗ[𝕜] SpectralCoeff E where
  toFun := P N
  map_add' := by
    intro a b
    funext k
    by_cases hk : IsLowMode N k <;> simp [P, hk]
  map_smul' := by
    intro c a
    funext k
    by_cases hk : IsLowMode N k <;> simp [P, hk]

@[simp]
theorem PLinear_apply (N : ℕ) (a : SpectralCoeff E) :
    PLinear (𝕜 := 𝕜) N a = P N a :=
  rfl

/-- The range of `P_N` consists exactly of coefficient fields fixed by it. -/
theorem mem_range_PLinear_iff (N : ℕ) (a : SpectralCoeff E) :
    a ∈ LinearMap.range (PLinear (𝕜 := 𝕜) N) ↔ P N a = a := by
  constructor
  · rintro ⟨b, rfl⟩
    simp
  · intro ha
    exact ⟨a, ha⟩

end Linear

end BardosTartar
