import Mathlib

/-!
# Elementary polynomial coefficient bounds

This file formalises the elementary interpolation estimate used in the appendix of
*The Bardos--Tartar Conjecture for the 2D Hyperviscous Navier--Stokes Equation*.

The paper's printed interval lemma is stated for arbitrary endpoints `a,b`, while its proof
uses the grid spacing `(b-a)/d`.  The mathematically correct nondegenerate statement assumes
`a < b`; see `FormalizationIssues.md`.  Degree zero is split off before the interpolation
argument, so no division by the degree is hidden in the proof.

The final compact-set estimate is factored through a `DudleyControl` hypothesis.  In the
integrated project that hypothesis is supplied by the cited Dudley/Remez declaration in
`Citations/PolynomialInequality.lean`; no literature result is reproved here.
-/

namespace BardosTartar.Nonextendable

open scoped BigOperators
open Set Finset Polynomial

/-- A polynomial is bounded by `M` on `E`. -/
def PolynomialBoundedOn (E : Set ℝ) (P : ℝ[X]) (M : ℝ) : Prop :=
  ∀ x ∈ E, |P.eval x| ≤ M

private noncomputable def interpolationGrid (a b : ℝ) (d i : ℕ) : ℝ :=
  a + (i : ℝ) * (b - a) / (d : ℝ)

private theorem interpolationGrid_mem_Icc
    {a b : ℝ} {d i : ℕ} (hab : a < b) (hd : 0 < d) (hi : i ≤ d) :
    interpolationGrid a b d i ∈ Icc a b := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hiR : (i : ℝ) ≤ d := by exact_mod_cast hi
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hratio0 : 0 ≤ (i : ℝ) / d := div_nonneg (Nat.cast_nonneg _) hdR.le
  have hratio1 : (i : ℝ) / d ≤ 1 := (div_le_one hdR).2 hiR
  have hmul0 : 0 ≤ ((i : ℝ) / d) * (b - a) := mul_nonneg hratio0 hgap.le
  have hmul1 : ((i : ℝ) / d) * (b - a) ≤ b - a := by
    nlinarith [mul_le_mul_of_nonneg_right hratio1 hgap.le]
  constructor <;> dsimp [interpolationGrid]
  · rw [show (i : ℝ) * (b - a) / d = ((i : ℝ) / d) * (b - a) by ring]
    linarith
  · rw [show (i : ℝ) * (b - a) / d = ((i : ℝ) / d) * (b - a) by ring]
    linarith

private theorem interpolationGrid_injOn
    {a b : ℝ} {d : ℕ} (hab : a < b) (hd : 0 < d) :
    Set.InjOn (interpolationGrid a b d) (↑(Finset.range (d + 1)) : Set ℕ) := by
  intro i hi j hj hij
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hstep : 0 < (b - a) / (d : ℝ) := div_pos (sub_pos.mpr hab) hdR
  have hijR : (i : ℝ) = (j : ℝ) := by
    dsimp [interpolationGrid] at hij
    have hfactor : ((i : ℝ) - (j : ℝ)) * ((b - a) / (d : ℝ)) = 0 := by
      calc
        ((i : ℝ) - (j : ℝ)) * ((b - a) / (d : ℝ))
            = (i : ℝ) * (b - a) / d - (j : ℝ) * (b - a) / d := by ring
        _ = 0 := by linarith
    rcases mul_eq_zero.mp hfactor with hzero | hzero
    · exact sub_eq_zero.mp hzero
    · exact (ne_of_gt hstep hzero).elim
  exact_mod_cast hijR

private theorem abs_interpolationGrid_le
    {a b : ℝ} {d i : ℕ} (hab : a < b) (hd : 0 < d) (hi : i ≤ d) :
    |interpolationGrid a b d i| ≤ |a| + |b| + 1 := by
  have hx := interpolationGrid_mem_Icc hab hd hi
  have hmax : |interpolationGrid a b d i| ≤ max |a| |b| := by
    rw [abs_le]
    constructor
    · have hna : -max |a| |b| ≤ a := by
        have : -|a| ≤ a := neg_abs_le a
        exact (neg_le_neg (le_max_left |a| |b|)).trans this
      exact hna.trans hx.1
    · have hb : b ≤ max |a| |b| := by
        have : b ≤ |b| := le_abs_self b
        exact this.trans (le_max_right _ _)
      exact hx.2.trans hb
  calc
    |interpolationGrid a b d i| ≤ max |a| |b| := hmax
    _ ≤ |a| + |b| + 1 := by
      apply max_le
      · linarith [abs_nonneg b]
      · linarith [abs_nonneg a]

/--
Coefficient bound for a product of linear factors whose roots lie in `[-A,A]`.
This is the numerator estimate in the paper's Lagrange interpolation proof.
-/
private theorem abs_coeff_prod_X_sub_C_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (v : ι → ℝ) (A : ℝ)
    (hA : 0 ≤ A) (hv : ∀ i ∈ s, |v i| ≤ A) (k : ℕ) :
    |(∏ i ∈ s, (X - C (v i))).coeff k| ≤ (1 + A) ^ s.card := by
  classical
  induction s using Finset.induction_on generalizing k with
  | empty =>
      simp only [Finset.prod_empty, Finset.card_empty, pow_zero, Polynomial.coeff_one]
      split_ifs <;> norm_num
  | @insert i s hi ih =>
      have hvi : |v i| ≤ A := hv i (by simp)
      have hvs : ∀ j ∈ s, |v j| ≤ A := by
        intro j hj
        exact hv j (by simp [hj])
      have hbase : 0 ≤ 1 + A := by linarith
      cases k with
      | zero =>
          rw [Finset.prod_insert hi, Polynomial.mul_coeff_zero, abs_mul]
          have hih := ih hvs 0
          have hlin : |(X - C (v i)).coeff 0| = |v i| := by simp
          rw [hlin]
          calc
            |v i| * |(∏ j ∈ s, (X - C (v j))).coeff 0|
                ≤ A * (1 + A) ^ s.card :=
                  mul_le_mul hvi hih (abs_nonneg _) hA
            _ ≤ (1 + A) * (1 + A) ^ s.card := by
                  exact mul_le_mul_of_nonneg_right (by linarith) (pow_nonneg hbase _)
            _ = (1 + A) ^ (insert i s).card := by
                  rw [Finset.card_insert_of_notMem hi, pow_succ]
                  ring
      | succ k =>
          rw [Finset.prod_insert hi, mul_comm, Polynomial.coeff_mul_X_sub_C]
          have hihk := ih hvs k
          have hihks := ih hvs (k + 1)
          calc
            |(∏ j ∈ s, (X - C (v j))).coeff k -
                (∏ j ∈ s, (X - C (v j))).coeff (k + 1) * v i|
                ≤ |(∏ j ∈ s, (X - C (v j))).coeff k| +
                    |(∏ j ∈ s, (X - C (v j))).coeff (k + 1) * v i| :=
                  abs_sub _ _
            _ = |(∏ j ∈ s, (X - C (v j))).coeff k| +
                    |(∏ j ∈ s, (X - C (v j))).coeff (k + 1)| * |v i| := by
                  rw [abs_mul]
            _ ≤ (1 + A) ^ s.card + (1 + A) ^ s.card * A := by
                  gcongr
            _ = (1 + A) ^ s.card * (1 + A) := by ring
            _ = (1 + A) ^ (insert i s).card := by
                  rw [Finset.card_insert_of_notMem hi, pow_succ]

private theorem factorial_product_controls_power
    {d i : ℕ} (hi : i ≤ d) :
    d ^ d ≤ 8 ^ d * i.factorial * (d - i).factorial := by
  have hchoose : d.choose i ≤ 2 ^ d := Nat.choose_le_two_pow d i
  have hfactorial : d.choose i * i.factorial * (d - i).factorial = d.factorial :=
    Nat.choose_mul_factorial_mul_factorial hi
  have hpow_choose : d ^ d ≤ 4 ^ d * d.factorial := by
    by_cases hd : d = 0
    · subst d
      simp
    · have hdpos : 0 < d := Nat.pos_of_ne_zero hd
      have hp := (Nat.pow_le_choose (α := ℝ) d (2 * d - 1))
      have hsub : 2 * d - 1 + 1 - d = d := by omega
      rw [hsub] at hp
      have hchoose2 : (2 * d - 1).choose d ≤ 2 ^ (2 * d - 1) :=
        Nat.choose_le_two_pow _ _
      have hchoose2R : ((2 * d - 1).choose d : ℝ) ≤ (2 : ℝ) ^ (2 * d - 1) := by
        exact_mod_cast hchoose2
      have htwo : (2 : ℝ) ^ (2 * d - 1) ≤ (4 : ℝ) ^ d := by
        calc
          (2 : ℝ) ^ (2 * d - 1) ≤ (2 : ℝ) ^ (2 * d) := by
            exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
          _ = ((2 : ℝ) ^ 2) ^ d := by rw [pow_mul]
          _ = (4 : ℝ) ^ d := by norm_num
      have hfacpos : (0 : ℝ) < d.factorial := by positivity
      have hcastchoose : ((2 * d - 1).choose d : ℝ) ≤ (4 : ℝ) ^ d :=
        hchoose2R.trans htwo
      have hp' : (d : ℝ) ^ d / d.factorial ≤ ((2 * d - 1).choose d : ℝ) := hp
      have hp'' : (d : ℝ) ^ d / d.factorial ≤ (4 : ℝ) ^ d := hp'.trans hcastchoose
      have : (d : ℝ) ^ d ≤ (4 : ℝ) ^ d * d.factorial :=
        (div_le_iff₀ hfacpos).mp hp''
      exact_mod_cast this
  calc
    d ^ d ≤ 4 ^ d * d.factorial := hpow_choose
    _ = 4 ^ d * (d.choose i * i.factorial * (d - i).factorial) := by rw [hfactorial]
    _ ≤ 4 ^ d * (2 ^ d * i.factorial * (d - i).factorial) := by
      gcongr
    _ = (4 ^ d * 2 ^ d) * i.factorial * (d - i).factorial := by ac_rfl
    _ = 8 ^ d * i.factorial * (d - i).factorial := by
      rw [← mul_pow]
      norm_num

/-- Product of the integer distances from `i` to all other indices in `0,…,d`. -/
private theorem prod_abs_cast_sub_eq_factorials
    {d i : ℕ} (hi : i ≤ d) :
    ∏ j ∈ (Finset.range (d + 1)).erase i, |(i : ℝ) - (j : ℝ)| =
      (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by
  classical
  have hirange : i ∈ Finset.range (d + 1) := by simp [Nat.lt_succ_iff, hi]
  have hsplit :
      (Finset.range (d + 1)).erase i = Finset.Ico 0 i ∪ Finset.Ico (i + 1) (d + 1) := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    omega
  rw [hsplit, Finset.prod_union]
  · have hleft :
        ∏ j ∈ Finset.Ico 0 i, |(i : ℝ) - (j : ℝ)| = (i.factorial : ℝ) := by
      calc
        ∏ j ∈ Finset.Ico 0 i, |(i : ℝ) - (j : ℝ)|
            = ∏ j ∈ Finset.Ico 0 i, ((i - j : ℕ) : ℝ) := by
                apply Finset.prod_congr rfl
                intro j hj
                have hji : j ≤ i := (Finset.mem_Ico.mp hj).2.le
                rw [abs_of_nonneg]
                · norm_num [Nat.cast_sub hji]
                · exact sub_nonneg.mpr (by exact_mod_cast hji)
        _ = (i.descFactorial i : ℝ) := by
              rw [Nat.descFactorial_eq_prod_range]
              norm_num [Finset.prod_Ico_eq_prod_range]
        _ = (i.factorial : ℝ) := by rw [Nat.descFactorial_self]
    have hright :
        ∏ j ∈ Finset.Ico (i + 1) (d + 1), |(i : ℝ) - (j : ℝ)| =
          ((d - i).factorial : ℝ) := by
      calc
        ∏ j ∈ Finset.Ico (i + 1) (d + 1), |(i : ℝ) - (j : ℝ)|
            = ∏ k ∈ Finset.range (d - i), ((k + 1 : ℕ) : ℝ) := by
                rw [Finset.prod_Ico_eq_prod_range]
                have hrange : d + 1 - (i + 1) = d - i := by omega
                rw [hrange]
                apply Finset.prod_congr rfl
                intro k hk
                have hik : i < i + 1 + k := by omega
                rw [abs_of_nonpos]
                · push_cast
                  ring
                · exact sub_nonpos.mpr (by exact_mod_cast hik.le)
        _ = ((d - i).factorial : ℝ) := by
              rw [← Nat.cast_prod]
              norm_num [Finset.prod_range_add_one_eq_factorial]
    rw [hleft, hright]
  · exact Finset.disjoint_left.2 (by
      intro j hj1 hj2
      have h1 := (Finset.mem_Ico.mp hj1).2
      have h2 := (Finset.mem_Ico.mp hj2).1
      omega)

private theorem abs_grid_denominator_eq
    {a b : ℝ} {d i : ℕ} (hab : a < b) (hd : 0 < d) (hi : i ≤ d) :
    |∏ j ∈ (Finset.range (d + 1)).erase i,
        (interpolationGrid a b d i - interpolationGrid a b d j)| =
      ((b - a) / d) ^ d * (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by
  classical
  have hid : i ∈ Finset.range (d + 1) := by simp [Nat.lt_succ_iff, hi]
  rw [abs_prod]
  have hcard : ((Finset.range (d + 1)).erase i).card = d := by simp [hid]
  calc
    ∏ j ∈ (Finset.range (d + 1)).erase i,
        |interpolationGrid a b d i - interpolationGrid a b d j|
        = ∏ j ∈ (Finset.range (d + 1)).erase i,
            (|(i : ℝ) - (j : ℝ)| * ((b - a) / d)) := by
              apply Finset.prod_congr rfl
              intro j hj
              have hstep : 0 ≤ (b - a) / (d : ℝ) :=
                (div_pos (sub_pos.mpr hab) (by exact_mod_cast hd)).le
              dsimp [interpolationGrid]
              rw [show
                a + (i : ℝ) * (b - a) / d - (a + (j : ℝ) * (b - a) / d) =
                  ((i : ℝ) - (j : ℝ)) * ((b - a) / d) by ring,
                abs_mul, abs_of_nonneg hstep]
    _ = (∏ j ∈ (Finset.range (d + 1)).erase i, |(i : ℝ) - (j : ℝ)|) *
          ∏ _j ∈ (Finset.range (d + 1)).erase i, ((b - a) / d) := by
            rw [Finset.prod_mul_distrib]
    _ = ((i.factorial : ℝ) * ((d - i).factorial : ℝ)) * ((b - a) / d) ^ d := by
          rw [prod_abs_cast_sub_eq_factorials hi]
          have hconst :
              ∏ _j ∈ (Finset.range (d + 1)).erase i, ((b - a) / d) =
                ((b - a) / d) ^ d := by
            rw [Finset.prod_const]
            simp [hcard]
          rw [hconst]
    _ = ((b - a) / d) ^ d * (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by ring

private theorem grid_denominator_lower_bound
    {a b : ℝ} {d i : ℕ} (hab : a < b) (hd : 0 < d) (hi : i ≤ d) :
    ((b - a) / 8) ^ d ≤
      |∏ j ∈ (Finset.range (d + 1)).erase i,
        (interpolationGrid a b d i - interpolationGrid a b d j)| := by
  rw [abs_grid_denominator_eq hab hd hi]
  have hnat := factorial_product_controls_power hi
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hnatR : (d : ℝ) ^ d ≤ (8 : ℝ) ^ d * i.factorial * (d - i).factorial := by
    exact_mod_cast hnat
  have hdPow : 0 < (d : ℝ) ^ d := pow_pos hdR _
  have h8 : 0 < (8 : ℝ) ^ d := by positivity
  rw [div_pow, div_pow]
  have hfactor : 0 ≤ (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by positivity
  have hrecip :
      (1 : ℝ) / (8 : ℝ) ^ d ≤
        ((i.factorial : ℝ) * ((d - i).factorial : ℝ)) / (d : ℝ) ^ d := by
    apply (div_le_div_iff₀ h8 hdPow).2
    simpa [mul_assoc, mul_left_comm, mul_comm] using hnatR
  have hgapPow : 0 ≤ (b - a) ^ d := pow_nonneg hgap.le _
  calc
    (b - a) ^ d / (8 : ℝ) ^ d =
        (b - a) ^ d * ((1 : ℝ) / (8 : ℝ) ^ d) := by ring
    _ ≤ (b - a) ^ d *
        (((i.factorial : ℝ) * ((d - i).factorial : ℝ)) / (d : ℝ) ^ d) :=
          mul_le_mul_of_nonneg_left hrecip hgapPow
    _ = (b - a) ^ d / (d : ℝ) ^ d *
        (i.factorial : ℝ) * ((d - i).factorial : ℝ) := by ring

private theorem succ_le_two_pow {d : ℕ} (hd : 0 < d) : d + 1 ≤ 2 ^ d := by
  induction d with
  | zero => omega
  | succ d ih =>
      by_cases hz : d = 0
      · subst d
        norm_num
      · have hdpos : 0 < d := Nat.pos_of_ne_zero hz
        have hih := ih hdpos
        rw [pow_succ]
        omega

/--
Paper Lemma `poly` (Appendix, “Polynomial coefficient bound”), with the necessary
nondegeneracy hypothesis `a < b` made explicit.

For every nondegenerate compact interval there is `C > 0`, depending only on its endpoints,
such that every coefficient of every degree-`≤ d` real polynomial is bounded by `C^d` times
the supremum bound on that interval.
-/
theorem polynomial_coefficient_bound_interval (a b : ℝ) (hab : a < b) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (d : ℕ) (P : ℝ[X]) (M : ℝ), P.natDegree ≤ d → 0 ≤ M →
        PolynomialBoundedOn (Icc a b) P M →
        ∀ k : ℕ, |P.coeff k| ≤ C ^ d * M := by
  classical
  let A : ℝ := |a| + |b| + 1
  let C0 : ℝ := max 1 (16 * (1 + A) / (b - a))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC0 : 0 < C0 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨C0, hC0, ?_⟩
  intro d P M hdeg hM hbound k
  by_cases hd0 : d = 0
  · subst d
    have hPC : P = C (P.coeff 0) := Polynomial.eq_C_of_natDegree_le_zero hdeg
    by_cases hk : k = 0
    · subst k
      have ha_mem : a ∈ Icc a b := ⟨le_rfl, hab.le⟩
      have heval := hbound a ha_mem
      rw [hPC] at heval
      simpa using heval
    · rw [hPC, Polynomial.coeff_C_of_ne_zero hk]
      simpa using hM
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    let s : Finset ℕ := Finset.range (d + 1)
    let x : ℕ → ℝ := interpolationGrid a b d
    have hxs : Set.InjOn x (↑s : Set ℕ) := by
      simpa [s, x] using interpolationGrid_injOn hab hd
    have hdegree_le : P.degree ≤ (d : WithBot ℕ) :=
      Polynomial.degree_le_of_natDegree_le hdeg
    have hdegree : P.degree < (s.card : WithBot ℕ) := by
      simpa [s] using hdegree_le.trans_lt (show (d : WithBot ℕ) < d + 1 by exact_mod_cast Nat.lt_succ_self d)
    have hinterp : P = (Lagrange.interpolate s x) (fun i => P.eval (x i)) :=
      Lagrange.eq_interpolate hxs hdegree
    have hsum :
        P = ∑ i ∈ s,
          C (P.eval (x i) / ∏ j ∈ s.erase i, (x i - x j)) *
            ∏ j ∈ s.erase i, (X - C (x j)) := by
      calc
        P = (Lagrange.interpolate s x) (fun i => P.eval (x i)) := hinterp
        _ = ∑ i ∈ s,
            C (P.eval (x i) / ∏ j ∈ s.erase i, (x i - x j)) *
              ∏ j ∈ s.erase i, (X - C (x j)) := by
                exact Lagrange.interpolate_eq_sum (s := s) (v := x)
                  (fun i => P.eval (x i))
    have hcoeffsum := congrArg (fun Q : ℝ[X] => Q.coeff k) hsum
    simp only [Polynomial.finsetSum_coeff] at hcoeffsum
    have hterm : ∀ i ∈ s,
        |(C (P.eval (x i) / ∏ j ∈ s.erase i, (x i - x j)) *
            ∏ j ∈ s.erase i, (X - C (x j))).coeff k| ≤
          M * (8 / (b - a)) ^ d * (1 + A) ^ d := by
      intro i hi
      have hi_le : i ≤ d := by simpa [s, Nat.lt_succ_iff] using hi
      have hxi_mem : x i ∈ Icc a b := by
        simpa [x] using interpolationGrid_mem_Icc hab hd hi_le
      have hPi : |P.eval (x i)| ≤ M := hbound _ hxi_mem
      have hdenlower : ((b - a) / 8) ^ d ≤
          |∏ j ∈ s.erase i, (x i - x j)| := by
        simpa [s, x] using grid_denominator_lower_bound hab hd hi_le
      have hdenpos : 0 < |∏ j ∈ s.erase i, (x i - x j)| := by
        have hbase : 0 < (b - a) / 8 := div_pos (sub_pos.mpr hab) (by norm_num)
        exact lt_of_lt_of_le (pow_pos hbase d) hdenlower
      have hscalar :
          |P.eval (x i) / ∏ j ∈ s.erase i, (x i - x j)| ≤
            M * (8 / (b - a)) ^ d := by
        rw [abs_div]
        have hrecip : 1 / |∏ j ∈ s.erase i, (x i - x j)| ≤ (8 / (b - a)) ^ d := by
          have hgap : 0 < b - a := sub_pos.mpr hab
          have hleftpos : 0 < ((b - a) / 8) ^ d := pow_pos (div_pos hgap (by norm_num)) _
          have hinv := one_div_le_one_div_of_le hleftpos hdenlower
          calc
            1 / |∏ j ∈ s.erase i, (x i - x j)|
                ≤ 1 / (((b - a) / 8) ^ d) := hinv
            _ = (1 / ((b - a) / 8)) ^ d := by rw [one_div_pow]
            _ = (8 / (b - a)) ^ d := by
              congr 1
              field_simp [ne_of_gt hgap]
        calc
          |P.eval (x i)| / |∏ j ∈ s.erase i, (x i - x j)|
              = |P.eval (x i)| * (1 / |∏ j ∈ s.erase i, (x i - x j)|) := by ring
          _ ≤ M * (8 / (b - a)) ^ d :=
            mul_le_mul hPi hrecip (by positivity) hM
      have hxA : ∀ j ∈ s.erase i, |x j| ≤ A := by
        intro j hj
        have hjrange : j ∈ s := Finset.mem_of_mem_erase hj
        have hjle : j ≤ d := by simpa [s, Nat.lt_succ_iff] using hjrange
        simpa [x, A] using abs_interpolationGrid_le hab hd hjle
      have hnum := abs_coeff_prod_X_sub_C_le (s.erase i) x A hA hxA k
      have hcard : (s.erase i).card = d := by
        have : i ∈ s := hi
        simp [s, this]
      rw [hcard] at hnum
      rw [Polynomial.coeff_C_mul, abs_mul]
      have hscalarUpper : 0 ≤ M * (8 / (b - a)) ^ d := by
        exact mul_nonneg hM (pow_nonneg (by positivity) _)
      exact mul_le_mul hscalar hnum (abs_nonneg _) hscalarUpper
    have hsumabs :
        |∑ i ∈ s,
          (C (P.eval (x i) / ∏ j ∈ s.erase i, (x i - x j)) *
            ∏ j ∈ s.erase i, (X - C (x j))).coeff k| ≤
          (s.card : ℝ) * (M * (8 / (b - a)) ^ d * (1 + A) ^ d) := by
      calc
        |∑ i ∈ s,
          (C (P.eval (x i) / ∏ j ∈ s.erase i, (x i - x j)) *
            ∏ j ∈ s.erase i, (X - C (x j))).coeff k|
            ≤ ∑ i ∈ s,
                |(C (P.eval (x i) / ∏ j ∈ s.erase i, (x i - x j)) *
                  ∏ j ∈ s.erase i, (X - C (x j))).coeff k| := by
                  exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ s, (M * (8 / (b - a)) ^ d * (1 + A) ^ d) := by
              exact Finset.sum_le_sum (fun i hi => hterm i hi)
        _ = (s.card : ℝ) * (M * (8 / (b - a)) ^ d * (1 + A) ^ d) := by simp
    have hcardnat : s.card ≤ 2 ^ d := by
      simpa [s] using succ_le_two_pow hd
    have hcardpow : (s.card : ℝ) ≤ (2 : ℝ) ^ d := by
      exact_mod_cast hcardnat
    have hbaseC : 16 * (1 + A) / (b - a) ≤ C0 := le_max_right _ _
    have hbaseNonneg : 0 ≤ 16 * (1 + A) / (b - a) := by positivity
    have hpowC : (16 * (1 + A) / (b - a)) ^ d ≤ C0 ^ d :=
      pow_le_pow_left₀ hbaseNonneg hbaseC d
    have hbaseeq :
        (2 : ℝ) ^ d * ((8 / (b - a)) ^ d * (1 + A) ^ d) =
          (16 * (1 + A) / (b - a)) ^ d := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      field_simp [ne_of_gt (sub_pos.mpr hab)]
      ring
    calc
      |P.coeff k| = |∑ i ∈ s,
          (C (P.eval (x i) / ∏ j ∈ s.erase i, (x i - x j)) *
            ∏ j ∈ s.erase i, (X - C (x j))).coeff k| := by rw [hcoeffsum]
      _ ≤ (s.card : ℝ) * (M * (8 / (b - a)) ^ d * (1 + A) ^ d) := hsumabs
      _ ≤ (2 : ℝ) ^ d * (M * (8 / (b - a)) ^ d * (1 + A) ^ d) := by
            exact mul_le_mul_of_nonneg_right hcardpow (by positivity)
      _ = (16 * (1 + A) / (b - a)) ^ d * M := by
            calc
              (2 : ℝ) ^ d * (M * (8 / (b - a)) ^ d * (1 + A) ^ d) =
                  M * ((2 : ℝ) ^ d * ((8 / (b - a)) ^ d * (1 + A) ^ d)) := by ring
              _ = M * (16 * (1 + A) / (b - a)) ^ d := by rw [hbaseeq]
              _ = (16 * (1 + A) / (b - a)) ^ d * M := by ring
      _ ≤ C0 ^ d * M := mul_le_mul_of_nonneg_right hpowC hM

/--
The exact interface Agent E needs from the cited Dudley/Remez inequality: a sup bound on a
closed positive-measure subset controls the sup bound on its containing compact interval with
an exponential-in-degree loss.
-/
def DudleyControl (E : Set ℝ) (a b K : ℝ) : Prop :=
  0 < K ∧ E ⊆ Icc a b ∧
    ∀ (d : ℕ) (P : ℝ[X]) (M : ℝ), P.natDegree ≤ d → 0 ≤ M →
      PolynomialBoundedOn E P M →
      PolynomialBoundedOn (Icc a b) P (K ^ d * M)

/--
Paper Lemma `bigpoly` (Appendix, “Polynomial coefficient bound”), after supplying the cited
Dudley/Remez estimate for `E`.

This theorem contains exactly the paper-original deduction: combine the interval coefficient
bound with the externally cited sup-norm comparison.  The citation itself belongs in
`Citations/PolynomialInequality.lean`.
-/
theorem polynomial_coefficient_bound_of_dudley
    {E : Set ℝ} {a b KD : ℝ} (hab : a < b) (hD : DudleyControl E a b KD) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (d : ℕ) (P : ℝ[X]) (M : ℝ), P.natDegree ≤ d → 0 ≤ M →
        PolynomialBoundedOn E P M →
        ∀ k : ℕ, |P.coeff k| ≤ K ^ d * M := by
  obtain ⟨CI, hCI, hinterval⟩ := polynomial_coefficient_bound_interval a b hab
  refine ⟨CI * KD, mul_pos hCI hD.1, ?_⟩
  intro d P M hdeg hM hE k
  have hDinterval := hD.2.2 d P M hdeg hM hE
  have hIM : 0 ≤ KD ^ d * M := mul_nonneg (pow_nonneg hD.1.le _) hM
  have hcoeff := hinterval d P (KD ^ d * M) hdeg hIM hDinterval k
  calc
    |P.coeff k| ≤ CI ^ d * (KD ^ d * M) := hcoeff
    _ = (CI * KD) ^ d * M := by ring

end BardosTartar.Nonextendable
