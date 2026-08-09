import Mathlib

/-!
# Measure helpers for the non-extendability argument

These are deliberately generic.  The paper later needs only the elementary fact that a
countable union of null sets is null, together with its immediate subset and contrapositive
forms.
-/

namespace BardosTartar.Nonextendable

open Set
open MeasureTheory

variable {α : Type*} {ι : Sort*}

/--
A countable union of measure-zero sets has measure zero.

This is the measure-theoretic fact used in the proof of Theorem `eve` when the extendable
parameter set is covered by countably many exceptional sets.
-/
theorem measure_iUnion_eq_zero_of_forall
    [MeasurableSpace α] [Countable ι] (μ : Measure α) (s : ι → Set α)
    (hs : ∀ i, μ (s i) = 0) :
    μ (⋃ i, s i) = 0 :=
  MeasureTheory.measure_iUnion_null hs

/--
Any subset of a countable union of null sets is null.

This is the exact wrapper used later after proving that the set of extendable parameters is
contained in a countable union of null exceptional sets.
-/
theorem measure_eq_zero_of_subset_iUnion_null
    [MeasurableSpace α] [Countable ι] (μ : Measure α) (t : Set α) (s : ι → Set α)
    (ht : t ⊆ ⋃ i, s i) (hs : ∀ i, μ (s i) = 0) :
    μ t = 0 := by
  apply le_antisymm
  · calc
      μ t ≤ μ (⋃ i, s i) := measure_mono ht
      _ = 0 := MeasureTheory.measure_iUnion_null hs
  · exact bot_le

/--
If a countable union has nonzero measure, then at least one member has nonzero measure.

This is the elementary contrapositive form convenient for the final positive-measure
contradiction in the paper.
-/
theorem exists_measure_ne_zero_of_iUnion_ne_zero
    [MeasurableSpace α] [Countable ι] (μ : Measure α) (s : ι → Set α)
    (h : μ (⋃ i, s i) ≠ 0) :
    ∃ i, μ (s i) ≠ 0 := by
  by_contra hnone
  push Not at hnone
  exact h (MeasureTheory.measure_iUnion_null hnone)

end BardosTartar.Nonextendable
