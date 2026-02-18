import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.NullMeasurable

open Function Set Real Filter Topology TopologicalSpace MeasureTheory Metric Function

/-! # Exercises to practice -/

/- Here are a few example proofs: golf each one according to the ideas discussed in class.
Indicate which changes you made and why. -/

section example1

example {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by
  have ⟨t, t_sub_s, t_m, t_eq_s⟩ := h.exists_measurable_subset_ae_eq
  use t, t_sub_s, t_m
  constructor
  · exact measure_congr t_eq_s
  · exact ae_le_set.mp t_eq_s.symm.le

-- Your version
example {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by
  have ⟨t, t_sub_s, t_m, t_eq_s⟩ := h.exists_measurable_subset_ae_eq
  exact ⟨t, t_sub_s, t_m, measure_congr t_eq_s, ae_le_set.mp t_eq_s.symm.le⟩

end example1

-- Assume this is code proposed for inclusion into your library. It is likely written in non-ideal
-- ways. For instance, it might duplicate lemmas already in mathlib (in which case, you would prefer
-- to use the existing lemmas).
section example2

-- proven above; you don't need to golf this proof
lemma nullmeasurable_measurable_null {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by sorry

lemma measurable_null_nullmeasurable {s t : Set ℝ}
    (hm : NullMeasurableSet s) (hn : volume t = 0) : NullMeasurableSet (s ∪ t) :=
  NullMeasurableSet.union_null hm hn

lemma measurable_nullmeasurable {s : Set ℝ} (h : MeasurableSet s) : NullMeasurableSet s volume :=
  h.nullMeasurableSet

lemma shift_volume (s : Set ℝ) (c : ℝ) : volume ((fun x ↦ x + c) '' s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

lemma shift_nullmeasurable {s : Set ℝ} (h : NullMeasurableSet s volume) (c : ℝ) :
    NullMeasurableSet ((fun x ↦ x + c) '' s) volume := by
  rcases nullmeasurable_measurable_null h with ⟨t, ts, tm, vs, vt⟩
  rw [← union_diff_cancel ts, image_union]
  refine measurable_null_nullmeasurable ?_ ?_
  · have : MeasurableSet ((fun x ↦ x + c) '' t) := by
      apply (MeasurableEmbedding.measurableSet_image ?_).mpr tm
      exact measurableEmbedding_addRight c
    exact measurable_nullmeasurable this
  · rw [shift_volume (s \ t), vt]

end example2

-- Your version: copy-paste the code, clean it up and say what changes you made
namespace example2'

-- proven above; you don't need to golf this proof
lemma nullmeasurable_measurable_null {s : Set ℝ} (h : NullMeasurableSet s volume) :
    ∃ t ⊆ s, MeasurableSet t ∧ volume t = volume s ∧ volume (s \ t) = 0 := by sorry

-- `measurable_null_nullmeasurable` is unnecessary since it just duplicates
-- `NullMeasurableSet.union_null` with a slightly different name

-- `measurable_nullmeasurable` is unnecessary since it just duplicates
-- `MeasurableSet.nullMeasurableSet` with a different name

lemma shift_volume (s : Set ℝ) (c : ℝ) : volume ((fun x ↦ x + c) '' s) = volume s := by
  simp only [image_add_right, measure_preimage_add_right]

-- replace `measurable_null_nullmeasurable` by `NullMeasurableSet.union_null`
-- replace `measurable_nullmeasurable` by `MeasurableSet.nullMeasurableSet`
-- replace `MeasurableEmbedding.measurableSet_image` by `MeasurableEmbedding.measurableSet_image'`
-- because an `apply`-lemma is more fitting here
-- combine `MeasurableEmbedding.measurableSet_image'` with `measurableEmbedding_addRight`
-- using dot-notation
-- now the proof of `MeasurableSet ((fun x ↦ x + c) '' t)` is down to
-- `(measurableEmbedding_addRight c).measurableSet_image' tm`
-- put that proof into the final `exact` using dot notation
-- combine the `refine` and `exact`
-- make the `refine` into an `apply`
lemma shift_nullmeasurable {s : Set ℝ} (h : NullMeasurableSet s volume) (c : ℝ) :
    NullMeasurableSet ((fun x ↦ x + c) '' s) volume := by
  rcases nullmeasurable_measurable_null h with ⟨t, ts, tm, vs, vt⟩
  rw [← union_diff_cancel ts, image_union]
  apply ((measurableEmbedding_addRight c).measurableSet_image' tm).nullMeasurableSet.union_null
  rw [shift_volume (s \ t), vt]

end example2'

section example3

lemma volume_mono {s t : Set ℝ} (h : s ⊆ t) : volume s ≤ volume t := by
  exact OuterMeasureClass.measure_mono volume h

lemma union_volume_null {s t : Set ℝ} (hs : MeasurableSet s) (ht : volume t = 0) :
    volume (s ∪ t) = volume s := by
  have hu : s ∪ t = s ∪ (t \ s) := union_diff_self.symm
  have hd : Disjoint s (t \ s) := disjoint_sdiff_right
  have hz : volume (t \ s) = 0 := by
    apply le_antisymm
    · rw [← ht]
      exact volume_mono diff_subset
    · exact zero_le (volume (t \ s))
  rw [hu, measure_union' hd hs, hz]
  abel

end example3

-- Your version: copy-paste the code, clean it up and say what changes you made
namespace example3'

-- remove `volume_mono` because it just duplicates mathlib

-- use `measure_mono` instead of `volume_mono`
-- put the proof `hd` directly where it is needed
-- do the same for `hu`
-- add `add_zero` into the `rw` to remove `abel`
-- put `zero_le (volume (t \ s))` directly into the `apply`
lemma union_volume_null {s t : Set ℝ} (hs : MeasurableSet s) (ht : volume t = 0) :
    volume (s ∪ t) = volume s := by
  have hz : volume (t \ s) = 0 := by
    apply le_antisymm ?_ (zero_le (volume (t \ s)))
    rw [← ht]
    exact measure_mono diff_subset
  rw [← union_diff_self, measure_union' disjoint_sdiff_right hs, hz, add_zero]

end example3'


/- Take a lemma from your formalisation project and clean up its code in the same manner. -/
-- If you like to paste its code here, you may need to add additional imports at the top,
-- and also copy any necessary auxiliary lemmas.





/-
Take a theorem from your project that is a bit slow and investigate:
* can you make a guess which tactic(s) are slow?
* can you use the profiler to investigate?
* what are possible ways to speed this up?
-/






/-! # Exercises to hand in -/

/- There are **no graded exercises** this week: work on your formalisation projects,
do the practice exercises and review the last exercises in detail. -/


/-
This exercise is a **bonus exercise**: you may gain addition points if you need them.
Take a solution of yours on an old exercise and clean it up it using your current knowledge.
Make sure to take all feedback you got into account, but also use your own judgement.
-/
