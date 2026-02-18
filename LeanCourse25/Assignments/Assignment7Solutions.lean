import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace

/-! # Exercises to hand in. -/

section GroupActions

variable (G : Type*) {X : Type*} [Group G] [MulAction G X]

/- Below is the orbit of an element `x ∈ X` w.r.t. a group action by `G`.
Prove that the orbits of two elements are equal
precisely when one element is in the orbit of the other. -/
def orbitOf (x : X) : Set X := range (fun g : G ↦ g • x)

lemma orbitOf_eq_iff (x y : X) : orbitOf G x = orbitOf G y ↔ y ∈ orbitOf G x := by
  constructor
  · intro h
    rw [h]
    use 1
    exact one_smul _ _
  · intro ⟨g, hg⟩
    ext z
    constructor
    · intro ⟨g', hg'⟩
      use g' * g⁻¹
      simp [← hg', ← hg, mul_smul]
    · intro ⟨g', hg'⟩
      use g' * g
      simp [← hg', ← hg, mul_smul]
  done

/- Define the stabilizer of an element `x` as the subgroup of elements
`g ∈ G` that satisfy `g • x = x`. -/
def stabilizerOf (x : X) : Subgroup G where
  carrier := {g | g • x = x}
  mul_mem' {a b} ha hb := by simp_all [mul_smul]
  one_mem' := by simp
  inv_mem' {a} ha := by simp_all [inv_smul_eq_iff]

-- This is a lemma that allows `simp` to simplify `x ≈ y` in the proof below.
@[simp] theorem leftRel_iff {x y : G} {s : Subgroup G} :
    letI := QuotientGroup.leftRel s; x ≈ y ↔ x⁻¹ * y ∈ s :=
  QuotientGroup.leftRel_apply

def forwardMap (x : X) : G ⧸ stabilizerOf G x → orbitOf G x :=
  Quotient.lift (fun g ↦ (⟨g • x, by use g⟩ : orbitOf G x))
    (by intro a b hab; simp_all [stabilizerOf, mul_smul, inv_smul_eq_iff])

/- Let's prove the orbit-stabilizer theorem.

Hint: Only define the forward map (as a separate definition),
and use `Equiv.ofBijective` to get an equivalence.
(Note that we are coercing `orbitOf G x` to a (sub)type in the right-hand side) -/
def orbit_stabilizer_theorem (x : X) : G ⧸ stabilizerOf G x ≃ orbitOf G x :=
  Equiv.ofBijective (forwardMap G x) (by
    constructor
    · apply Quotient.ind₂
      intro a b hab
      simp_all [forwardMap, QuotientGroup.eq, stabilizerOf, mul_smul, inv_smul_eq_iff]
    · intro ⟨a, g, hga⟩
      use ⟦g⟧
      simp [forwardMap, hga])

end GroupActions

section tendsto

/- Let's convince ourselves that convergence of a sequence and continuity at `x` as
defined in the lecture (and mathlib) correspond to the definitions we used in an analysis course. -/

/- Using these operations, we can define the limit. -/
def MyTendsto {X Y : Type*} (f : X → Y)
    (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

-- The following lemma will be very helpful.
#check mem_nhds_iff

-- You can assume this lemma for this exercise; you don't have to prove it.
-- (It is similar to the lemma `IsOpen.exists_Ioo_subset` in mathlib.)
lemma _root_.IsOpen.exists_Ioo_subset' {s : Set ℝ} {x : ℝ} (hs : IsOpen s) (hx : x ∈ s) :
    ∃ a b, a < b ∧ x ∈ Ioo a b ∧ Ioo a b ⊆ s := by
  sorry

example (u : ℕ → ℝ) (x : ℝ) : MyTendsto u atTop (𝓝 x) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - x| < ε := by
  simp only [MyTendsto]
  constructor
  · intro h ε hε
    have : ∃ N, ∀ n ≥ N, n ∈ u ⁻¹' (Ioo (x - ε) (x + ε)) := by
      simp_rw [le_def, mem_map, mem_atTop_sets] at h
      exact h (Ioo (x - ε) (x + ε)) (isOpen_Ioo.mem_nhds (by simp [hε]))
    simp_all [abs_sub_lt_iff, sub_lt_iff_lt_add, and_comm, add_comm]
  · intro h s hs
    -- Choose epsilon so an open interval around it is contained in s.
    have : ∃ ε, 0 < ε ∧ Ioo (x - ε) (x + ε) ⊆ s := by
      simp_rw [Metric.mem_nhds_iff, ball_eq_Ioo] at hs
      exact hs
    obtain ⟨ε, hε, hεs⟩ := this
    obtain ⟨N, hN⟩ := h ε hε
    rw [mem_map, mem_atTop_sets]
    use N
    intro n hn
    apply hεs
    simp_all [abs_sub_lt_iff, sub_lt_iff_lt_add, and_comm, add_comm]

-- The following exercise is a bonus exercise: any points you get here will be counted on top
-- of your regular points.
example (f : ℝ → ℝ) (x : ℝ) :
    Tendsto f (𝓝 x) (𝓝 (f x)) ↔ ∀ ε > 0, ∃ δ > 0, ∀ x y, |x - y| < δ → |f x - f y| < ε := by
  sorry

end tendsto

section indicator

#check Filter.Eventually.filter_mono
#check Filter.Eventually.mono

/- Here is a technical property using filters, characterizing when a 2-valued function converges to
a filter of the form `if q then F else G`. The next exercise is a more concrete application.
Useful lemmas here are
* `Filter.Eventually.filter_mono`
* `Filter.Eventually.mono` -/
lemma technical_filter_exercise {ι α : Type*} {p : ι → Prop} {q : Prop} {a b : α}
    {L : Filter ι} {F G : Filter α}
    (hbF : ∀ᶠ x in F, x ≠ b) (haG : ∀ᶠ x in G, x ≠ a) (haF : pure a ≤ F) (hbG : pure b ≤ G) :
    (∀ᶠ i in L, p i ↔ q) ↔
    Tendsto (fun i ↦ if p i then a else b) L (if q then F else G) := by
  have hab : a ≠ b := haF hbF
  rw [tendsto_iff_eventually]
  constructor
  · intro h r hFG
    filter_upwards [h] with i hi
    rw [hi]
    by_cases hq : q
    · simp [hq] at hFG ⊢
      exact haF hFG
    · simp [hq] at hFG ⊢
      exact hbG hFG
  · intro h
    by_cases hq : q
    · simp [hq] at h ⊢
      specialize h hbF
      filter_upwards [h] with i
      simp [hab]
    · simp [hq] at h ⊢
      specialize h haG
      filter_upwards [h] with i
      simp [hab.symm]
  done

/- To be more concrete, we can use the previous lemma to prove the following.
if we denote the characteristic function of `A` by `1_A`, and `f : ℝ → ℝ` is a function,
then  `f * 1_{s i}` tends to `f * 1_t` iff `x ∈ s i` is eventually equivalent to
`x ∈ t` for all `x`. (note that this does *not* necessarily mean that `s i = t` eventually).
`f * 1_t` is written `indicator t f` in Lean.
Useful lemmas for this exercise are `indicator_apply`, `apply_ite` and `tendsto_pi_nhds`. -/
lemma tendsto_indicator_iff {ι : Type*} {L : Filter ι} {s : ι → Set ℝ} {t : Set ℝ} {f : ℝ → ℝ}
    (ha : ∀ x, f x ≠ 0) :
    (∀ x, ∀ᶠ i in L, x ∈ s i ↔ x ∈ t) ↔
    Tendsto (fun i ↦ indicator (s i) f) L (𝓝 (indicator t f)) := by
  unfold indicator
  simp_rw [tendsto_pi_nhds, apply_ite 𝓝]
  apply forall_congr'
  intro x
  apply technical_filter_exercise
  · exact continuous_id.continuousAt.eventually_ne (ha x)
  · exact continuous_id.continuousAt.eventually_ne (ha x).symm
  · rw [pure_le_nhds_iff]
  · rw [pure_le_nhds_iff]
  done

end indicator
