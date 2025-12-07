import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

noncomputable section
open BigOperators Function Set Real Filter Classical Topology TopologicalSpace


-- **Submission of Nora Depenheuer and Joachim Roscher**


/-! # Exercises to practice -/

section

variable {X Y : Type*}

example [TopologicalSpace X] [TopologicalSpace Y] (f : X ≃ₜ Y) (x : X) : (𝓝 x).map f = 𝓝 (f x) := by
  apply le_antisymm
  · sorry
  · sorry -- prove this, using a calc block

end

example : Differentiable ℝ (fun x ↦ Real.exp (x ^ 2) * Real.sin (x ^ 5 + 3) - 2) := by
  simp
  exact Differentiable.mul (by simp) (by simp)

example (x : ℝ) :
    deriv (fun x ↦ Real.exp (x ^ 2)) x = 2 * x * Real.exp (x ^ 2) := by
  simp
  ring
  done

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] {n : ℕ∞} in
/- Prove this by combining the right lemmas from the library,
such as `IsBoundedBilinearMap.contDiff`. -/
example (L : E →L[𝕜] E →L[𝕜] E) (f g : E → E) (hf : ContDiff 𝕜 n f)
    (hg : ContDiff 𝕜 n g) :
    ContDiff 𝕜 n (fun z : E × E ↦ L (f z.1) (g z.2)) := by
  sorry
  done

section

variable (α : Type*)
  [ConditionallyCompleteLinearOrder α] [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α]

/-
In the next three exercises we will show that every continuous injective function `ℝ → ℝ` is
either strictly monotone or strictly antitone.

We start by proving a slightly harder version of the statement in class.
We generalize the real numbers to an arbitrary type `α`
that satisfies all the conditions required for the intermediate value theorem.
If you want to prove this by using the intermediate value theorem only once,
then use `intermediate_value_uIcc`.
`uIcc a b` is the unordered interval `[min a b, max a b]`.
Useful lemmas: `uIcc_of_le` and `mem_uIcc`. -/

lemma mono_exercise_part1 {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by
  sorry
  done

/- Now use this and the intermediate value theorem again
to prove that `f` is at least monotone on `[a, ∞)`. -/
lemma mono_exercise_part2 {f : α → α} (hf : Continuous f) (h2f : Injective f)
    {a b : α} (hab : a ≤ b) (h2ab : f a < f b) : StrictMonoOn f (Ici a) := by
  sorry
  done

/-
Now we can finish just by using the previous exercise multiple times.
In this proof we take advantage that we did the previous exercise for an arbitrary order,
because that allows us to apply it to `ℝ` with the reversed order `≥`.
This is called `OrderDual ℝ`. This allows us to get that `f` is also strictly monotone on
`(-∞, b]`.
Now finish the proof yourself.
You do not need to apply the intermediate value theorem in this exercise.
-/
lemma mono_exercise_part3 (f : ℝ → ℝ) (hf : Continuous f) (h2f : Injective f) :
    StrictMono f ∨ StrictAnti f := by
  have : ∀ {a b : ℝ} (hab : a ≤ b) (h2ab : f a < f b), StrictMonoOn f (Iic b) := by
    intro a b hab h2ab
    have := mono_exercise_part2 (OrderDual ℝ) hf h2f hab h2ab
    rw [strictMonoOn_dual_iff.symm] at this
    exact this
  sorry

end


/-! # Exercises to hand in -/

example {X : Type*} [MetricSpace X] {x : X} : ⋂ i ∈ {s : Set X | IsOpen s ∧ x ∈ s }, i = {x} := by
  ext y
  simp
  constructor
  · intro h
    specialize h (Metric.ball x (dist y x))
    simp at h
    assumption
  · intro h
    simp [h]
  done


/- This is a copy of `mono_exercise_part1` above. See the comments there for more info. -/
variable (α : Type*) [ConditionallyCompleteLinearOrder α]
  [TopologicalSpace α] [OrderTopology α] [DenselyOrdered α] in
lemma mono_exercise_part1_copy {f : α → α} (hf : Continuous f) (h2f : Injective f) {a b x : α}
    (hab : a ≤ b) (h2ab : f a < f b) (hx : a ≤ x) : f a ≤ f x := by
  have ha_lt_b : a < b := lt_of_le_of_ne hab fun a_1 => (ne_of_lt h2ab) (congrArg f a_1)
  by_contra hcontra
  rw [not_le] at hcontra
  -- suppose a ≤ x, a ≤ b s.t. f(x) < f(a) < f(b)
  -- Since f(a) ≠ f(x), we know that a < x
  have ha_lt_x : a < x := by
    have : f a ≠ f x := (ne_of_lt hcontra).symm
    exact lt_of_le_of_ne hx fun a_1 => this (congrArg f a_1)
  -- use the IVT on the interval uIcc x b
  have hIVT : uIcc (f x) (f b) ⊆ f '' uIcc x b :=
    intermediate_value_uIcc (Continuous.continuousOn hf)
  have : f a ∈ uIcc (f x) (f b) := by
    simp [mem_uIcc]; left; exact ⟨le_of_lt hcontra, le_of_lt h2ab⟩
  -- It gives us some x' ∈ uIcc x b with f(x') = f(a)
  obtain ⟨x',hx', hfx'_eq_fa⟩ := hIVT this
  -- This gives us a contradiction by injectivity of f:
  -- on the one hand, a ∈ uIcc x b...
  have : a = x' := h2f (h2f (congrArg f hfx'_eq_fa.symm))
  rw [← this] at hx'
  -- but on the other hand, a ∉ uIcc x b
  have hc2 : a ∉ uIcc x b := by exact notMem_uIcc_of_lt ha_lt_x ha_lt_b
  contradiction
  done

example (x y : ℝ) :
    let f := fun ((x,y) : ℝ × ℝ) ↦ x^2 + x * y
    fderiv ℝ f (x, y) (1, 0) = 2 * x + y := by
  simp
  rw [fderiv_fun_add, ContinuousLinearMap.add_apply]
  · congr
    · simp_rw [sq]
      rw [fderiv_fun_mul differentiableAt_fst differentiableAt_fst, fderiv_fst]
      simp [two_mul]
    · rw [fderiv_fun_mul differentiableAt_fst differentiableAt_snd, fderiv_fst, fderiv_snd]
      simp
  · simp
  · simp

section

/-
Let's prove that the absolute value function is not differentiable at 0.
You can do this by showing that the left derivative and the right derivative do exist,
but are not equal. We can state this with `HasDerivWithinAt`
To make the proof go through, we need to show that the intervals have unique derivatives.
An example of a set that doesn't have unique derivatives is the set `ℝ × {0}`
as a subset of `ℝ × ℝ`, since that set doesn't contains only points in the `x`-axis,
so within that set there is no way to know what the derivative of a function should be
in the direction of the `y`-axis.

The following lemmas will be useful
* `HasDerivWithinAt.congr`
* `uniqueDiffWithinAt_convex`
* `HasDerivWithinAt.derivWithin`
* `DifferentiableAt.derivWithin`.
-/

example : ¬ DifferentiableAt ℝ (fun x : ℝ ↦ |x|) 0 := by
  intro h
  have h1 : HasDerivWithinAt (fun x : ℝ ↦ |x|) 1 (Ici 0) 0 := by
    have : HasDerivWithinAt (id : ℝ → ℝ) 1 (Ici 0) 0 := hasDerivWithinAt_id 0 (Ici 0)
    exact HasDerivWithinAt.congr this (by norm_num) abs_zero
    done
  have h2 : HasDerivWithinAt (fun x : ℝ ↦ |x|) (-1) (Iic 0) 0 := by
    have : HasDerivWithinAt (-id : ℝ → ℝ) (-1) (Iic 0) 0 := by
      apply HasDerivWithinAt.neg
      exact hasDerivWithinAt_id 0 (Iic 0)
    apply HasDerivWithinAt.congr this (by norm_num) (by norm_num)
    done
  have h3 : UniqueDiffWithinAt ℝ (Ici (0 : ℝ)) 0 := by
    apply uniqueDiffWithinAt_convex (convex_Ici 0)
    all_goals simp
    done
  have h4 : UniqueDiffWithinAt ℝ (Iic (0 : ℝ)) 0 := by
    apply uniqueDiffWithinAt_convex (convex_Iic 0)
    all_goals simp
    done
  have := DifferentiableAt.derivWithin h h3
  rw [← DifferentiableAt.derivWithin h h4] at this
  rw [HasDerivWithinAt.derivWithin h1 h3] at this
  rw [HasDerivWithinAt.derivWithin h2 h4] at this
  norm_num at this
  end
