/-
# Overall Points: 40/40

* To see all points search for `TA Points` in this file

* To see all comments search for `TA Comment` in this file

-/

import Mathlib.Analysis.Complex.Exponential

--import Mathlib
open Real Function Set Nat


-- **Submission of Nora Depenheuer and Joachim Roscher**

/-

* Hand in the solutions to the exercises below. Deadline: **Monday**, 10.11.2025 at **19:00**.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)



/-! # Exercises to hand-in. -/

-- **TA Points: 5/5**
/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by
  ext x
  constructor
  · intro ⟨⟨z,hzs,hfz⟩,hx⟩ -- *TA Comment:* very nice
    use z
    simp [hzs, hfz, hx]
    -- *TA Comment:* style: don't leave empty lines
  · intro ⟨z,⟨⟨hzs,hfzt⟩,hfz⟩⟩
    rw [←hfz] -- *TA Comment:* You could have added this to the `simp` below
    simp at hfzt ⊢
    /- *TA Comment:* You could do `refine ⟨?_, hfzt⟩` here.
    Or even `exact ⟨⟨z, ⟨hzs, rfl⟩⟩, hfzt⟩`. -/
    constructor
    · use z
    · exact hfzt
  done

-- **TA Points: 5/5**
/- Prove this without using lemmas from Mathlib. -/
example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
  ext y
  simp
  constructor
  · intro ⟨x,⟨i,hxAi⟩,hxy⟩
    use i
    use x -- *TA Comment:* You can combine the two `use`s: `use i, x`
  · intro ⟨i,x,⟨hxAi,hxy⟩⟩
    use x
    simp [hxy]
    use i
  done

-- **TA Points: 3/3**
/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by
  ext x
  simp
  have : (16 : ℝ) = 4^2 := by norm_num
  rw [this, sq_le_sq, le_abs']
  norm_num
  done

section

-- In class, we saw that Lean does not accept definitions like this:
-- def wrong : ℕ → ℕ
--  | n => 1 + wrong (n + 1)

-- **TA Points: 7/7**
-- In this case, you can actually derive a contradiction from a function with this property.
-- Do so in the following exercise.
-- (If you'd like a mathematical hint, scroll to the bottom of this file.)
example (f : ℕ → ℕ) (h : ∀ n : ℕ, f n = 1 + f (n + 1)) : False := by
  -- One can show via induction, that f(0) = n + f(n) holds for all n
  have hn : ∀ n : ℕ, f 0 = n + f n := by
    intro n
    induction n with
    | zero => norm_num
    | succ n hn =>
        rw [hn, h n]
        ring
  -- Then f(0) ≥ n for all n
  have hn' : ∀ n : ℕ, f 0 ≥ n := by
    intro n
    simp [hn n]
  -- and in particular, f(0) ≥ f(0) + 1.
  specialize hn' (f 0 + 1)
  -- Contradiction.
  simp at hn'
  done

-- **TA Points: 6/6**
/- Prove by induction that `∑_{i = 0}^{n} i^3 = (∑_{i=0}^{n} i) ^ 2`. -/
open Finset in
lemma sum_cube_eq_sq_sum (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℚ) ^ 3) = (∑ i ∈ Finset.range (n + 1), (i : ℚ)) ^ 2 := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [Finset.range_add_one]
      simp
      rw [hn, add_sq, add_left_inj]
      field_simp
      -- *TA Comment:* style: don't leave empty lines
      clear hn -- *TA Comment:* This isn't really needed, just name the `hn` below something else
      apply eq_add_of_sub_eq'

      -- Now it's just left to show little Gauß in ℚ
      induction n with
      | zero => simp
      | succ n hn =>
          rw [Finset.range_add_one]
          simp
          rw [mul_add, ← hn]
          ring
  done

end

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

-- **TA Points: 4/4**
lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by
  unfold SurjectiveFunction at *
  -- *TA Comment:* the above is not needed but I understand it can be helpful
  constructor
  · intro hgf y
    obtain ⟨x,hx⟩ := hgf y
    use (f x)
    assumption
  · intro hg y
    obtain ⟨z,hz⟩ := hg y
    obtain ⟨x,hx⟩ := hf z
    use x
    simp [hx,hz]
  done

-- **TA Points: 4/4**
/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by
  -- *TA Comment:* This is an interesting way to do this!
  let φ : ℝ → ℝ := fun x ↦ 2*x+1 -- outer function
  let ψ : ℝ → ℝ := fun x ↦ 3*(x+4) -- inner function

  -- They are both surjective
  have hφ : SurjectiveFunction φ := by
    intro y
    use (y - 1)/2
    ring
  have hψ : SurjectiveFunction ψ := by
    intro y
    use y/3 - 4
    ring

  -- Thus their composition is surjective
  exact (surjective_composition hψ).2 ((surjective_composition hf).2 hφ)
  done

-- **TA Points: 6/6**
/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by
  let R := {x | x ∉ f x}
  by_contra hf -- *TA Comment:* You could also do `intro hf` simply
  -- let x be a preimage of the set R
  obtain ⟨x,hx⟩ := hf R
  -- Then, x ∉ R iff x ∈ R
  have h : x ∉ R ↔ x ∈ R := by
    constructor <;>
    /- *TA Comment:* It might be nicer to write it like this:
      ( intro h
        simp [R]
        rw [hx]
        assumption)-/
    intro h <;>
    simp [R] <;>
    rw [hx] <;>
    assumption
  -- which is a contradiction
  exact not_iff_self h
  done

end Surjectivity

-- Hint for the exercise `contradictory_definition`:
-- use the hypothesis to study `f 0`: can you relate it to `f 1`, `f 2`, etc.?
-- Perhaps you can formulate a hypothesis and prove it by induction.
