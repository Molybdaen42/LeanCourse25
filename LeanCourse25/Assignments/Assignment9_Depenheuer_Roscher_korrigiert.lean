/-
# Overall Points: 20/20

* To see all points search for `TA Points` in this file

* To see all comments search for `TA Comment` in this file

-/

import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BigOperators Function Set Real Topology Filter
open ENNReal MeasureTheory Interval intervalIntegral
set_option linter.unusedVariables false
noncomputable section

/-! # Exercises to practice -/

-- **Submission of Nora Depenheuer and Joachim Roscher**

section

/- There are special cases of the change of variables theorems for affine transformations
(but you can also use the change of variable theorem from the lecture) -/
example (a b : ℝ) :
    ∫ x in a..b, sin (x / 2 + 3) =
    2 * cos (a / 2 + 3) - 2 * cos (b / 2  + 3) := by
  sorry
  done

/- Use the change of variables theorem for this exercise. -/
example (f : ℝ → ℝ) (s : Set ℝ) (hs : MeasurableSet s) :
    ∫ x in s, exp x * f (exp x) = ∫ y in exp '' s, f y := by
  sorry
  done

example (x : ℝ) : ∫ t in 0..x, t * exp t = (x - 1) * exp x + 1 := by
  sorry
  done

example (a b : ℝ) : ∫ x in a..b, 2 * x * exp (x ^ 2) =
    exp (b ^ 2) - exp (a ^ 2) := by
  sorry
  done


/- This is the last exercise from the lecture. -/
example (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∫ x in a..b, 1 / x + 1 / x ^ 2 =
  log b + 1 / a - log a - 1 / b := by
  have : 0 ∉ [[a, b]] := by sorry
  sorry
  done


/- Define tetration `n ↑↑ k = n^n^n^...^n` (`k` copies of `n`) on the natural numbers
recursively using `Nat.rec`. It is defined to be `1` when `k = 0`. -/

def tetration : ℕ → ℕ → ℕ :=
  fun n ↦ Nat.rec (motive := fun _ ↦ ℕ) 1
    (fun k tetr_k ↦ n ^ tetr_k)


-- Uncomment these to test whether your function is (probably) correct.
example : tetration 2 4 = 65536 := rfl
example : tetration 3 3 = 7625597484987 := rfl
example : tetration 5 1 = 5 := rfl
example : tetration 0 5 = 0 := rfl
example : tetration 5 0 = 1 := rfl
example : tetration 0 0 = 1 := rfl

/- In class we mentioned that if Disjunction could eliminate to
types, this would lead to a contradiction. Proof this.
Recall: `rfl` can prove that any two proofs of the same proposition are equal. -/
inductive Disjunction (P Q : Prop) : Prop where
  | left  : P → Disjunction P Q
  | right : Q → Disjunction P Q

open Disjunction
example
    (rec : ∀ (P Q : Prop) (motive : Disjunction P Q → Type)
      (h_left : ∀ hp : P, motive (left hp)) (h_right : ∀ hq : Q, motive (right hq))
      (h : Disjunction P Q), motive h)
    (comp_left : ∀ P Q motive h_left h_right (hp : P),
      rec P Q motive h_left h_right (left hp) = h_left hp)
    (comp_right : ∀ P Q motive h_left h_right (hq : Q),
      rec P Q motive h_left h_right (right hq) = h_right hq) : False := by
  sorry
  done

end


/-! # Exercises to hand in -/

/-
There are just two exercises to hand in.
Also work on your project.
-/

-- **TA Points: 10/10**
/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in 0..π, sin x * f (cos x) = ∫ y in -1..1, f y := by
  simp [intervalIntegral_eq_integral_uIoc, pi_nonneg, ← integral_Icc_eq_integral_Ioc]
  have hs : MeasurableSet (Icc 0 π) := measurableSet_Icc
  have hg' : ∀ x ∈ Icc 0 π, HasDerivWithinAt cos (-sin x) (Icc 0 π) x := by
    intro x hx
    apply HasDerivAt.hasDerivWithinAt
    exact hasDerivAt_cos x
    -- *TA Comment:* you can combine the last two lines into:
    -- `exact (hasDerivAt_cos x).hasDerivWithinAt`
  have hg : InjOn cos (Icc 0 π) := injOn_cos
  have h := integral_image_eq_integral_abs_deriv_smul hs hg' hg f
  simp [BijOn.image_eq bijOn_cos] at h
  rw [h]
  apply setIntegral_congr_fun hs
  simp [EqOn]
  intro x hx_nonneg hx_le_pi
  left
  exact (abs_eq_self.2 (sin_nonneg_of_nonneg_of_le_pi hx_nonneg hx_le_pi)).symm
  done


/-
In class we saw a definition of the Ackermann function.
Show that you can define this function just using `Nat.rec`
(without using pattern-matching notation), and show that it is equal
to the function defined by pattern matching.
When writing `Nat.rec`, give the `motive` explicitly using `Nat.rec (motive := ...)` -/

/- The Ackermann function, defined using pattern matching notation. -/
def A : ℕ → ℕ → ℕ
| 0,     n     => n + 1
| m + 1, 0     => A m 1
| m + 1, n + 1 => A m (A (m + 1) n)

-- **TA Points: 6/6**
def myA : ℕ → ℕ → ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ → ℕ) (fun n ↦ n+1)
    fun m Am ↦
      Nat.rec (motive := fun _ ↦ ℕ) (Am 1)
        fun n Amn ↦ Am Amn

-- **TA Pounts: 4/4**
example : A = myA := by
  apply funext₂
  intro m
  -- *TA Comment:* in case you don't know this: you can do `induction m generalizing m` if you have
  -- already introduced `m`
  induction m with
  | zero => simp [A, myA]
  | succ m hm =>
      intro n
      induction n with
      | zero => simp [A, myA, hm]
      | succ n hn => simp [A, myA, hn, hm]
  done
