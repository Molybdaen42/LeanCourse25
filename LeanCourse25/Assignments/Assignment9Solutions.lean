import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.JacobianOneDim

open BigOperators Function Set Real Topology Filter
open ENNReal MeasureTheory Interval intervalIntegral
set_option linter.unusedVariables false
noncomputable section


/-! # Exercises to hand in -/

/-
There are just two exercises to hand in.
Also work on your project.
-/

/- Prove the following using the change of variables theorem. -/
lemma change_of_variables_exercise (f : ℝ → ℝ) :
    ∫ x in 0..π, sin x * f (cos x) = ∫ y in -1..1, f y := by
  rw [intervalIntegral.integral_of_le (by positivity),
    intervalIntegral.integral_of_le (by norm_num), ← integral_Icc_eq_integral_Ioc,
    ← integral_Icc_eq_integral_Ioc]
  have : ∀ x ∈ Icc 0 π, HasDerivWithinAt cos (-sin x) (Icc 0 π) x := by
    intro x hx
    exact (hasDerivAt_cos x).hasDerivWithinAt
  rw [← bijOn_cos.image_eq, integral_image_eq_integral_abs_deriv_smul (measurableSet_Icc) this
    injOn_cos]
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  simp [abs_of_nonneg (sin_nonneg_of_mem_Icc hx)]


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

#check Nat.rec

/- `Am` corresponds to `A m` and `Bn` corresponds to `A (m + 1) n`. -/
def myA : ℕ → ℕ → ℕ := Nat.rec (motive := fun n ↦ ℕ → ℕ) Nat.succ
    (fun m Am ↦ Nat.rec (motive := fun n ↦ ℕ) (Am 1) (fun n Bn ↦ Am (Bn)))

example : A = myA := by
  ext n m
  induction n generalizing m with
  | zero => simp [A, myA]
  | succ n hn =>
    induction m with
    | zero => simp [A, myA, hn 1]
    | succ m hm => simp [A, myA, hm, hn]
