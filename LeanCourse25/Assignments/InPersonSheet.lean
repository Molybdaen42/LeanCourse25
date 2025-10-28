import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.Util.Delaborators

section Functions

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ x, a ≤ f x

variable (f g : ℝ → ℝ) (a b : ℝ)

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  unfold FnLb
  intro x
  exact add_le_add (hfa x) (hgb x)

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  unfold FnLb
  intro x
  exact Left.mul_nonneg (nnf x) (nng x)

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  unfold FnUb
  intro x
  exact mul_le_mul (hfa x) (hgb x) (nng x) nna

def FnEven (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = f (-x)

def FnOdd (f : ℝ → ℝ) : Prop :=
  ∀ x, f x = -f (-x)

example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) := by
  unfold FnLb
  intro x
  exact add_le_add (hfa x) (hgb x)

example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 := by
  unfold FnLb
  intro x
  exact Left.mul_nonneg (nnf x) (nng x)

example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
    FnUb (fun x ↦ f x * g x) (a * b) := by
  unfold FnUb
  intro x
  exact mul_le_mul (hfa x) (hgb x) (nng x) nna

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
  exact Monotone.const_mul mf nnc

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by
  exact Monotone.comp mf mg

end Functions

section existential

def FnHasUb (f : ℝ → ℝ) :=
  ∃ a, FnUb f a

def FnHasLb (f : ℝ → ℝ) :=
  ∃ a, FnLb f a

variable {f g : ℝ → ℝ}

example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
  unfold FnHasLb
  obtain ⟨ a, ha⟩ := lbf
  obtain ⟨ b, hb⟩ := lbg
  use a+b
  unfold FnLb
  intro x
  exact add_le_add (ha x) (hb x)

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
  unfold FnHasUb
  obtain ⟨ a, ha⟩ := ubf
  use c*a
  unfold FnUb
  intro x
  exact mul_le_mul_of_nonneg_left (ha x) h

variable {α : Type*} [CommRing α]

def SumOfSquares (x : α) :=
  ∃ a b, x = a ^ 2 + b ^ 2

theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
    SumOfSquares (x * y) := by
  unfold SumOfSquares at sosx sosy ⊢
  obtain ⟨a,  b, hab⟩ := sosx
  obtain ⟨c,  d, hcd⟩ := sosy
  use (a*c+b*d)
  use (a*d-b*c)
  rw[hab,hcd]
  ring_nf

example {a b c : ℕ} (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
  exact (Nat.dvd_add_iff_right divab).mp divac

open Function

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
  exact mul_left_surjective₀ h

end existential

section negation

variable (f : ℝ → ℝ)

example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f := by
  unfold FnHasLb FnLb
  push_neg
  assumption

example : ¬FnHasUb fun x ↦ x := by
  unfold FnHasUb FnUb
  push_neg
  intro x
  use x+1
  norm_num

example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
  push_neg
  use fun x ↦ 0
  unfold Monotone
  simp
  use 1
  use 0
  simp

end negation

section conjunction

theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 := by
  have hx : x^2 ≥ 0 := sq_nonneg x
  have hy : y^2 ≥ 0 := sq_nonneg y
  apply sq_eq_zero_iff.1
  linarith

example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
  constructor
  · intro h
    constructor
    · exact aux h
    · rw [add_comm] at h
      exact aux h
  · intro ⟨hx,hy⟩
    simp [hx,hy]

theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
  unfold Monotone
  simp

example : ¬Monotone fun x : ℝ ↦ -x := by
  apply not_monotone_iff.2
  use 0
  use 1
  simp

end conjunction

section disjunction

-- use `eq_zero_or_eq_zero_of_mul_eq_zero` to prove the following

#check eq_zero_or_eq_zero_of_mul_eq_zero

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  have h' : (x-1)*(x+1)=0 := by
    ring_nf
    exact neg_add_eq_zero.mpr h.symm
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h'
  simp [sub_eq_zero, add_eq_zero_iff_eq_neg] at h'
  assumption

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  have h' : (x-y)*(x+y)=0 := by
    ring_nf
    exact sub_eq_zero_of_eq h
  apply eq_zero_or_eq_zero_of_mul_eq_zero at h'
  simp [sub_eq_zero, add_eq_zero_iff_eq_neg] at h'
  assumption

end disjunction
