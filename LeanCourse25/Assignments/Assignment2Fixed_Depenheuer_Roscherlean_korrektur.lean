/-
# Overall Points: 40/40

* To see all points search for `TA Points` in this file

* To see all comments search for `TA Comment` in this file

-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.FieldTheory.Finite.Basic

open Real Function Set Nat

/-

* Hand in the solutions to the exercises below. Deadline: 30.10.2025 at 10:00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

example (p q r s : Prop) (h : p ∧ q → r) (hp : p) (h' : q → s) : q → r ∧ s := by
  intro hq
  constructor
  apply h
  constructor
  exact hp
  exact hq
  apply h'
  exact hq

example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by
  intro h'
  obtain ⟨x, hx⟩  := h'
  use x
  specialize h x hx
  exact h

-- Exercise: prove this by contraposition.
example : 2 ≠ 4 → 1 ≠ 2 := by
  contrapose
  simp

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by
  constructor
  · intro h x hpx
    apply h
    use x
  · intro h ⟨x,hpx⟩
    exact h x hpx

/- Prove the following with basic tactics,
in particular without using `tauto`, `grind` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by
  constructor
  · intro ⟨x, hx, hr⟩
    constructor
    use x
    assumption
  · intro ⟨⟨x,hpx⟩,hr⟩
    use x

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by
  constructor
  · intro ⟨x,hx⟩
    by_contra h
    exact h x hx
  · intro h
    by_contra h'
    apply h
    intro x hpx
    apply h'
    use x

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by
  unfold SequentialLimit
  intro ε hε
  use 0
  intro n hn
  simp
  assumption

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by
  apply factorial_dvd_factorial
  linarith

example (a b c x y : ℝ) (h : a ≤ b) (h2 : b < c) (h3 : x ≤ y) :
    a + exp x ≤ c + exp (y + 2) := by
  have h' : exp x ≤ exp (y+2) := by
    rw [exp_le_exp]
    linarith
  linarith

-- Use `rw?` or `rw??` to help you in the following calculation.
-- Alternatively, write out a calc block by hand.
example {G : Type*} [Group G] {a b c d : G}
    (h : a⁻¹ * b * c * c⁻¹ * a * b⁻¹ * a * a⁻¹ = b) (h' : b * c = c * b) : b = 1 := by
  -- first try
  simp at h
  rw [← h]
  -- ????
  sorry


/-- Prove the following using `linarith`.
Note that `linarith` cannot deal with implication or if and only if statements. -/
example (a b c : ℝ) : a + b ≤ c ↔ a ≤ c - b := by
  constructor
  · intro h
    linarith
  · intro h
    linarith


/- You can prove many equalities and inequalities by being smart with calculations.
In this case `linarith` can also prove this, but `calc` can be a lot more flexible. -/
example {x y : ℝ} (hx : x + 3 ≤ 2) (hy : y + 2 * x ≥ 3) : y > 3 := by
  calc
    y = y + 2 * x - 2 * x := by ring
    _ ≥ 3 - 2 * x := by gcongr
    _ = 9 - 2 * (x + 3) := by ring
    _ ≥ 9 - 2 * 2 := by gcongr
    _ > 3 := by norm_num

/-- It can be useful to add a `+ 0` in a calculational proof for `gcongr` -/
example {m n : ℤ} : n ≤ n + m ^ 2 := by
  -- gcongr doesn't make progress here
  calc
    n = n + 0 := by ring
    _ ≤ n + m ^ 2 := by gcongr; exact sq_nonneg m

/- Sometimes `congr`/`gcongr` goes too deep into a term.
In that case, you can give `gcongr` a pattern with how deep it should enter the terms.
When the pattern contains `?_`, it creates a subgoal with the corresponding terms
on each side of the inequality.
For `congr` you can also do this using the tactic `congrm`. -/
example {a₁ a₂ b₁ b₂ c₁ c₂ : ℝ} (hab : a₁ + a₂ = b₁ + b₂) (hbc : b₁ + b₂ ≤ c₁ + c₂) :
    a₁ + a₂ + 1 ≤ c₁ + c₂ + 1 := by
  calc a₁ + a₂ + 1 = b₁ + b₂ + 1 := by congrm ?_ + 1; exact hab
    _ ≤ c₁ + c₂ + 1 := by gcongr ?_ + 1 -- gcongr automatically applies `hbc`.


example {m n : ℤ} : n - m ^ 2 ≤ n + 3 := by
  have : -m^2 ≤ 0 := by
    simp
    exact sq_nonneg m
  linarith


example {a : ℝ} (h : ∀ b : ℝ, a ≥ -3 + 4 * b - b ^ 2) : a ≥ 1 := by
  specialize h 2
  norm_num at h
  assumption



/-! # Exercises to hand-in. -/

section Logic
-- Prove the following statements with basic tactics,
-- in particular without using `tauto`, `grind` or lemmas from mathlib.

/-- The function`f : ℝ → ℝ` is continuous at `x₀`.-/
def ContinuousAtPoint (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| < δ → |f x - f x₀| < ε

def Continuous' (f : ℝ → ℝ) := ∀ x, ContinuousAtPoint f x

-- **TA Points: 2/2**
-- Exercise for you. Remember that you can use `unfold` to expand a definition.
example (f g : ℝ → ℝ) (hfg : ∀ x, ContinuousAtPoint f x ↔ ContinuousAtPoint g x) :
    Continuous' f ↔ Continuous' g := by
  unfold Continuous'
  constructor
  · intro h x
    specialize hfg x -- *TA Comment:* You don't need this
    specialize h x
    rw[← hfg]
    exact h -- *TA Comment:* You could do `exact h x` here instead of the `specialize` above
  intro h x -- *TA Comment:* stylistically it would be better to also have a `·` here
  specialize hfg x
  specialize h x
  rw[hfg]
  exact h

def All (p : ℝ → Prop) := ∀ x, p x

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    All p ↔ All q := by
  unfold All
  simp_rw [h]

example (p q : ℝ → Prop) (h : ∀ x, p x ↔ q x) :
    (∃ x, p x) ↔ (∃ x, q x) := by
  simp_rw [h]

-- Is the following true? If yes, prove it in Lean.
-- If not, give a counterexample and prove it. (What do you have to do to do so?)
example (p q : ℕ → Prop) (h: (∃ x, p x) ↔ (∃ x, q x)) : ∀ x, p x ↔ q x := by
  -- It's not true. A counterexample is: p(n) = true iff n=0 and q(n) = true iff n=1.
  sorry

-- **TA Points: 5/5**
example : ¬∀ (p q : ℕ → Prop), ((h: (∃ x, p x) ↔ (∃ x, q x)) → ∀ x, p x ↔ q x) := by
  -- define some counterexamples p and q
  let p : ℕ → Prop := fun n => (n=0)
  let q : ℕ → Prop := fun n => (n=1)
  push_neg
  use p
  use q

  constructor
  · -- show that (∃ x, p x) ↔ ∃ x, q x
    -- it's trivial since both sides are true
    have hp : ∃ x, p x := by use 0
    have hq : ∃ x, q x := by use 1
    simp [hp, hq]
  · -- show that ∃ x, p x ∧ ¬q x ∨ ¬p x ∧ q x
    use 0
    simp [p,q]

-- **TA Points: 3/3**
/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by
  constructor
  · intro h
    obtain ⟨ x, hp | hq⟩ := h
    · left
      use x
    · right
      use x
  · intro h
    obtain  hp| hq := h
    · obtain ⟨ x ,hx⟩ := hp
      use x
      left
      exact hx
    · obtain ⟨ x, hx⟩ := hq
      use x
      right
      exact hx

end Logic

section Functions

-- Let us investigate the function example from the lecture further.

-- This is how to say "a natural number p is prime" in mathlib.
#check Nat.Prime

-- The following theorem is the key ingredient to it.
-- (You have not seen the syntax `[hp: Fact (Nat.Prime p)]` yet: this is related to implicit
-- arguments.
--  You can assume it says `(hp: Nat.Prime p)`. We will discuss the precise difference later.)
--
-- Use `exact?`, `apply?` or `rw??` to find this theorem in mathlib.
-- Describe what you are doing.
-- **TA Points: 1/1**
example (p : ℕ) [hp: Fact (Nat.Prime p)] (x : ZMod p) : x ^ p = x := by
  -- using `exact?`, we get
  exact ZMod.pow_card x

-- The above theorem has a name. What is it?
-- Use this name to find the same result using leansearch.net.
-- Describe every step you're performing.
/--
Typing `(x : ZMod p) : x ^ p = x` intro `leansearch.net` yields an exact match at second position
(at first position in the output was `Generalized Fermat's Little Theorem in ℤ/pℤ`)
with the title `Fermat's Little Theorem in ℤ/pℤ`.
-/

-- Use `rw??` to find the following theorem in mathlib.
-- **TA Points: 1/1**
example (p : ℕ) [hp: Fact (Nat.Prime p)] (k : ZMod p) (hk : k ≠ 0) : k ^ (p - 1) = 1 := by
  exact ZMod.pow_card_sub_one_eq_one hk

-- **TA Points: 3/3**
-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] :
    (fun k ↦ k ^ p + 2 * k ^ (2 * (p - 1) + 1) : ZMod p → ZMod p) = (fun k ↦ 3 * k) := by
  ext k

  by_cases hk : k = 0
  · simp [hk]
  · -- if k ≠ 0, we can use Fermat's Little Theorem in ℤ/pℤ
    simp [pow_add, pow_mul', ZMod.pow_card_sub_one_eq_one hk]
    ring

-- **TA Points: 3/3**
-- Prove the following.
example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (3 * (p - 1) + 1) = k := by
  by_cases hk : k = 0
  · simp [hk]
  · -- if k ≠ 0, we can use Fermat's Little Theorem in ℤ/pℤ
    simp [pow_add, pow_mul', ZMod.pow_card_sub_one_eq_one hk]

-- **TA Points: 2/2**
example (p : ℕ) [Fact (Nat.Prime p)] (k : ZMod p) : k ^ (5 * (p - 1) + 1) = k := by
  by_cases hk : k = 0
  · simp [hk]
  · -- if k ≠ 0, we can use Fermat's Little Theorem in ℤ/pℤ
    simp [pow_add, pow_mul', ZMod.pow_card_sub_one_eq_one hk]

end Functions


-- **TA Points: 4/4**
/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by
  unfold SequentialLimit at hs ht ⊢
  intro ε hε

  -- divide ε in half
  obtain ⟨Ns,hNs⟩ := hs (ε/2) (half_pos hε)
  obtain ⟨Nt,hNt⟩ := ht (ε/2) (half_pos hε)
  use max Ns Nt

  intro n hn
  specialize hNs n (le_of_max_le_left hn)
  specialize hNt n (le_of_max_le_right hn)

  calc
    |s n + t n - (a + b)| = |s n - a + (t n - b)| := by ring_nf
                        _ ≤ |s n - a| + |t n - b| := by apply abs_add_le
                        _ < ε                     := by linarith

-- **TA Points: 4/4**
/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by
  -- wlog c ≠ 0
  by_cases hc : c = 0
  · intro ε hε
    use 0
    simp [hc, hε]
  have hc_pos : |c| > 0 := by exact abs_pos.mpr hc
  have hc_nonzero : |c| ≠ 0 := by exact abs_ne_zero.mpr hc

  intro ε hε
  -- divide ε by |c|
  obtain ⟨Ns,hNs⟩ := hs (ε/|c|) (div_pos hε hc_pos)
  use Ns
  intro n hn

  calc
    |c * s n - c* a| = |c * (s n - a)| := by rw [mul_sub]
                   _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
                   _ < |c| * (ε / |c|) := by exact (mul_lt_mul_iff_right₀ hc_pos).mpr (hNs n hn)
                   _ = ε               := by exact mul_div_cancel₀ ε hc_nonzero


-- **TA Points: 2/2**
/-- Prove this using a calculation. -/
lemma exercise_square {m n k : ℤ} (h : m ^ 2 + n ≤ 2) : n + 1 ≤ 3 + k ^ 2 := by
  have hm : m^2 ≥ 0 := sq_nonneg m
  have hk : k^2 ≥ 0 := sq_nonneg k
  have hn : n ≤ 2 := le_of_add_le_of_nonneg_right h hm
  calc
    n + 1 ≤ 2 + 1   := by exact (add_le_add_iff_right 1).mpr hn
        _ = 3       := by norm_num
        _ ≤ 3 + k^2 := by exact le_add_of_nonneg_right hk


section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

-- **TA Points: 2/2**
/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by
  intro k
  use k
  intro n hn
  simp
  exact mul_le_mul_right (s n) hn

-- **TA Points: 4/4**
/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by
  intro k
  obtain ⟨N₁, hN₁⟩ := h₁ k
  obtain ⟨N₂, hN₂⟩ := h₂ k
  use max N₁ N₂

  intro n hn
  specialize hN₁ n (le_of_max_le_left hn)
  specialize hN₂ n (le_of_max_le_right hn)
  simp
  linarith

-- **TA Ponits: 4/4**
/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by
  use fun n ↦ n^n
  simp

  intro k
  simp
  use k
  intro n hn
  rw [pow_add_one']

  have hn_pow_n : n^n ≤ (n+1)^n := by
    exact Nat.pow_le_pow_left (le_add_right n 1) n
  have hk_n_plus_one : k ≤ n+1 := by linarith
  -- *TA Comment:* `exact?` actually already finds a proof here
  calc
    k * n^n ≤ (n+1) * n^n       := by exact mul_le_mul_right (n^n) hk_n_plus_one
          _ ≤ (n+1) * (n + 1)^n := by exact mul_le_mul_left (n+1) hn_pow_n

end Growth
