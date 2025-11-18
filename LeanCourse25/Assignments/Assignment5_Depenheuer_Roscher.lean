import Mathlib.Analysis.Complex.Exponential

import Mathlib
open Real Function Set

-- **Submission of Nora Depenheuer and Joachim Roscher**

/-

* An advertisement: for a current event by the *Fachschaft* you may find interesting:

**Equity in math-an event for men**
The event will take place on 17 November from 16:00 to 18:00 in the Lipschitzsaal.
The Gleichstellungsreferat of the Fachschaft Mathematik warmly invites you to this event,
where we will discuss male perspectives on gender equality.
The program will include a talk on the topic, a panel discussion with professors and students, and
the opportunity to chat over drinks and enjoy free cookies afterwards.
You can find more information on our website at fsmath.uni-bonn.de.
Of course, everyone is welcome to join — we look forward to seeing you there 🙂


* Hand in the solutions to the exercises below. Deadline: **Thursday**, 20.11.2025 at 10.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/

-- Remember the definition Point from last week's assignment: let's parametrise this by a type.
@[ext]
structure Point (α : Type*) where
  x : α
  y : α
  z : α

-- Let's connect this to ℝ³. Here is to define a point in a triple:
-- you can use matching, just like you would for an inductive type.
example {x y z : ℝ} : Fin 3 → ℝ := fun
  | 0 => x
  | 1 => y
  | 2 => z

-- Define an equivalence from Fin 2 × Fin 3 to Fin 6.
example : Fin 3 × Fin 2 ≃ Fin 6 := sorry

-- Now prove that Point α and α³ are equivalent.
-- In particular, `Point` from last week and `ℝ³` are equivalent.
example {α : Type*} : (Fin 3 → α) ≃ Point α where
  toFun := fun f ↦ ⟨f 0, f 2, f 1⟩
  invFun P := fun
    | 0 => P.x
    | 1 => P.z
    | 2 => P.y
  left_inv := by sorry
  right_inv := by sorry

section

variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by
  sorry
  done

end

section

-- In the lecture, we also saw injectivity and bijectivity of functions.
-- There is another variant, "bijectivity on a set":
def BijectiveOn {α β : Type*} (f : α → β) (s : Set α) (t : Set β) : Prop :=
  (f '' s ⊆ t) ∧ InjOn f s ∧ SurjOn f s t

-- There is a curious fact about infinite types: they are bijective to a proper subset.
-- Let us explore this theme in the following exercises.

example : ∃ f : ℕ → ℕ, BijectiveOn f univ (univ \ {0}) := by
  sorry

example {α : Type*} [Infinite α] {a : α} : ∃ f : α → α, BijectiveOn f (univ \ {a}) univ := by
  -- Hint: a useful first step is "there exists an injective map ℕ → α".
  -- Use loogle or exact? to find this.
  sorry

-- In particular, an infinite type is bijective to a proper subtype.
-- If you like a little *challenge*, prove the converse.
-- This is a bit harder; you want to write down a careful mathematical proof first
-- and use loogle to re-use existing results from mathlib.
example {α : Type*} {s : Set α} (hs : s ≠ univ) {f : α → α} (hf : BijectiveOn f s univ) :
    Infinite α := by
  sorry

end



/-! # Exercises to hand-in. -/

-- There are only two exercises to hand in this week. In the remaining time, work on your first
-- project about formal conjectures.

section choice

/-- This exercise is about a subtle detail regarding the axiom of choice: while you know there
is a global choice function, it is not given by one "computation rule".
The following exercise makes this precise: prove it.

Remember that Lean has proof irrelevance: any two proofs of a given proposition are equal.
-/
example (choiceFunction : ∀ (α : Type) (p : α → Prop) (_h : ∃ x, p x), α)
    (h : ∀ (α : Type) (p : α → Prop) (x : α) (hx : p x), choiceFunction α p ⟨x, hx⟩ = x) :
    False := by
  specialize h Bool (fun x ↦ true)
  simp at h


end choice

section cardinality

/-
Compute by induction the cardinality of the powerset of a finite set.

Hints:
* Use `Finset.induction` as the induction principle, using the following pattern:
```
  induction s using Finset.induction with
  | empty => sorry
  | @insert x s hxs ih => sorry
```
* You will need various lemmas about the powerset, search them using Loogle.
  The following queries will be useful for the search:
  `Finset.powerset, insert _ _`
  `Finset.card, Finset.image`
  `Finset.card, insert _ _`
* As part of the proof, you will need to prove an injectivity condition
  and a disjointness condition.
  Separate these out as separate lemmas or state them using `have` to break up the proof.
* Mathlib already has `card_powerset` as a simp-lemma, so we remove it from the simp-set,
  so that you don't actually simplify with that lemma.
-/
attribute [-simp] Finset.card_powerset
#check Finset.induction

lemma finset_card_powerset (α : Type*) [DecidableEq α] (s : Finset α) :
    Finset.card (Finset.powerset s) = 2 ^ Finset.card s := by
  induction s using Finset.induction with
  | empty => rfl
  | insert x s hxs ih =>
      have :  Disjoint s.powerset (Finset.image (insert x) s.powerset) := by
        intro t hts htxs
        by_contra ht_nonempty
        simp at *
        obtain ⟨u,hu⟩ := Finset.Nonempty.exists_mem (Finset.nonempty_iff_ne_empty.mpr ht_nonempty)
        have hus := Finset.mem_powerset.mp (hts hu)
        have ⟨v,hvs,hxvu⟩ := Finset.mem_image.mp (htxs hu)
        rw [Finset.mem_powerset] at hvs
        by_cases hxu : x ∈ u
        · exact hxs (hus hxu)
        · simp [← hxvu] at hxu
      -- divide 𝒫(s) into two sets: one with x and one without
      rw [Finset.powerset_insert, Finset.card_union_of_disjoint this]
      -- compute stuff and use the induction hypothesis
      rw [Finset.card_insert_of_notMem hxs, Nat.pow_add_one, mul_two, ← ih, Nat.add_left_cancel_iff]
      apply Finset.card_image_of_injOn
      intro t₁ ht₁ t₂ ht₂ h
      simp at ht₁ ht₂
      replace ht₁ : x ∉ t₁ := by exact fun a ↦ hxs (ht₁ a)
      replace ht₂ : x ∉ t₂ := by exact fun a ↦ hxs (ht₂ a)
      ext y
      constructor
      · intro hyt₁
        have hy_ne_x : y ≠ x := ne_of_mem_of_not_mem hyt₁ ht₁
        have : y ∈ insert x t₁ := Finset.mem_insert_of_mem hyt₁
        rw [h] at this
        exact Finset.mem_of_mem_insert_of_ne this hy_ne_x
      · intro hyt₂
        have hy_ne_x : y ≠ x := ne_of_mem_of_not_mem hyt₂ ht₂
        have : y ∈ insert x t₂ := Finset.mem_insert_of_mem hyt₂
        rw [← h] at this
        exact Finset.mem_of_mem_insert_of_ne this hy_ne_x
  done

end cardinality
