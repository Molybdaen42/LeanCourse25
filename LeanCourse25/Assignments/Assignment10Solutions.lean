import Mathlib.Tactic
import Mathlib.Data.W.Basic

open Function Set
noncomputable section

/-! # Exercises to practice -/

section

/-
**Exercise 1**
* Finish the exercises from Lecture 19
* Prove the following exercises, by copying them at the bottom of the Lecture 19 file.

example : Provable (~(A || B) ⇔ ~A && ~B) := by
  sorry
  done

example {C : Formula} : Provable (A || (B && C) ⇔ (A || B) && (A || C)) := by
  sorry
  done

example {C : Formula} : Provable (A && (B || C) ⇔ (A && B) || (A && C)) := by
  sorry
  done

-/

-- This is more of an exercise in logic than it is in Lean. The first one can for example be solved
-- like this:

/-
lemma neg_neg_iff : Provable (~~A ⇔ A) := by
  apply andI
  · apply impI
    apply botC
    exact impE (A := ~A) (ax (by simp [neg])) (ax (by simp))
  · apply impI
    apply impI
    exact impE (A := A) (ax (by simp [neg])) (ax (by simp))

lemma imp_iff : Provable ((A ⇒ B) ⇔ (~B ⇒ ~ A)) := by
  apply andI
  · apply impI
    apply impI
    apply impI
    apply impE (A := B) (ax (by simp [neg]))
    exact impE (A := A) (ax (by simp)) (ax (by simp))
  · apply impI
    apply impI
    apply botC
    apply impE (A := A)
    · exact impE (A := ~B) (ax (by simp [neg])) (ax (by simp))
    · exact ax (by simp)

/- Exercise: prove one of the de-Morgan laws. -/
example : Provable (~(A && B) ⇔ ~A || ~B) := by
  apply andI
  · apply impE (A := ~(~A || ~B) ⇒ ~~(A && B)) (andE2 imp_iff)
    apply impI
    apply impE (A := A && B)
    · exact weakening (andE2 neg_neg_iff) (empty_subset _)
    · simp
      apply andI
      · apply botC
        apply impE (A := ~A || ~B) (ax (by simp [neg]))
        exact orI1 (ax (mem_insert ~A {~(~A || ~B)}))
      · apply botC
        apply impE (A := ~A || ~B) (ax (by simp [neg]))
        exact orI2 (ax (mem_insert ~B {~(~A || ~B)}))
  · apply impI
    apply impI
    simp only [insert_empty_eq]
    apply orE (A := ~A) (B := ~B)
    · exact ax (mem_insert_of_mem (A && B) rfl)
    · apply impE (A := A)
      · exact ax (mem_insert ~A {A && B, ~A || ~B})
      · apply andE1 (B := B) (ax (by simp))
    · apply impE (A := B)
      · exact ax (by simp [neg])
      · apply andE2 (A := A) (ax (by simp))
  done
-/


/-
**Exercise 2**
Define the inductive type of labeled binary trees.
A labeled binary tree is either
- a leaf, labeled with an element from `α : Type*`
- a node, labeled with an element from `β : Type*`,
  which has two children that are again labeled binary trees (labeled in the same way)

Define two operations on your inductive type:
- the `flip` operator that swaps the two children of *every* node in the tree
- a replacement operation that takes as argument a function from `α` to labeled binary trees,
  and it replaces all leaves labeled with `x` by the tree `f x` (for all `x`).

Now state and proof three lemmas:
- show that applying `flip` twice gives the original tree back.
- show that if you apply the replacement operation to a tree and then flip it,
  that is equal to flipping first and applying a (slightly different) replacement operation.
- show that if you apply the replacement operation twice (with two different functions),
  then you can also apply the replacement operation once (with a more complicated function).
-/

inductive LabeledBinaryTree (α β : Type*) where
  | Leaf (a : α) : LabeledBinaryTree α β
  | Node (b : β) (inl : LabeledBinaryTree α β) (inr : LabeledBinaryTree α β) : LabeledBinaryTree α β

namespace LabeledBinaryTree

variable {α β : Type*}

def flip : LabeledBinaryTree α β → LabeledBinaryTree α β
  | Leaf a => Leaf a
  | Node b inl inr => Node b (flip inr) (flip inl)

def replace (f : α → LabeledBinaryTree α β) : LabeledBinaryTree α β → LabeledBinaryTree α β
  | Leaf a => f a
  | Node b inl inr => Node b (replace f inl) (replace f inr)

lemma flip_flip (x : LabeledBinaryTree α β) : flip (flip x) = x := by
  induction x with
  | Leaf a => rfl
  | Node b inl inr hinl hinr => simp [hinl, hinr, flip]

lemma flip_replace (f : α → LabeledBinaryTree α β) (x : LabeledBinaryTree α β) :
    flip (replace f x) = replace (flip ∘ f) (flip x) := by
  induction x with
  | Leaf a => rfl
  | Node b inl inr hinl hinr => simp [hinl, hinr, replace, flip]

lemma replace_replace (f g : α → LabeledBinaryTree α β) (x : LabeledBinaryTree α β) :
    replace g (replace f x) = replace (fun y ↦ replace g (f y)) x := by
  induction x with
  | Leaf a => rfl
  | Node b inl inr hinl hinr => simp [hinl, hinr, replace]

end LabeledBinaryTree

/-
**Exercise 3**
W-types are general recursive types.
`WType α β` has `|α|`-many constructors and
constructor `i : α` has arity `β i`
-/
#print WType

def forwardMap : ℕ → WType (α := Bool) (Bool.rec Empty Unit)
  | Nat.zero => WType.mk (α := Bool) (β := Bool.rec Empty Unit) false Empty.elim
  | Nat.succ n => WType.mk (α := Bool) (β := Bool.rec Empty Unit) true (fun i ↦ forwardMap n)

def backwardMap : WType (α := Bool) (Bool.rec Empty Unit) → ℕ
  | ⟨a, f⟩ => match a with
    | false => 0
    | true => Nat.succ (backwardMap (f Unit.unit))

/- The natural numbers have 2 constructors,
`zero` is nullary (has no recursive arguments) and
`succ` is unary (has one recursive argument).

Prove this equivalence.
Hint: define the functions back-and-forth as separate definitions. -/
example : ℕ ≃ WType (α := Bool) (Bool.rec Empty Unit) where
  toFun := forwardMap
  invFun := backwardMap
  left_inv x := by
    induction x with
    | zero => rfl
    | succ n hn => simp [forwardMap, backwardMap, hn]
  right_inv x := by
    induction x with
    | mk a f h =>
      exact match a with
      | false => by
        simp only [backwardMap, forwardMap, WType.mk.injEq, heq_eq_eq, true_and]
        ext x
        exact x.elim
      | true => by
        simp [forwardMap, backwardMap, h]

end


/-! # Exercises to hand in

**There are no exercises to hand-in this week. Enjoy the holidays!**

In January, there will be few exercises to be handed in.
Make sure to work on Project 2 instead.

You can work on Project 2 either:
* by creating Lean files in the `Projects` folder of the course repository.
  You can commit to your work to a fork (see `Projects/Git.md` for instructions)
* in your own new repository.
  You can create a new repository by using the extension symbol in VSCode:
  `∀ > New Project... > Create Project using Mathlib` and choosing a directory.

In both cases, once you have pushed something to GitHub, add the URL of your repository to the
[Sciebo table](https://uni-bonn.sciebo.de/s/tBzqggEFajsgwC6).
-/
