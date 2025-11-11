import Mathlib.Analysis.Complex.Exponential

import Mathlib
open Real Function Set

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapters 7 and 8.1.
  Chapter 8 explains some of the design decisions for classes in Mathlib.

* Hand in the solutions to the exercises below. Deadline: **Thursday**, 14.11.2025 at 10.00.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/

/-! # Exercises to practice. -/


-- Recall the definition of points from the lecture.
@[ext] structure Point where
  x : ℝ
  y : ℝ
  z : ℝ

namespace Point

def add (a b : Point) : Point where
  x := a.x + b.x
  y := a.y + b.y
  z := a.z + b.z

instance : Add Point := ⟨add⟩

-- Prove that addition of points is associative.
lemma add_assoc {a b c : Point} : a + (b + c) = a + b + c := by
  ext
  · have : (a + (b + c)).x = a.x + (b.x + c.x) := by rfl
    rw [this]
    have : (a + b + c).x = a.x + b.x + c.x := by rfl
    rw [this, AddSemigroup.add_assoc]
  · have : (a + (b + c)).y = a.y + (b.y + c.y) := by rfl
    rw [this]
    have : (a + b + c).y = a.y + b.y + c.y := by rfl
    rw [this, AddSemigroup.add_assoc]
  · have : (a + (b + c)).z = a.z + (b.z + c.z) := by rfl
    rw [this]
    have : (a + b + c).z = a.z + b.z + c.z := by rfl
    rw [this, AddSemigroup.add_assoc]
  done

-- Define scalar multiplication of a point by a real number
-- in the way you know from Euclidean geometry.
def smul (r : ℝ) (a : Point) : Point where
  x := r*a.x
  y := r*a.y
  z := r*a.z

-- If you made the right definition, proving these lemmas should be easy.
@[simp] lemma smul_x (r : ℝ) (a : Point) : (Point.smul r a).x = r * a.x := by rfl
@[simp] lemma smul_y (r : ℝ) (a : Point) : (Point.smul r a).y = r * a.y := by rfl
@[simp] lemma smul_z (r : ℝ) (a : Point) : (Point.smul r a).z = r * a.z := by rfl

-- This registers the above operation as "scalar multiplication":
-- you can now write • for scalar multiplication.
instance : SMul ℝ Point := ⟨smul⟩

variable (x : ℝ) (a : Point)
#check x • a

end Point

-- This is the standard two-simplex in ℝ³. How does it look like, geometrically?
structure StandardTwoSimplex where
  coords : Point
  x_nonneg : 0 ≤ coords.x
  y_nonneg : 0 ≤ coords.y
  z_nonneg : 0 ≤ coords.z
  sum_eq : coords.x + coords.y + coords.z = 1

namespace StandardTwoSimplex

noncomputable section

-- Prove that a convex combination of two points in the standard simplex is again in the
-- standard simplex.
def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
  (a b : StandardTwoSimplex) : StandardTwoSimplex
where
  coords := lambda • a.coords + (1 - lambda) • b.coords
  x_nonneg := by
    have : (lambda • a.coords + (1 - lambda) • b.coords).x = lambda*a.coords.x + (1-lambda)*b.coords.x := by rfl
    rw [this]
    apply add_nonneg
    · apply mul_nonneg lambda_nonneg a.x_nonneg
    · apply mul_nonneg
      · exact sub_nonneg_of_le lambda_le
      · exact b.x_nonneg
  y_nonneg := by sorry
  z_nonneg := by sorry
  sum_eq := by sorry

end

end StandardTwoSimplex


/- Prove the following exercises about functions where the domain/codomain are
subtypes. -/

abbrev PosReal : Type := {x : ℝ // x > 0}

/- Codomain is a subtype (usually not recommended). -/
example (f : ℝ → PosReal) (hf : Monotone f) :
    Monotone (fun x ↦ log (f x)) := by
  sorry
  done

/- Specify that the range is a subset of a given set (recommended). -/
example (f : ℝ → ℝ) (hf : range f ⊆ {x | x > 0}) (h2f : Monotone f) :
  Monotone (log ∘ f) := by
  sorry
  done

/- Domain is a subtype (not recommended). -/
example (f : PosReal → ℝ) (hf : Monotone f) :
    Monotone (fun x ↦ f ⟨exp x, exp_pos x⟩) := by
  sorry
  done

/- Only specify that a function is well-behaved on a subset of its domain (recommended). -/
example (f : ℝ → ℝ) (hf : MonotoneOn f {x | x > 0}) :
    Monotone (fun x ↦ f (exp x)) := by
  sorry
  done


example : Setoid (ℕ × ℕ) where
  r := fun ⟨k, l⟩ ⟨m, n⟩ ↦ k + n = m + l
  iseqv := sorry


/-! # Exercises to hand-in. -/

section

-- Let's define a new operation on points in ℝ⁴.

@[ext]
structure Point4 where
  x : ℝ
  y : ℝ
  z : ℝ
  w : ℝ

def op (a b : Point4) : Point4 where
  x := a.x * b.x - a.y * b.y - a.z * b.z - a.w * b.w
  y := a.x * b.y + a.y * b.x + a.z * b.w - a.w * b.z
  z := a.x * b.z - a.y * b.w + a.z * b.x + a.w * b.y
  w := a.x * b.w + a.y * b.z - a.z * b.y + a.w * b.x

-- Prove that op is associative.
lemma op_assoc {a b c : Point4} : op (op a b) c = op a (op b c) := by
  simp only [op, Point4.mk.injEq]
  ring_nf
  tauto
  done

-- Investigate whether op is commutative: prove one of the following.
lemma op_comm : ∀ a b : Point4, op a b = op b a := by sorry
--not provable so still a sorry. But the one below is proven

-- For the latter, you may the following helpful.
example : ⟨0, 1, 2, 3⟩ ≠ (⟨0, 3, 2, 3⟩ : Point4) := by
  simp
  done

example {x y : ℝ} (h : x ≠ y) : ⟨0, 1, x, 3⟩ ≠ (⟨0, 1, y, 3⟩ : Point4) := by
  simp
  exact h
  done

-- If you want to use one of these lemmas, prove it also.
lemma ne_of_ne_x {a b : Point4} (h : a.x ≠ b.x) : a ≠ b := by
  by_contra h'; apply h
  simp [h']
lemma ne_of_ne_y {a b : Point4} (h : a.y ≠ b.y) : a ≠ b := by
  by_contra h'; apply h
  simp [h']
lemma ne_of_ne_z {a b : Point4} (h : a.z ≠ b.z) : a ≠ b := by
  by_contra h'; apply h
  simp [h']
lemma ne_of_ne_w {a b : Point4} (h : a.w ≠ b.w) : a ≠ b := by
  by_contra h'; apply h
  simp [h']


lemma not_op_comm : ¬(∀ a b : Point4, op a b = op b a) := by
  push_neg
  use ⟨0, 0, 1, 0⟩
  use ⟨0, 1, 0, 0⟩
  simp [op]
  norm_num

-- Let us now consider a special kind of points.
def SpecialPoint := { p : Point4 // p.x ^2 + p.y ^2 + p.z ^ 2 + p.w ^ 2 = 1 }

-- We define "the same" operation on special points: complete the proof.
def op' (a b : SpecialPoint) : SpecialPoint :=
  ⟨op a.val b.val,
  by
    have ha := a.prop.symm
    have hb := b.prop.symm
    simp [op]
    ring_nf
    rw [← sub_eq_of_eq_add (sub_eq_of_eq_add (sub_eq_of_eq_add ha)),
        ← sub_eq_of_eq_add (sub_eq_of_eq_add (sub_eq_of_eq_add hb))]
    ring
  ⟩

-- Prove that `SpecialPoint` with the operation `op'` is a group.
-- (If commutativity holds, it's even an abelian group. You don't need to prove this.)
-- Here is a definition of group to use.
structure Group' (G : Type*) where
  gop (x : G) (y : G) : G
  assoc (x y z : G) : gop (gop x y) z = gop x (gop y z)
  neutral : G
  gop_neutral : ∀ x : G, gop x neutral = x
  inv (x : G) : G
  gop_inv : ∀ x : G, gop x (inv x) = neutral

-- Note that you are working with subtypes again: you may need to use loogle to
-- find the right lemma to get "out of subtype world".
noncomputable example : Group' SpecialPoint where
  gop := op'
  assoc := by simp only [op', op_assoc, implies_true]
  neutral := ⟨(⟨1,0,0,0⟩ : Point4), by norm_num⟩
  gop_neutral := by
    intro a
    simp [op', op]
    rfl
  inv := fun a ↦ ⟨⟨a.1.x,-a.1.y,-a.1.z,-a.1.w⟩, by simp [a.prop]⟩
  gop_inv := by
    intro a
    simp [op', op]
    ring_nf
    simp [a.prop]


-- Bonus: Do you recognise this operation from your mathematics classes?
-- Can you even give it a geometric interpretation?
-- Answer: It's  the multiplication of quaternions
end



section Bipointed

/- **Exercise**.
Define the structure of "strict bipointed types", i.e. a type together with 2 unequal points
`x₀ ≠ x₁` in it.
Then state and prove the lemma that for any element of a strict bipointed type we have
`∀ z, z ≠ x₀ ∨ z ≠ x₁.` -/

-- give the definition here
structure StrictBipointedType where
  carrier : Type*
  x₀ : carrier
  x₁ : carrier
  x₀_ne_x₁ : x₀ ≠ x₁

-- state and prove the lemma here
lemma lemma1 (X : StrictBipointedType) : ∀ z : X.carrier, z ≠ X.x₀ ∨ z ≠ X.x₁ := by
  intro z
  by_cases h : z = X.x₀
  · simp [h, X.x₀_ne_x₁]
  · simp [h]


end Bipointed

section Subtypes

/-- Let's prove that the positive rationals form a group under multiplication.
Note: in this exercise `rw` and `simp` will not be that helpful, since the definition is hidden
behind notation. But you can use apply to use the lemmas about real numbers. -/

abbrev PosRat : Type := {x : ℚ // 0 < x}

def groupPosRat : Group PosRat where
  mul := fun a ↦ fun b ↦ ⟨a*b, mul_pos a.prop b.prop⟩
  mul_assoc := by
    intro a b c
    ext
    simp
    apply mul_assoc
  one := 1
  one_mul := by
    intro a
    ext
    simp
  mul_one := by
    intro a
    ext
    simp
  npow_zero := by
    intro a
    rfl
  npow_succ := by
    intro n a
    rfl
  inv := fun a ↦ ⟨a⁻¹, by simp only [inv_pos, a.prop]⟩
  div_eq_mul_inv := by
    intro a b
    ext
    rfl
  zpow_zero' := by
    intro a
    unfold zpowRec
    simp
    rfl
  zpow_succ' := by
    intro n a
    rfl
  zpow_neg' := by
    intro n a
    rfl
  inv_mul_cancel := by
    intro a
    ext
    simp
    apply Rat.inv_mul_cancel
    apply ne_of_gt a.prop

end Subtypes

section EquivalenceRelation

-- Prove that the following defines an equivalence relation.
def integerEquivalenceRelation : Setoid (ℤ × ℤ) where
  r := fun ⟨k, l⟩ ⟨m, n⟩ ↦ k + n = l + m
  iseqv := by
    simp
    constructor
    · -- refl
      intro x
      apply add_comm
    · -- symm
      intro x y h
      rw [add_comm, ← h, add_comm]
    · -- trans
      intro x y z h1 h2
      apply eq_sub_of_add_eq at h1
      apply eq_sub_of_add_eq at h2
      rw [h1,h2]
      ring

/- This simp-lemma will simplify `x ≈ y` in the lemma below. -/
@[simp] lemma integerEquivalenceRelation'_iff (a b : ℤ × ℤ) :
  letI := integerEquivalenceRelation; a ≈ b ↔ a.1 + b.2 = a.2 + b.1 := by rfl

example : Quotient integerEquivalenceRelation ≃ ℤ where
  toFun := Quotient.lift (fun ⟨k,l⟩ ↦ k-l) (sorry)
  --need proof that fun is well defined on the equiv classes
  invFun := sorry
  left_inv := sorry
  right_inv := sorry

end EquivalenceRelation
