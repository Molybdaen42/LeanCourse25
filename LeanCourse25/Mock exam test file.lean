import Mathlib.Topology.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Finset.Range
open Topology Real unitInterval Finset

section ex1
example {p q : Prop} : p → q → p := by
  intro p q
  exact p
example {p q : Prop} : p ∨ q → q ∨ p := by
  rw [or_comm, imp_self]
  trivial
end ex1

section ex2
example : Differentiable ℝ (fun x : ℝ ↦ exp (x^2) + sin (π * x)) := by
  --exact Differentiable.sq.exp.add Differentiable.const_mul.sin
  apply Differentiable.add
  · apply Differentiable.exp
    sorry
  · sorry
example {a b c d e : ℝ} (hab : a ≤ b) (hc : 0 ≤ c) (hde : d ≤ e) : exp a * c + d ≤ exp b * c + e := by
  --nlinarith
  --linarith
  gcongr
end ex2

section ex4
example : AddCommGroup ℝ := sorry
example : CommGroup { x : ℝ // x ≠ 0} := sorry
example : ∀ n, ∑ i ∈ range (n+1), i = n*(n+1)/2 := by sorry
instance Baum1 : AddCommGroup ℝ := sorry
instance Baum2 : CommGroup { x : ℝ // x ≠ 0} := sorry
instance Baum3 : ∀ n, ∑ i ∈ range (n+1), i = n*(n+1)/2 := by sorry
end ex4

section ex5
def f : ℕ → ℕ := fun
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | n+3 => f (n+2) + f (n+1) + f n
end ex5

section ex6
variable {X Y Z : Type} {f : X×Y→Z} {a : X} {b : Y} {c : Z}
#check f a
#check (c, f (a,b))
#check Prod.mk X Y a b
#check Prod.mk (β := X) (α := Y)
#check Prod.mk (α := Y) (β := Y) a
#check Prod.mk (β := Y) (fst := a)
#check Prod.mk b a
#check Prod.mk (a,b) (b,a)
#check Prod.mk (snd := Y) (fst := X)
end ex6
