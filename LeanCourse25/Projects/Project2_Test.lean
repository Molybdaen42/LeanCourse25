import Mathlib.Topology.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Equiv
open Topology Real

section MobiusStrip
/--
The unit interval with it's canonical topology.
-/
abbrev I := unitInterval
instance I.instTopologicalSpace : TopologicalSpace I := instTopologicalSpaceSubtype
-- ToDo: Braucht man das? Muss man statt 1 lieber ⟨1,one_mem⟩ schreiben?
abbrev I.zero_mem := unitInterval.zero_mem
abbrev I.one_mem := unitInterval.one_mem

/--
(x,t) ∼ (y,s) ↔ (x,t)=(y,s) ∨ (((t = 0 ∧ s = 1) ∨ (t = 1 ∧ s = 0)) ∧ x = 1 - y)
-/
def MobiusStrip.setoid : Setoid (I×I) where
  r x y := x=y ∨
    (((x.2 = 0 ∧ y.2 = 1) ∨ (x.2 = 1 ∧ y.2 = 0)) ∧ x.1 = (1 : ℝ) - y.1)
  iseqv := {
    refl x := by left;rfl
    symm {x} {y} := by
      gcongr ?_ ∨ (?_ ∧ ?_)
      · exact eq_comm.1
      · simp only [and_comm, or_comm, imp_self]
      · simp only [eq_sub_iff_add_eq, add_comm, imp_self]
    trans {x} {y} {z} hxy hxz := by
      rcases hxy with hxy | ⟨hxy1|hxy1,hxy2⟩
      · simp only [hxy, hxz]
      all_goals
        simp [hxy1] at hxz ⊢;
        rw [hxy2, sub_right_inj]
        rcases hxz with hxz | hxz
        right; simp only [← hxz, hxy1.2, and_self]
        left
        ext
        rw [hxy2, hxz.2, sub_sub_cancel]
        rw [hxz.1,hxy1.1]
  }
def MobiusStrip := Quotient MobiusStrip.setoid
instance MobiusStrip.instTopologicalSpace : --ToDo: Namen ändern
  TopologicalSpace MobiusStrip := instTopologicalSpaceQuotient

def Circle.setoid : Setoid I where
  r x y := x=y ∨ (x=0 ∧ y=1) ∨ (x=1 ∧ y=0)
  iseqv := {
    refl x := by simp
    symm {x} {y} := by
      gcongr ?_ ∨ ?_
      · exact eq_comm.1
      · simp only [and_comm, or_comm, imp_self]
    trans {x} {y} {z} hxy hxz := by
      rcases hxy with hxy | ⟨hxy1|hxy1⟩
      · simp only [hxy, hxz]
      all_goals
        simp [hxy1] at hxz ⊢;
        rw [or_comm, eq_comm]
        nth_rw 2 [eq_comm]
        assumption
  }
def Circle := Quotient Circle.setoid
instance Circle.instTopologicalSpace :
  TopologicalSpace Circle := instTopologicalSpaceQuotient

--lemma Circle_is_circle : Circle ≃ Complex.Circle := by sorry


noncomputable def MobiusStrip_htpy_equiv_to_circle : ContinuousMap.HomotopyEquiv MobiusStrip Circle where
  toFun := {
    /- The lifted map is ˋfun (x,y) ↦ ⟦y⟧ˋ.-/
    toFun := Quotient.lift (Quotient.mk'' ∘ Prod.snd) (by
      intro ⟨x,t⟩ ⟨y,s⟩
      simp only [← Quotient.eq_iff_equiv, Quotient.eq, MobiusStrip.setoid, Function.comp_apply]
      rw [Quotient.eq'']
      simp only [Circle.setoid]
      gcongr
      · simp
      · intro h
        exact h.1
      )
    continuous_toFun := by
      apply continuous_quot_lift
      exact Continuous.comp continuous_quotient_mk' continuous_snd
  }
  invFun := {
    toFun := Quotient.lift (fun x ↦ ⟦(⟨1/2,by simp; linarith⟩,x)⟧) (by
      intro x y
      simp
      rw [Quotient.eq'', ← Quotient.eq_iff_equiv, Quotient.eq]
      simp [Circle.setoid, MobiusStrip.setoid]
      norm_num
      )
    continuous_toFun := by
      apply continuous_quot_lift
      apply Continuous.comp' continuous_quotient_mk'
      apply Continuous.prodMk_right
  }
  left_inv := by
    let f : ℝ × ℝ → ℝ := fun (t,x) ↦ t/2 + (1-t)*x
    have hf : ∀ t ∈ I, ∀ x ∈ I, f (t,x) ∈ I := by sorry
    use {
      toFun x := ⟦(⟨f (x.1,x.2.out.1),by sorry /-apply hf-/⟩,x.2.out.2)⟧
      continuous_toFun := sorry
    }
    · simp
      sorry
    · simp
      sorry
  right_inv := by
    use {
      toFun := Prod.snd
      continuous_toFun := continuous_snd
    }
    · apply Quotient.ind
      simp
    · exact fun x ↦ rfl

end MobiusStrip
