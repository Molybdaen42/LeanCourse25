import Mathlib.Topology.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
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

def myCircle.setoid : Setoid I where
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
def myCircle := Quotient myCircle.setoid
instance myCircle.instTopologicalSpace :
  TopologicalSpace myCircle := instTopologicalSpaceQuotient

def myCircle_is_circle : myCircle ≃ Circle := sorry


noncomputable def MobiusStrip_htpy_equiv_to_myCircle :
    ContinuousMap.HomotopyEquiv MobiusStrip myCircle where
  toFun := {
    /- The lifted map is ˋfun (x,y) ↦ ⟦y⟧ˋ.-/
    toFun := Quotient.lift (Quotient.mk'' ∘ Prod.snd) (by
      intro ⟨x,t⟩ ⟨y,s⟩
      simp only [← Quotient.eq_iff_equiv, Quotient.eq, MobiusStrip.setoid, Function.comp_apply]
      rw [Quotient.eq'']
      simp only [myCircle.setoid]
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
      simp [myCircle.setoid, MobiusStrip.setoid]
      norm_num
      )
    continuous_toFun := by
      apply continuous_quot_lift
      apply Continuous.comp' continuous_quotient_mk'
      apply Continuous.prodMk_right
  }
  left_inv := by
    let f : I × I → I := fun (t,x) ↦
      ⟨(1-t)/2 + t*x, by
        have ⟨ht1,ht2⟩ := t.prop
        have ⟨hx1,hx2⟩ := x.prop
        constructor
        · apply add_nonneg (by linarith)
          sorry
          --apply mul_nonneg (sub_nonneg.2 ht2) hx1
        · sorry
          /-rw [one_sub_mul, add_sub, sub_le_iff_le_add, add_comm, ← mul_one_div]
          by_cases hx : x.val ≥ 1/2
          · gcongr
          · calc
              _ ≤ 1/2 + t.val*(1/2) := by linarith
              _ ≤ 1/2 + 1/2         := by linarith
              _ = 1                 := by norm_num
              _ ≤ 1 + t*x           := by apply le_add_of_nonneg_right (mul_nonneg ht1 hx1)-/
      ⟩
    use {
      /- ((t,⟦(x,y)⟧) : I × MobiusStrip) ↦ ⟦(t/2 + (1-t)*x, y)⟧
      is a homotopy from id to ⟦(x,y)⟧ ↦ ⟦(1/2, y)⟧ -/
      toFun :=
        fun x ↦ ⟦(f (x.1, x.2.out.1), x.2.out.2)⟧
        /- (fun t ↦
        Quotient.lift (fun (x,y) ↦
          Quotient.mk'' (f (t,x), y))
          (by
            intro (x₁,x₂) (y₁,y₂)
            simp only [f, MobiusStrip.setoid, ← Quotient.eq_iff_equiv, Quotient.eq, Prod.mk.injEq]
            rw [Quotient.eq'']
            simp
            gcongr ?_ ∨ ?_
            · intro ⟨h1, h2⟩
              simp [h1, h2]
            · intro ⟨h1, h2⟩
              simp [h1, h2]
              ring
          )
        ).uncurry-/
      continuous_toFun := by

        sorry
        /-apply Continuous.comp₂ continuous_quotient_mk'
        · apply Continuous.subtype_mk --Hier liegt der Fehler
          apply Continuous.add
          · apply Continuous.div_const (Continuous.fst' continuous_subtype_val)
          apply Continuous.mul
          · apply Continuous.sub continuous_const (Continuous.fst' continuous_subtype_val)
          apply Continuous.subtype_val
          apply Continuous.fst
          apply Continuous.snd'
          -- Ist das überhaupt wahr? Nein, oder?
          sorry
        · apply Continuous.subtype_mk

          sorry
        -/
    }
    · simp
      apply Quotient.ind
      intro (x,y)
      apply Quotient.eq.mpr
      simp [f, MobiusStrip.setoid]
      norm_num
      by_cases hy0 : y = 0
      · simp [hy0]

        sorry
      by_cases hy1 : y = 1
      · sorry
      · -- if 0 < y < 1
        sorry
    · simp [f]
  right_inv := by
    use {
      toFun := Prod.snd
      continuous_toFun := continuous_snd
    }
    · apply Quotient.ind
      simp
    · exact fun x ↦ rfl

noncomputable def e : myCircle ≃ Circle where
  toFun x := Circle.exp (x.out*2*π)
  invFun z := ⟦⟨((Complex.log z).im + π) / (2*π), by --Das +π ist sehr weird und wahrscheinlich falsch
    apply unitInterval.div_mem
    · linarith [Complex.neg_pi_lt_log_im z]
    · linarith [pi_nonneg]
    · linarith [Complex.log_im_le_pi z]
    ⟩⟧
  left_inv x := by
    simp [Complex.log_im]
    #check Complex.arg_exp_mul_I
    sorry
  right_inv := sorry

noncomputable def MobiusStrip_htpy_equiv_to_Circle :
    ContinuousMap.HomotopyEquiv MobiusStrip Circle where
  toFun := sorry
  invFun := sorry
  left_inv := by sorry
  right_inv := by sorry

end MobiusStrip
