import Mathlib.Topology.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open Topology Real unitInterval

/-
I is the unit interval with it's canonical topology.
-/
lemma I.one_minus (x : I) : 1-x.val ∈ I :=
  ⟨unitInterval.one_minus_nonneg x,unitInterval.one_minus_le_one x⟩

section MobiusStrip
/--
The unit square I × I modulo
(x,0) ∼ (1-x,1)
-/
def MobiusStrip.setoid : Setoid (I × I) where
  r x y :=
    x=y ∨
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
instance MobiusStrip.instTopologicalSpace :
  TopologicalSpace MobiusStrip := instTopologicalSpaceQuotient

section MobiusStrip.embedding
/--
This creates a Möbius strip with a width of 1,
whose centre line coincides with the unit circle of the xy plane.
The angle α has its apex at the centre;
as it changes, the variation of r leads to the area that spans between the single edge.
Source: Wikipedia
-/
noncomputable def MobiusStrip.embedding.map : MobiusStrip → ℝ×ℝ×ℝ := Quotient.lift
  (fun (a,b) ↦
    letI r := 2*a.val - 1  -- -1 ≤ r ≤ 1
    letI α := 2*π*b.val    -- 0 ≤ α ≤ 2π
    (
    cos α * (1 + r/2 * cos (α/2)), -- x-coordinate
    sin α * (1 + r/2 * cos (α/2)), -- y-coordinate
    r/2 * sin (α/2)                -- z-coordinate
  ))
  -- Well-definedness:
  (by
    intro ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ h
    simp only [setoid, ← Quotient.eq_iff_equiv, Quotient.eq, Prod.mk.injEq] at *
    rcases h with ⟨ha,hb⟩ | ⟨⟨hb₁,hb₂⟩ | ⟨hb₁,hb₂⟩,ha⟩
    · -- If (a₁,b₁) = (a₁,b₂)
      simp only [hb, ha, and_self]
    -- If (a₁,b₁) ∼ (a₂,b₂) via the Möbius relation
    all_goals
      simp [hb₁, hb₂]
      rw [ha]
      ring
  )

lemma MobiusStrip.embedding.injective : Function.Injective map := by
  apply Quotient.ind₂
  intro a b
  simp [map]
  field_simp
  intro hx hy hz
  apply Quotient.eq.mpr
  by_cases h2 : a.2 = b.2
  · -- If a.2 = b.2, it follows that a = b
    left
    simp [Prod.ext_iff, h2]; ext
    simp_all
    rcases hz with hz|hz
    · exact hz
    by_cases hb2_le_one : b.2 = 1
    · simp [hb2_le_one] at hx
      exact hx
    apply unitInterval.coe_ne_one.mpr at hb2_le_one
    apply lt_of_le_of_ne b.2.prop.2 at hb2_le_one
    apply (sin_eq_zero_iff_of_lt_of_lt
      (lt_of_lt_of_le (neg_neg_iff_pos.mpr pi_pos) ((mul_nonneg_iff_of_pos_left pi_pos).mpr
        b.2.prop.1))
      (by rw [← propext (lt_inv_mul_iff₀ pi_pos), inv_mul_cancel₀ pi_ne_zero]; exact hb2_le_one)).mp
      at hz
    rw [mul_eq_zero_iff_left pi_ne_zero] at hz
    simp [hz] at hx
    exact hx
  · right
    -- Here one would have to compute a lot of stuff
    sorry

/--
An embedding of the Möbius Strip into ℝ³.
-/
def MobiusStrip.embedding : Set (ℝ×ℝ×ℝ) := Set.range embedding.map

/--
An isomorphism between the quotient MobiusStrip and it's embedding
into ℝ³.
-/
noncomputable def MobiusStrip.embedding.isom : MobiusStrip ≃ embedding :=
  Equiv.ofInjective map injective

/--
A homeomorphism between the quotient MobiusStrip and it's embedding
into ℝ³.
-/
noncomputable def MobiusStrip.embedding.homeom : MobiusStrip ≃ₜ embedding := by
  apply Homeomorph.mk (Equiv.ofInjective map injective) ?_ ?_
  · -- map is continuous
    apply Continuous.subtype_coind
    apply Continuous.quotient_lift
    simp only [continuous_prodMk]
    refine ⟨Continuous.mul (continuous_cos.comp' ?_) ?_,
      Continuous.mul (continuous_sin.comp' ?_) ?_,
      ?_⟩
    all_goals
      try
        apply continuous_const.add
        apply Continuous.mul
        · apply Continuous.div_const
          apply Continuous.sub ?_ continuous_const
          apply continuous_const.mul continuous_fst.subtype_val
        · apply continuous_cos.comp'
          apply Continuous.div_const
          apply continuous_const.mul continuous_snd.subtype_val
      try apply continuous_const.mul continuous_snd.subtype_val
    apply Continuous.mul ?_ (continuous_sin.comp' ?_)
    · apply Continuous.div_const
      apply Continuous.sub ?_ continuous_const
      apply continuous_const.mul continuous_fst.subtype_val
    · apply Continuous.div_const
      apply continuous_const.mul continuous_snd.subtype_val
  · -- map⁻¹ is continuous
    sorry

end MobiusStrip.embedding

-- In this section we will show that the Möbius Strip is homotopy equivalent to the circle.
section MobiusStrip_htpy_equiv_to_Circle

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

/--
The circle as a quotient of [0,1] by glueing together both endpoints.
-/
def Circle := Quotient Circle.setoid

instance Circle.instTopologicalSpace :
  TopologicalSpace Circle := instTopologicalSpaceQuotient

/--
The Möbius Strip is homotopy equivalent to the circle.
ToDo: For future use it may be useful to change the proof to the mathlib notion of the circle in ℂ.
-/
noncomputable def MobiusStrip_htpy_equiv_to_Circle :
    ContinuousMap.HomotopyEquiv MobiusStrip Circle where
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
      exact continuous_quotient_mk'.comp continuous_snd
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
      apply continuous_quotient_mk'.comp'
      apply Continuous.prodMk_right
  }
  left_inv := by
    let f : I × I → I := fun (t,x) ↦
      ⟨(1-t)/2 + t*x, by
        have ht1 : 0 ≤ 1-t.val := unitInterval.one_minus_nonneg t
        have ht2 : 1-t.val ≤ 1 := unitInterval.one_minus_le_one t
        have ⟨hx1,hx2⟩ := x.prop
        constructor
        · apply add_nonneg (by linarith)
          apply mul_nonneg t.prop.1 hx1
        · nth_rw 2 [(sub_sub_cancel 1 t.val).symm]
          rw [one_sub_mul, add_sub, sub_le_iff_le_add, add_comm, ← mul_one_div]
          by_cases hx : x.val ≥ 1/2
          · gcongr
          · calc
              _ ≤ 1/2 + (1-t.val)*(1/2) := by linarith
              _ ≤ 1/2 + 1/2             := by linarith
              _ = 1                     := by norm_num
              _ ≤ 1 + (1-t)*x           := by apply le_add_of_nonneg_right (mul_nonneg ht1 hx1)
      ⟩
    use {
      /- ((t,⟦(x,y)⟧) : I × MobiusStrip) ↦ ⟦(t/2 + (1-t)*x, y)⟧
      is a homotopy from id to ⟦(x,y)⟧ ↦ ⟦(1/2, y)⟧ -/
      toFun :=
        fun x ↦ ⟦(f (x.1, x.2.out.1), x.2.out.2)⟧
      continuous_toFun := sorry
    }
    · simp
      apply Quotient.ind
      intro (x,y)
      apply Quotient.eq.mpr
      simp [f, MobiusStrip.setoid]
      norm_num
      by_cases hy0 : y = 0
      · simp [hy0]
        have : (⟦(x,0)⟧ : MobiusStrip).out = (x,0) ∨
               (⟦(x,0)⟧ : MobiusStrip).out = (⟨1-x, I.one_minus x⟩, 1) := by sorry
        rcases this with h|h
        · left
          have : (x,(0:I)).2 = 0 := by simp
          symm
          nth_rw 1 [← this]
          exact congrArg Prod.snd h.symm
        · right
          have : ((⟨1-x,I.one_minus x⟩, 1) : I×I).2 = 1 := by simp
          symm
          nth_rw 1 [← this]
          exact congrArg Prod.snd h.symm
      by_cases hy1 : y = 1
      · simp [hy1]
        sorry
      · -- if 0 < y < 1
        simp [hy0,hy1]
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

end MobiusStrip_htpy_equiv_to_Circle
