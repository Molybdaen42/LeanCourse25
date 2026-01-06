import Mathlib.Topology.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Topology.Constructions
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.Complex.Log
open Topology Real


/--
The unit interval with it's canonical topology.
-/
abbrev I := unitInterval
instance I.instTopologicalSpace : TopologicalSpace I := instTopologicalSpaceSubtype
-- ToDo: Braucht man das? Muss man statt 1 lieber ⟨1,one_mem⟩ schreiben?
abbrev I.zero_mem := unitInterval.zero_mem
abbrev I.one_mem := unitInterval.one_mem

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
  simp only [setoid] -- Can be removed (ToDo)
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
    sorry

def MobiusStrip.embedding : Set (ℝ×ℝ×ℝ) := Set.range embedding.map

noncomputable def MobiusStrip.embedding.equiv : MobiusStrip ≃ₜ embedding := by
  apply Homeomorph.mk (Equiv.ofInjective map injective) ?_ ?_
  · -- map is continuous
    apply Continuous.subtype_coind
    apply Continuous.quotient_lift
    simp only [continuous_prodMk]
    constructor
    · apply Continuous.mul (Continuous.comp' continuous_cos ?_)
      · apply Continuous.add continuous_const
        apply Continuous.mul
        · apply Continuous.div_const
          apply Continuous.sub ?_ continuous_const
          apply Continuous.mul continuous_const (Continuous.subtype_val continuous_fst)
        · apply Continuous.comp' continuous_cos ?_
          apply Continuous.div_const
          apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
      · apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
    constructor
    · apply Continuous.mul (Continuous.comp' continuous_sin ?_)
      · apply Continuous.add continuous_const
        apply Continuous.mul
        · apply Continuous.div_const
          apply Continuous.sub ?_ continuous_const
          apply Continuous.mul continuous_const (Continuous.subtype_val continuous_fst)
        · apply Continuous.comp' continuous_cos ?_
          apply Continuous.div_const
          apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
      · apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
    · apply Continuous.mul ?_ (Continuous.comp' continuous_sin ?_)
      · apply Continuous.div_const
        apply Continuous.sub ?_ continuous_const
        apply Continuous.mul continuous_const (Continuous.subtype_val continuous_fst)
      · apply Continuous.div_const
        apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
  · -- map⁻¹ is continuous
    sorry

end MobiusStrip.embedding
section MobiusStrip_htpy_equiv_to_Circle

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

/-
-- ToDo
def myCircle_is_circle : myCircle ≃ Circle := sorry
-/

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
        have ht1 : 0 ≤ 1-t.val := by exact unitInterval.one_minus_nonneg t
        have ht2 : 1-t.val ≤ 1 := by exact unitInterval.one_minus_le_one t
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
        simp only [continuous_iff_continuousAt, Prod.forall, f]
        intro t
        apply Quotient.ind
        intro ⟨x₁,x₂⟩ U
        simp only [Filter.mem_map]
        intro hU_nhd
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
        --have : MobiusStrip.setoid (⟦(x,0)⟧ : MobiusStrip).out (x,0) := Quotient.mk_out (x,0)
        --simp [Quotient.out, Quot.out]
        sorry
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

/-
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
-/

end MobiusStrip_htpy_equiv_to_Circle
end MobiusStrip

section KleinBottle
/--
The unit square modulo
(x,0) ∼ (1-x,1) and (0,y) ∼ (1,y)
-/
def KleinBottle.setoid : Setoid (I×I) where
  r x y :=
    -- Equality
    x=y ∨
    -- Möbius relation
    (((x.2 = 0 ∧ y.2 = 1) ∨ (x.2 = 1 ∧ y.2 = 0)) ∧ (x.1 : ℝ) = 1 - y.1) ∨
    -- Torus relation
    (((x.1 = 0 ∧ y.1 = 1) ∨ (x.1 = 1 ∧ y.1 = 0)) ∧ x.2 = y.2) ∨
    -- Vertical corners
    ((x.1 = y.1 ∧ (x.1 = 0 ∨ x.1 = 1)) ∧ ((x.2 = 0 ∧ y.2 = 1) ∨ (x.2 = 1 ∧ y.2 = 0)))

  iseqv := {
    refl x := by left;rfl
    symm {x} {y} := by
      gcongr ?_ ∨ (?_ ∧ ?_) ∨ (?_ ∧ ?_) ∨ (?_ ∧ ?_)
      · exact eq_comm.mp
      · simp only [and_comm, or_comm, imp_self]
      · simp only [eq_sub_iff_add_eq, add_comm, imp_self]
      · simp only [and_comm, or_comm, imp_self]
      · exact eq_comm.mp
      · intro h
        simp only [← h.1, h.2, and_self]
      · simp only [and_comm, or_comm, imp_self]
    trans {x} {y} {z} hxy hyz := by
      rcases hxy with hx_eq_y | hxy | hxy | hxy
      · -- If x = y, it's clear
        rw [hx_eq_y]
        exact hyz
      · -- If x ∼ y via Möbius relation, i.e.
        -- (((x.2 = 0 ∧ y.2 = 1) ∨ (x.2 = 1 ∧ y.2 = 0)) ∧ (x.1 : ℝ) = 1 - y.1))
        rcases hxy with ⟨⟨hx2,hy2⟩|⟨hx2,hy2⟩,hxy⟩
        all_goals
          simp [hx2,hy2] at hyz ⊢;
          rcases hyz with hy_eq_z | hyz | hyz | hyz
          · -- If y = z, the Möbius relation from x ∼ y must transport to x ∼ z
            right; left
            simp [← hy_eq_z, hy2, hxy]
          · -- If y ∼ z via Möbius relation
            left
            ext
            rw [hxy, hyz.2, sub_sub_cancel]
            rw [hx2, hyz.1]
          · -- If y ∼ z via torus relation
            right; right; right
            simp only [← hyz.2, and_true]
            rcases hyz.1 with ⟨hy1,hz1⟩ | ⟨hy1,hz1⟩
            · simp [hy1] at hxy
              simp [hxy, hz1]
            · simp [hy1] at hxy
              simp [hxy, hz1]
          · -- If y and z are vertical corners
            right; right; left
            simp only [hyz.2, and_true, ← hyz.1.1]
            rcases hyz.1 with ⟨hyz1, hy1|hy1⟩
            · right
              simp only [hxy, hy1, Set.Icc.coe_zero, sub_zero,
                Set.Icc.coe_eq_one.mp, Set.Icc.coe_one, and_self]
            · left
              simp only [hxy, hy1, Set.Icc.coe_one, sub_self,
                Set.Icc.coe_eq_zero.mp, Set.Icc.coe_zero, and_self]
      · -- If x ∼ y via torus relation, i.e.
        -- (((x.1 = 0 ∧ y.1 = 1) ∨ (x.1 = 1 ∧ y.1 = 0)) ∧ x.2 = y.2)
        rcases hxy with ⟨⟨hx2,hy2⟩|⟨hx2,hy2⟩,hxy⟩
        all_goals
          simp [hx2,hy2] at hyz ⊢;
          nth_rw 6 [eq_comm] at hyz
          try rw [sub_eq_self] at hyz
          try
            rw [sub_eq_zero] at hyz
            nth_rw 6 [eq_comm] at hyz
          rcases hyz with hy_eq_z | hyz | hyz | hyz
          · -- If y = z, the torus relation from x ∼ y must transport to x ∼ z
            right; right; left
            simp [← hy_eq_z, hy2, hxy]
          · -- If y ∼ z via Möbius relation
            right; right; right
            constructor
            · ext; exact hyz.2.symm
            rw [hxy]
            exact hyz.1
          · -- If y ∼ z via torus relation
            left
            rw [eq_comm, ← hx2, ← hxy] at hyz
            exact Prod.ext_iff.mpr hyz
          · -- If y and z are vertical corners
            right; left
            rw [hxy]
            simp [hyz.2, ← hyz.1]
      · -- If x and y are vertical corners
        rcases hxy with ⟨⟨hxy1,hx1|hx1⟩,⟨hx2,hy2⟩|⟨hx2,hy2⟩⟩
        all_goals
          simp [hx2,hy2,hx1,← hxy1] at hyz ⊢;
          nth_rw 3 [eq_comm] at hyz
          try rw [sub_eq_self] at hyz
          try
            rw [sub_eq_zero] at hyz
            nth_rw 3 [eq_comm] at hyz
          rcases hyz with hy_eq_z | ⟨hz1,hz2⟩ | ⟨hz1,hz2⟩ | ⟨hz1,hz2⟩
          · -- If y = z, the vertical corner relation from x ∼ y must transport to x ∼ z
            right; right; right
            simp [← hy_eq_z, hy2, ← hxy1, hx1]
          · -- If y ∼ z via Möbius relation
            right; right; left
            simp [hz1]
            ext
            exact hz2
          · -- If y ∼ z via torus relation
            right; left
            simp [hz1, ← hz2]
          · -- If y and z are vertical corners
            left
            ext
            · rw [hx1, ← hz1]
            · rw [hx2, hz2]
  }
def KleinBottle := Quotient KleinBottle.setoid
instance KleinBottle.instTopologicalSpace :
  TopologicalSpace KleinBottle := instTopologicalSpaceQuotient

section KleinBottle.embedding
/--
This creates an embedding of the Möbius strip into ℝ⁴ with a formula by
https://math.stackexchange.com/questions/330856/how-to-embed-klein-bottle-into-r4
and
https://mathoverflow.net/questions/430183/topologically-embed-klein-bottle-into-mathbbr4-projecting-to-usual-beer-b
-/
noncomputable def KleinBottle.embedding.map : KleinBottle → ℝ×ℝ×ℝ×ℝ := Quotient.lift
  (fun (u,t) ↦ (
    (2 + cos (2*π*u)) * cos (2*π*t), -- 1st coordinate
    (2 + cos (2*π*u)) * sin (2*π*t), -- 2nd coordinate
    cos (π*t) * sin (2*π*u),         -- 3rd coordinate
    sin (π*t) * sin (2*π*u)          -- 4th coordinate
  ))
  -- Well-definedness:
  (by
    intro ⟨a₁,b₁⟩ ⟨a₂,b₂⟩ h
    simp only [setoid, ← Quotient.eq_iff_equiv, Quotient.eq, Prod.mk.injEq] at *
    rcases h with ⟨ha,hb⟩ | ⟨hb,ha⟩ | ⟨ha,hb⟩ | ⟨⟨ha,ha₁⟩,hb⟩
    · -- If (a₁,b₁) = (a₁,b₂)
      simp only [hb, ha, and_self]
    · -- If (a₁,b₁) ∼ (a₂,b₂) via the Möbius relation
      rcases hb with ⟨hb₁,hb₂⟩ | ⟨hb₁,hb₂⟩
      all_goals
        simp [hb₁, hb₂, ha, mul_one_sub]
    · -- If (a₁,b₁) ∼ (a₂,b₂) via the torus relation
      rcases ha with ⟨ha₁,ha₂⟩ | ⟨ha₁,ha₂⟩
      all_goals
        simp [ha₁, ha₂, hb]
    · -- If (a₁,b₁) ∼ (a₂,b₂) via the vertical corner relation
      rcases ha₁ with ha₁ | ha₁
      all_goals
        rcases hb with ⟨hb₁,hb₂⟩ | ⟨hb₁,hb₂⟩
        all_goals
          simp [← ha, ha₁, hb₁, hb₂]

  )
lemma KleinBottle.embedding.injective : Function.Injective map := by sorry

def KleinBottle.embedding : Set (ℝ×ℝ×ℝ×ℝ) := Set.range embedding.map

instance KleinBottle.embedding.instTopologicalSpace :
  TopologicalSpace KleinBottle.embedding := instTopologicalSpaceSubtype

noncomputable def KleinBottle.embedding.equiv : KleinBottle ≃ₜ embedding := by
  apply Homeomorph.mk (Equiv.ofInjective map injective) ?_ ?_
  · -- map is continuous
    apply Continuous.subtype_coind
    apply Continuous.quotient_lift
    simp only [continuous_prodMk]
    constructor
    · apply Continuous.mul ?_ (Continuous.comp' continuous_cos ?_)
      · apply Continuous.add continuous_const (Continuous.comp' continuous_cos ?_)
        apply Continuous.mul continuous_const (Continuous.subtype_val continuous_fst)
      · apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
    constructor
    · apply Continuous.mul ?_ (Continuous.comp' continuous_sin ?_)
      · apply Continuous.add continuous_const (Continuous.comp' continuous_cos ?_)
        apply Continuous.mul continuous_const (Continuous.subtype_val continuous_fst)
      · apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
    constructor
    all_goals
      apply Continuous.mul ?_ (Continuous.comp' continuous_sin
        (Continuous.mul continuous_const (Continuous.subtype_val continuous_fst)))
    · apply Continuous.comp' continuous_cos ?_
      apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
    · apply Continuous.comp' continuous_sin ?_
      apply Continuous.mul continuous_const (Continuous.subtype_val continuous_snd)
  · -- map⁻¹ is continuous
    simp [Equiv.coe_ofInjective_symm]
    sorry

end KleinBottle.embedding
end KleinBottle
