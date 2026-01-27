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

/--
The Klein bottle as a quotient of the unit square [0,1]×[0,1].
-/
def KleinBottle := Quotient KleinBottle.setoid

instance KleinBottle.instTopologicalSpace :
  TopologicalSpace KleinBottle := instTopologicalSpaceQuotient

section KleinBottle.embedding
/--
This creates an embedding of the Klein bottle into ℝ⁴ with a formula by
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

/--
An embedding of the Klein bottle into ℝ⁴.
-/
def KleinBottle.embedding : Set (ℝ×ℝ×ℝ×ℝ) := Set.range embedding.map

instance KleinBottle.embedding.instTopologicalSpace :
  TopologicalSpace KleinBottle.embedding := instTopologicalSpaceSubtype

/--
An isomorphism between the quotient KleinBottle and it's embedding
into ℝ⁴.
-/
noncomputable def KleinBottle.embedding.isom : KleinBottle ≃ embedding :=
  Equiv.ofInjective map injective

/--
A homeomorphism between the quotient KleinBottle and it's embedding
into ℝ⁴.
-/
noncomputable def KleinBottle.embedding.homeom : KleinBottle ≃ₜ embedding := by
  apply Homeomorph.mk (Equiv.ofInjective map injective) ?_ ?_
  · -- map is continuous
    apply Continuous.subtype_coind
    apply Continuous.quotient_lift
    simp only [continuous_prodMk]
    refine ⟨Continuous.mul ?_ (continuous_cos.comp' ?_),
      Continuous.mul ?_ (continuous_sin.comp' ?_),
      ?_, ?_⟩
    all_goals
      try
        apply continuous_const.add (continuous_cos.comp' ?_)
        apply continuous_const.mul continuous_fst.subtype_val
      try
        exact continuous_const.mul continuous_snd.subtype_val
    all_goals
      apply Continuous.mul ?_ (continuous_sin.comp'
        (continuous_const.mul continuous_fst.subtype_val))
    · apply continuous_cos.comp' ?_
      apply continuous_const.mul continuous_snd.subtype_val
    · apply continuous_sin.comp' ?_
      apply continuous_const.mul continuous_snd.subtype_val
  · -- map⁻¹ is continuous
    simp [Equiv.coe_ofInjective_symm]
    sorry

end KleinBottle.embedding
end KleinBottle
