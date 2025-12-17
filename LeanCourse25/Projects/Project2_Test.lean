import Mathlib.Topology.Basic
import Mathlib.RingTheory.Real.Irrational
open Topology Real

def I : Set Real := Set.Icc 0 1
#check TopologicalSpace.mk
lemma I_TopSp : TopologicalSpace I := by sorry

def kleinBottle [TopologicalSpace I] : Type* := sorry
--instTopologicalSpaceQuotient
