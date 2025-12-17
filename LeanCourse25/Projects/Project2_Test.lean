import Mathlib.Topology.Basic
import Mathlib.RingTheory.Real.Irrational
import Mathlib.Topology.Constructions
open Topology Real

def I : Set Real := Set.Icc 0 1
instance instTopologicalSpaceI : TopologicalSpace I := instTopologicalSpaceSubtype

def kleinBottle : Type := sorry --Quotient.mk I
--instTopologicalSpaceQuotient
