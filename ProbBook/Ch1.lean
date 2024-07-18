import Mathlib.Init.Set
import Mathlib.Topology.Instances.ENNReal

-- Definition 1.2
structure DistFunc (Ω : Type u) where
  m : Ω → ℝ
  hp : m ω ≥ 0
  hs : (∑' ω, (m ω)) = 1

noncomputable
def Prob {Ω : Type u} (df : DistFunc Ω) (E : Set Ω) := (∑' (ω : E), (df.m ω))
