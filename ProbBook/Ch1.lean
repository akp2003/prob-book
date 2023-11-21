import Mathlib.Init.Set
import Mathlib.Topology.Instances.ENNReal
import Mathlib.Tactic.DeriveFintype

variable {Ω : Type u}

-- Definition 1.2
structure DistFunc (Ω : Type u) where
  m : Ω → ℝ
  hp (ω : Ω) : m ω ≥ 0
  hs : (∑' ω, (m ω)) = 1

noncomputable
def P (dist : DistFunc Ω) (E : Set Ω) := (∑' (ω : E), (dist.m ω))

-- Example 1.7
namespace Example_1_7

inductive Coin2 where
  | HH
  | HT
  | TH
  | TT
  deriving Fintype

open Coin2

noncomputable
def dist : DistFunc Coin2 := {
  m := fun (x : Coin2) => 1/4
  hp := by simp
  hs := by
    rw [one_div, tsum_const]
    have hc : Nat.card Coin2 = 4 := by aesop
    rw [hc]
    norm_num
}

lemma dist_pairwise : Pairwise (fun (x y : Coin2) => dist.m x = dist.m y) := by
  exact fun ⦃i j⦄ ↦ congrFun rfl

def E : Finset Coin2 := ⟨{HH,HT,TH},by simp⟩

example : P dist E = 3/4 := by
  rw [P, dist]
  aesop

def F : Finset Coin2 := ⟨{HH,HT},by simp⟩

example : P dist F = 2/4 := by
  rw [P, dist]
  aesop

end Example_1_7

--Theorem 1.1
--1
theorem P_positivity (dist : DistFunc Ω) (E : Set Ω) (hsum : Summable fun i : E ↦ dist.m ↑i):
  P dist E ≥ 0 := by
  rw [P]
  have hp (ω : E) : dist.m ω ≥ 0 := by
    exact dist.hp ↑ω
  calc
    ∑' (ω : ↑E), dist.m ↑ω ≥ ∑' (i : ↑E), 0 := by rel [(tsum_le_tsum hp (summable_zero) (hsum))]
    _ ≥ 0 := by simp
