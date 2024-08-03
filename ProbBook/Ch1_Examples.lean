import ProbBook.Ch1

-- Example 1.7
namespace Example_1_7

inductive Coin2 where
  | HH
  | HT
  | TH
  | TT
  deriving Fintype

open Coin2

@[simp]
noncomputable
instance dist : DiscreteDistFunc Coin2 := {
  m := fun (x : Coin2) => 1/4
  hp := by simp
  hu := by
    rw [one_div, tsum_const]
    have hc : Nat.card Coin2 = 4 := by aesop
    rw [hc]
    norm_num
}


lemma dist_pairwise : Pairwise (fun (x y : Coin2) => dist.m x = dist.m y) := by
  exact fun ⦃i j⦄ ↦ congrFun rfl

def E : Finset Coin2 := ⟨{HH,HT,TH},by simp⟩

example : P (E : Set Coin2) = 3/4 := by
  rw [P]
  aesop

def F : Finset Coin2 := ⟨{HH,HT},by simp⟩

example : P (F : Set Coin2) = 2/4 := by
  rw [P, dist]
  aesop

end Example_1_7
