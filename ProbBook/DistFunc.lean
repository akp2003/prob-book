import ProbBook.Ch1

namespace DistFunc

theorem P_le_of_subset [d : DistFunc Ω] (A B : Set Ω) (hs : A ⊆ B):
    P A ≤ P B := by
  let C := Aᶜ ∩ B
  have hd : Disjoint A C := by
    unfold_let
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    aesop
  have hunion : A ∪ C = B := by
    unfold_let
    rw [Set.union_inter_distrib_left]
    simp
    exact hs
  have hPB : P B = P A + P C  := by
    unfold P
    rw [← d.h3 A C hd]
    unfold_let
    rw [hunion]
  rw [hPB]
  simp [d.hp]
  exact d.hp C

theorem P_inter_eq_zero_left [d : DistFunc Ω] (A B : Set Ω) (hA : P A = 0) : P (A ∩ B) = 0 := by
    rw [eq_iff_le_not_lt]
    constructor
    · rw [← hA]
      exact P_le_of_subset (A ∩ B) A (by simp)
    · rw [not_lt]
      exact d.hp (A ∩ B)

theorem P_inter_eq_zero_of_or [d : DistFunc Ω] {E : Set Ω} {F : Set Ω} (h : (P E = 0) ∨ (P F = 0)):
    P (E ∩ F) = 0 := by
  cases h with
  | inl h => exact P_inter_eq_zero_left E F h
  | inr h => rw [Set.inter_comm] ; exact P_inter_eq_zero_left F E h

end DistFunc
