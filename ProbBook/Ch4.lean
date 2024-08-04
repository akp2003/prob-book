import ProbBook.DistFunc

variable {Ω : Type u}

-- A Notation for conditional probability
notation "P ⟦" s "|" t "⟧" => P (s ∩ t) / P t

--Definition 4.1
@[simp]
def Independent [DistFunc Ω] (E : Set Ω) (F : Set Ω) : Prop :=
  (P F ≠ 0 ∧ P E ≠ 0 ∧ (P ⟦E | F⟧ = P E) ∧ (P ⟦F | E⟧ = P F)) ∨ (P E = 0 ∨ P F = 0)

--Theorem 4.1
theorem Independent_iff_P_inter [d : DistFunc Ω] (E : Set Ω) (F : Set Ω) :
    Independent E F ↔ P (E ∩ F) = P E * P F := by
  by_cases hzero : (P E = 0) ∨ (P F = 0)
  · constructor
    · intro
      rw [DistFunc.P_inter_eq_zero_of_or hzero]
      exact zero_eq_mul.mpr hzero
    · intro
      rw [Independent]
      right
      exact hzero
  · constructor
    · rw [Independent]
      intro h
      apply symm
      calc
        P E * P F = P ⟦E | F⟧ * P F := by rw [← (Or.resolve_right h hzero).2.2.1]
        _ = P (E ∩ F) := by rw [div_mul_cancel₀] ; exact (Or.resolve_right h hzero).1
    · intro h
      rw [Independent]
      simp at hzero
      obtain ⟨hE,hF⟩ := hzero
      left
      have hEF :  P ⟦E | F⟧ = P E := by exact (eq_div_of_mul_eq hF (id (Eq.symm h))).symm
      have hFE :  P ⟦F | E⟧ = P F := by
        rw [Set.inter_comm] at h
        aesop
      exact ⟨hF,hE,hEF,hFE⟩
