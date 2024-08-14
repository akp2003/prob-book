import ProbBook.Ch1
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib
open MeasureTheory Filter Set ProbabilityTheory Topology

-- Definition 2.1
class ContinuousDistFunc :=
  -- f is not necessarily continuous
  f : ℝ → ℝ
  hp (x : ℝ) : f x ≥ 0
  hu : ∫ (x : ℝ), f x = 1

@[simp]
noncomputable
instance ContinuousDistFunc.toDistFunc [d : ContinuousDistFunc] : DistFunc ℝ := {
  prob := fun (E : Set ℝ) => ∫ x in E, f x
  hp := by
    intro E
    exact integral_nonneg hp
  hu := by
    simp only [Measure.restrict_univ]
    exact hu
}

namespace ContinuousDistFunc

-- Some simple lemmas
lemma P_empty [ContinuousDistFunc] : P (∅ : Set ℝ) = 0 := by
  unfold P
  simp

@[simp]
lemma f_Integrable [d : ContinuousDistFunc] : Integrable f := integrable_of_integral_eq_one d.hu

-- This theorem reminds me of DiscreteDistFunc.summable_set
@[simp]
lemma f_Integrable_restrict [d : ContinuousDistFunc] (E : Set ℝ): Integrable f (volume.restrict E) := by
  rw [Integrable]
  have hnz : ∫ (x : ℝ), f x ≠ 0 := by
    rw [d.hu]
    exact Ne.symm (zero_ne_one' ℝ)
  have h1 : AEStronglyMeasurable f := by exact not_imp_comm.1 integral_non_aestronglyMeasurable hnz
  constructor
  · exact AEStronglyMeasurable.restrict h1
  · exact HasFiniteIntegral.restrict f_Integrable.right

@[simp]
lemma f_IntegrableOn [d : ContinuousDistFunc] (E : Set ℝ): IntegrableOn f E := by
  rw [IntegrableOn]
  exact f_Integrable_restrict E

@[simp]
lemma f_EventuallyLE_ae [d : ContinuousDistFunc] (E : Set ℝ): 0 ≤ᶠ[ae (volume.restrict E)] f := by
  rw [EventuallyLE.eq_1]
  simp [d.hp]

-- Definition 2.2
def F [DistFunc ℝ] (x : ℝ) : ℝ := P {X | X ≤ x}

-- Some useful lemmas
lemma F_nonneg [d : ContinuousDistFunc] (x : ℝ):
    0 ≤ F x := by
  unfold F P
  exact DistFunc.hp {X | X ≤ x}

lemma F_integral [d : ContinuousDistFunc] :
    F = fun x => ∫ t in Iic x, d.f t := by
  exact rfl

lemma F_integral' [d : ContinuousDistFunc] :
    F x = ∫ t in Iic x, d.f t := by
  exact rfl

lemma F_mono [d : ContinuousDistFunc] :
    Monotone F := by
  rw [F_integral]
  rw [monotone_iff_forall_lt]
  intro a b ab
  have hs : Iic a ⊆ Iic b := by
    rw [@Iic_subset_Iic]
    exact le_of_lt ab
  rel [setIntegral_mono_set (f_IntegrableOn (Iic b)) (f_EventuallyLE_ae (Iic b)) (HasSubset.Subset.eventuallyLE hs)]

-- Thanks to Etienne Marion
lemma tendsto_setintegral_Iic_atBot_zero {f : ℝ → ℝ} (hf : Integrable f) :
    Tendsto (fun x ↦ ∫ (t : ℝ) in Iic x, f t) atBot (𝓝 0) := by
  have this (x : ℝ) : ∫ t in Iic x, f t = ∫ t, (Iic x).indicator f t :=
    (integral_indicator measurableSet_Iic).symm
  simp_rw [this]
  rw [← integral_zero]
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ ‖f x‖)
  · exact eventually_of_forall fun x ↦ hf.aestronglyMeasurable.indicator measurableSet_Iic
  · exact eventually_of_forall fun x ↦ eventually_of_forall fun y ↦ norm_indicator_le_norm_self _ _
  · exact hf.norm
  · refine eventually_of_forall fun x ↦ tendsto_const_nhds.congr' ?_
    rw [EventuallyEq, eventually_atBot]
    refine ⟨x - 1, fun y hy ↦ ?_⟩
    simp [Set.indicator, (by linarith : ¬x ≤ y)]

lemma F_tendsto_atBot_inf [d : ContinuousDistFunc] :
    Tendsto F atBot (𝓝 0) := by
  rw [F_integral]
  exact tendsto_setintegral_Iic_atBot_zero f_Integrable

-- Theorem 2.1
theorem F_deriv_eq_f [d : ContinuousDistFunc] (x : ℝ) :
    deriv F = f  := by
  rw [F_integral]
  sorry

end ContinuousDistFunc
