import ProbBook.Ch1
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Probability.Cdf
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.FundThmCalculus

open MeasureTheory Filter Set ProbabilityTheory Topology ProbabilityTheory

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

-- Definition 2.2
def F [DistFunc ℝ] (x : ℝ) : ℝ := P {X | X ≤ x}

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

-- This is a specific version of FTC
theorem HasDerivAt_integral_Iic {f : ℝ → ℝ} (c : ℝ)
  (hint : Integrable f) (hc : Continuous f):
    HasDerivAt (fun u => ∫ x : ℝ in Iic u, f x) (f c) c := by
  have hmIic {x : ℝ} : MeasurableSet (Iic x) := measurableSet_Iic
  have hmdiff {x : ℝ} : MeasurableSet ((Iic 0) \ (Ioc x 0)) := by simp
  have hmIoc {x y : ℝ} : MeasurableSet (Ioc x y) := by simp
  have hIic (x : ℝ) : (Iic x) = ((Iic 0) \ (Ioc x 0)) ∪ (Ioc 0 x)  := by
    ext y
    -- I used aesop
    simp_all only [measurableSet_Iic, implies_true, MeasurableSet.diff, measurableSet_Ioc, mem_Iic, mem_union,
      mem_diff, mem_Ioc, not_and, not_le]
    apply Iff.intro
    · intro a
      simp_all only [isEmpty_Prop, not_lt, IsEmpty.forall_iff, and_true]
      exact le_or_lt y 0
    · intro a
      cases a with
      | inl h =>
        obtain ⟨left, right⟩ := h
        exact le_imp_le_of_lt_imp_lt right left
      | inr h_1 => simp_all only
  simp_rw [(integral_indicator hmIic).symm]
  -- I used show_term simp_rw [hIic]
  refine Eq.mpr (id (congrArg (fun x ↦ HasDerivAt x (f c) c) (funext fun u ↦ congrArg (integral volume) (funext fun t ↦ congrArg (fun x ↦ x.indicator f t) ((fun x ↦ hIic x) u))))) ?_
  have hInter {x : ℝ} : Disjoint ((Iic 0) \ (Ioc x 0)) (Ioc 0 x) := by
    rw [disjoint_iff_inter_eq_empty]
    ext y
    simp
    intro y0 _ h1
    exact lt_imp_lt_of_le_imp_le (fun _ ↦ y0) h1
  simp_rw [indicator_union_of_disjoint hInter]
  simp_rw [integral_add (Integrable.indicator hint hmdiff) (Integrable.indicator hint hmIoc)]
  have hsub {x : ℝ} : (Ioc x 0) ⊆ (Iic 0) := by exact Ioc_subset_Iic_self
  simp_rw [indicator_diff hsub]
  have hInt1 {_ : ℝ} : Integrable ((Iic 0).indicator f) := by
    exact Integrable.indicator hint hmIic
  have hInt2 {u : ℝ} : Integrable ((Ioc u 0).indicator f) := by
    exact (Integrable.indicator hint hmIoc)
  have h1 {u : ℝ} : (∫ (a : ℝ), (Iic 0).indicator f a - (Ioc u 0).indicator f a) =
    ((∫ (a : ℝ), (Iic 0).indicator f a) - (∫ (a : ℝ), (Ioc u 0).indicator f a)) := by
    rw [integral_sub hInt1 hInt2]
    exact f (f (f (f c))) -- I don't know what this is :|
  simp only [Pi.sub_apply]
  simp_rw [h1]
  set A : ℝ :=  (∫ (a : ℝ), (Iic 0).indicator f a)
  have h2 {u : ℝ} : (A - ∫ (a : ℝ), (Ioc u 0).indicator f a) + ∫ (a : ℝ), (Ioc 0 u).indicator f a =
      ((∫ (a : ℝ), (Ioc 0 u).indicator f a) - (∫ (a : ℝ), (Ioc u 0).indicator f a)) + A := by
    rw [sub_add_comm]
  simp_rw [h2]
  have hderiv : HasDerivAt (fun u ↦ ((∫ (a : ℝ), (Ioc 0 u).indicator f a) - ∫ (a : ℝ), (Ioc u 0).indicator f a)) (f c) c := by
    simp_rw [(integral_indicator hmIoc)]
    have h {u : ℝ} : ∫ (x : ℝ) in Ioc 0 u, f x ∂volume - ∫ (x : ℝ) in Ioc u 0, f x ∂volume =
      intervalIntegral f 0 u volume := by
      exact rfl
    simp_rw [h]
    exact (Continuous.integral_hasStrictDerivAt hc 0 c).hasDerivAt
  exact HasDerivAt.add_const hderiv A

theorem Continuous.deriv_integral_Iic {f : ℝ → ℝ} (c : ℝ)
  (hint : Integrable f) (hc : Continuous f):
    deriv (fun u => ∫ x : ℝ in Iic u, f x) c = (f c) := by
  exact (HasDerivAt_integral_Iic c hint hc).deriv


-- Theorem 2.1
theorem F_deriv_eq_f [d : ContinuousDistFunc] (x : ℝ)
  (hc : Continuous f):
    deriv F x = f x  := by
  rw [F_integral]
  exact Continuous.deriv_integral_Iic x f_Integrable hc


end ContinuousDistFunc
