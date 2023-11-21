import ProbBook.Ch1
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis

open MeasureTheory

class ContinuousDistFunc :=
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
