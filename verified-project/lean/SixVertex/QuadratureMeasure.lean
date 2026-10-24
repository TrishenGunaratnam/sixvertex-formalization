import SixVertex.QuadratureLocalMass
import Mathlib.Basic.ENNReal.BigOperators

namespace SixVertex
noncomputable section
open Set MeasureTheory
open scoped ENNReal

/-- The actual positive atomic measure with inverse counting-density
weights. In the physical negative-kernel regime every weight is positive. -/
def rootQuadratureMeasure {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) : Measure ℝ :=
  Measure.sum (fun j : Fin n => ENNReal.ofReal ((countingSlope lam b L Y (Y j))⁻¹) • Measure.dirac (Y j))

theorem rootQuadratureMeasure_Icc {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (a z : ℝ) :
    rootQuadratureMeasure lam b L Y (Icc a z)=
      ENNReal.ofReal (∑ j ∈ rootsInInterval Y a z, (countingSlope lam b L Y (Y j))⁻¹) := by
  have hp (j : Fin n) : 0 ≤ (countingSlope lam b L Y (Y j))⁻¹ :=
    inv_nonneg.mpr (countingSlope_pos_nonpositiveK lam b L hL Y _ hhalf hpi).le
  rw [rootQuadratureMeasure,Measure.sum_apply_of_countable,tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => hp j)]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ measurableSet_Icc]
  rw [rootsInInterval,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : a ≤ Y j ∧ Y j ≤ z
  · have hm : Y j ∈ Icc a z := hj
    rw [if_pos hj,Set.indicator_of_mem hm]
    simp
  · have hm : Y j ∉ Icc a z := hj
    rw [if_neg hj,Set.indicator_of_notMem hm]
    simp

/-- Uniform interval mass for the actual quadrature measure, for all
finite negative-kernel root lists and every filling. -/
theorem rootQuadratureMeasure_interval_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0) (a z : ℝ) (haz : a ≤ z) :
    rootQuadratureMeasure lam b L Y (Icc a z) ≤
      ENNReal.ofReal ((Real.exp (kernelLogConstant lam*(z-a)))^2*(z-a)+
        Real.exp (kernelLogConstant lam*(z-a))/(-kernelK lam 0)) := by
  rw [rootQuadratureMeasure_Icc lam b L hL Y hhalf.le hpi a z]
  exact ENNReal.ofReal_le_ofReal (quadrature_interval_mass_bound lam b L hL Y hhalf hpi hroots a z haz)

/-- One constant chosen before all chains, fillings, real arrays and
unit intervals bounds the manuscript's actual positive measure nu_L. -/
theorem exists_uniform_unit_interval_quadrature_mass (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ), 0 < L →
      ∀ (Y : Fin n → ℝ), ConsecutiveRoots lam b L Y 0 → ∀ a : ℝ,
        rootQuadratureMeasure lam b L Y (Icc a (a+1)) ≤ ENNReal.ofReal C := by
  let C : ℝ := (Real.exp (kernelLogConstant lam))^2+Real.exp (kernelLogConstant lam)/(-kernelK lam 0)
  have hk : 0 < -kernelK lam 0 := neg_pos.mpr (kernelK_strict_neg lam 0 hhalf hpi)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro n b L hL Y hroots a
  have hh := rootQuadratureMeasure_interval_bound lam b L hL Y hhalf hpi hroots a (a+1) (by linarith)
  simpa only [add_sub_cancel_left,mul_one] using hh

end
end SixVertex
