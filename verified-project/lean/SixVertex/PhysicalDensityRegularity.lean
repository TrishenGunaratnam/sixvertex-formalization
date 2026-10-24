import SixVertex.PositiveDensitySpatial
import SixVertex.PhysicalReferenceQuantiles
import SixVertex.RelativeKernelVariation

namespace SixVertex
noncomputable section
open Set

/-- One explicit relative-variation constant covers both kernel signs. -/
def physicalDensityLogConstant (lam : ℝ) : ℝ := kernelLogConstant lam+Real.pi/lam

theorem physicalDensityLogConstant_pos (lam : ℝ) (h0 : 0 < lam) :
    0 < physicalDensityLogConstant lam :=
  add_pos_of_nonneg_of_pos (kernelLogConstant_nonneg lam) (div_pos Real.pi_pos h0)

/-- The actual finite-window derivative has a cutoff-independent relative
bound throughout the physical parameter range. -/
theorem finiteIntervalDensityPrime_relative_bound_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q u : ℝ) :
    |finiteIntervalDensityPrimeFunction lam h0 hpi Q u| ≤
      physicalDensityLogConstant lam*finiteIntervalDensity lam h0 hpi Q u := by
  have hp := (finiteIntervalDensity_pos_all lam h0 hpi Q u).le
  by_cases hh : Real.pi/2 ≤ lam
  · apply (finiteIntervalDensityPrime_relative_bound lam h0 hh hpi Q u).trans
    apply mul_le_mul_of_nonneg_right _ hp
    unfold physicalDensityLogConstant
    have h := (div_pos Real.pi_pos h0).le
    linarith
  · apply (finiteIntervalDensityPrime_relative_bound_positiveK lam h0 (lt_of_not_ge hh) Q u).trans
    apply mul_le_mul_of_nonneg_right _ hp
    unfold physicalDensityLogConstant
    have h := kernelLogConstant_nonneg lam
    linarith

/-- The logarithm of the actual window density has one global Lipschitz
bound, fixed before the cutoff and the evaluation points. -/
theorem finiteIntervalDensity_log_lipschitz_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q u v : ℝ) :
    |Real.log (finiteIntervalDensity lam h0 hpi Q v)-Real.log (finiteIntervalDensity lam h0 hpi Q u)| ≤
      physicalDensityLogConstant lam*|v-u| := by
  have hd (x : ℝ) : HasDerivAt (fun y => Real.log (finiteIntervalDensity lam h0 hpi Q y))
      (finiteIntervalDensityPrimeFunction lam h0 hpi Q x/finiteIntervalDensity lam h0 hpi Q x) x :=
    (finiteIntervalDensity_hasDerivAt lam h0 hpi Q x).log (finiteIntervalDensity_pos_all lam h0 hpi Q x).ne'
  have hb (x : ℝ) : ‖finiteIntervalDensityPrimeFunction lam h0 hpi Q x/finiteIntervalDensity lam h0 hpi Q x‖ ≤
      physicalDensityLogConstant lam := by
    have hp := finiteIntervalDensity_pos_all lam h0 hpi Q x
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr (finiteIntervalDensityPrime_relative_bound_all lam h0 hpi Q x)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (univ : Set ℝ)) => (hd x).hasDerivWithinAt)
    (fun x (_ : x ∈ (univ : Set ℝ)) => hb x)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ u) (mem_univ v)
  simpa only [Real.norm_eq_abs] using h

/-- Actual spatial multiplicative comparison for both signs of K. -/
theorem finiteIntervalDensity_exponential_comparison_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q u v : ℝ) :
    Real.exp (-(physicalDensityLogConstant lam*|v-u|))*finiteIntervalDensity lam h0 hpi Q u ≤
      finiteIntervalDensity lam h0 hpi Q v ∧
    finiteIntervalDensity lam h0 hpi Q v ≤
      Real.exp (physicalDensityLogConstant lam*|v-u|)*finiteIntervalDensity lam h0 hpi Q u :=
  positive_function_exponential_comparison _ _ _ (finiteIntervalDensity_pos_all lam h0 hpi Q)
    (finiteIntervalDensity_hasDerivAt lam h0 hpi Q)
    (finiteIntervalDensityPrime_relative_bound_all lam h0 hpi Q) u v

end
end SixVertex
