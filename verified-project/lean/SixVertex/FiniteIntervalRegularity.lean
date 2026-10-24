import SixVertex.FiniteIntervalSymmetry
import SixVertex.ResolventDerivative

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def finiteIntervalDensityPrimeFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) : BoundedRealFunction :=
  physicalKernelPrimeFunction (lam/2) (by linarith) (by linarith [Real.pi_pos])-
    boundedConvolution (windowedFunction Q (finiteIntervalDensity lam h0 hpi Q))
      (windowedFunction_integrable Q _) (physicalKernelPrimeFunction lam h0 hpi)

theorem finiteIntervalDensityPrimeFunction_apply (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q u : ℝ) : finiteIntervalDensityPrimeFunction lam h0 hpi Q u=
      kernelSPrime lam u-(∫ v in Icc (-Q) Q, kernelKPrime lam (u-v)*finiteIntervalDensity lam h0 hpi Q v) := by
  change kernelSPrime lam u-(∫ v : ℝ, windowedFunction Q (finiteIntervalDensity lam h0 hpi Q) v*kernelKPrime lam (u-v))=_
  have he : (fun v => windowedFunction Q (finiteIntervalDensity lam h0 hpi Q) v*kernelKPrime lam (u-v))=
      (Icc (-Q) Q).indicator (fun v => kernelKPrime lam (u-v)*finiteIntervalDensity lam h0 hpi Q v) := by
    funext v
    by_cases hv : v ∈ Icc (-Q) Q <;> simp [windowedFunction,hv,mul_comm]
  rw [he,integral_indicator measurableSet_Icc]

/-- Genuine differentiation of the actual finite-interval equation. -/
theorem finiteIntervalDensity_hasDerivAt (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q u : ℝ) : HasDerivAt (fun v => finiteIntervalDensity lam h0 hpi Q v)
      (finiteIntervalDensityPrimeFunction lam h0 hpi Q u) u := by
  let r := finiteIntervalDensity lam h0 hpi Q
  let c := boundedConvolution (windowedFunction Q r) (windowedFunction_integrable Q r) (physicalKernelFunction lam h0 hpi)
  have hc (x : ℝ) : c x=physicalWindowOperator lam h0 hpi Q r x := by
    change (∫ v : ℝ, windowedFunction Q r v*kernelK lam (x-v))=
      ∫ v : ℝ, kernelK lam (x-v)*windowedFunction Q r v
    simp only [mul_comm]
  have hr : (fun x => r x)=fun x => kernelS lam x-c x := by
    funext x
    rw [hc x,physicalWindowOperator_apply]
    linarith [finiteIntervalDensity_equation lam h0 hpi Q x]
  have hd := boundedConvolutionValue_hasDerivAt (windowedFunction Q r) (windowedFunction_integrable Q r)
    (physicalKernelFunction lam h0 hpi) (physicalKernelPrimeFunction lam h0 hpi)
    (fun x => hasDerivAt_kernelK lam x h0 hpi) u
  have hs := (hasDerivAt_kernelS lam u h0 hpi).sub hd
  change HasDerivAt (fun x => r x) _ u
  rw [hr]
  exact hs

theorem finiteIntervalDensityPrimeFunction_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) : Integrable (fun u => finiteIntervalDensityPrimeFunction lam h0 hpi Q u) := by
  exact (kernelSPrime_integrable lam h0 hpi).sub
    ((windowedFunction_integrable Q (finiteIntervalDensity lam h0 hpi Q)).integrable_convolution
      (L := ContinuousLinearMap.mul ℝ ℝ) (kernelKPrime_integrable lam h0 hpi))

/-- The relative derivative bound is uniform in Q and is proved from
the actual positive-kernel decomposition s+(-K)_Q r_Q. -/
theorem finiteIntervalDensityPrime_relative_bound (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q u : ℝ) :
    |finiteIntervalDensityPrimeFunction lam h0 hpi Q u| ≤
      kernelLogConstant lam*finiteIntervalDensity lam h0 hpi Q u := by
  let r := finiteIntervalDensity lam h0 hpi Q
  let C := kernelLogConstant lam
  have hCs : 2/(Real.sin (lam/2))^2 ≤ C := by
    dsimp [C,kernelLogConstant]
    have h : 0 ≤ 2/(Real.sin lam)^2 := by positivity
    linarith
  have hCk : 2/(Real.sin lam)^2 ≤ C := by
    dsimp [C,kernelLogConstant]
    have h : 0 ≤ 2/(Real.sin (lam/2))^2 := by positivity
    linarith
  have hr (v : ℝ) : 0 ≤ r v := (finiteIntervalDensity_pos lam h0 hhalf hpi Q v).le
  have hs : |kernelSPrime lam u| ≤ C*kernelS lam u :=
    (kernelSPrime_relative_bound lam u h0 hpi).trans
      (mul_le_mul_of_nonneg_right hCs (kernelS_pos lam u h0 hpi).le)
  have hpcont : Continuous (fun v : ℝ => kernelKPrime lam (u-v)*r v) :=
    ((physicalKernelPrimeFunction lam h0 hpi).continuous.comp (continuous_const.sub continuous_id)).mul r.continuous
  have hkcont : Continuous (fun v : ℝ => C*(-kernelK lam (u-v)*r v)) :=
    continuous_const.mul (((physicalKernelFunction lam h0 hpi).continuous.comp (continuous_const.sub continuous_id)).neg.mul r.continuous)
  have hpoint (v : ℝ) : |kernelKPrime lam (u-v)*r v| ≤ C*(-kernelK lam (u-v)*r v) := by
    rw [abs_mul,abs_of_nonneg (hr v)]
    have h := (kernelKPrime_relative_bound lam (u-v) h0 hpi).trans
      (mul_le_mul_of_nonneg_right hCk (abs_nonneg _))
    rw [abs_of_nonpos (kernelK_nonpos lam _ hhalf hpi)] at h
    apply (mul_le_mul_of_nonneg_right h (hr v)).trans_eq
    ring
  have hi : |∫ v in Icc (-Q) Q, kernelKPrime lam (u-v)*r v| ≤
      C*(-(∫ v in Icc (-Q) Q, kernelK lam (u-v)*r v)) := by
    calc
      _ ≤ ∫ v in Icc (-Q) Q, |kernelKPrime lam (u-v)*r v| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun v : ℝ => kernelKPrime lam (u-v)*r v)
      _ ≤ ∫ v in Icc (-Q) Q, C*(-kernelK lam (u-v)*r v) :=
        integral_mono hpcont.abs.integrableOn_Icc hkcont.integrableOn_Icc hpoint
      _ = _ := by
        rw [integral_const_mul]
        congr 1
        simp_rw [neg_mul]
        rw [integral_neg]
  rw [finiteIntervalDensityPrimeFunction_apply]
  calc
    _ ≤ |kernelSPrime lam u|+|∫ v in Icc (-Q) Q, kernelKPrime lam (u-v)*r v| := abs_sub _ _
    _ ≤ C*kernelS lam u+C*(-(∫ v in Icc (-Q) Q, kernelK lam (u-v)*r v)) := add_le_add hs hi
    _ = C*(kernelS lam u-(∫ v in Icc (-Q) Q, kernelK lam (u-v)*r v)) := by ring
    _ = _ := congrArg (fun x : ℝ => C*x) (by linarith [finiteIntervalDensity_equation lam h0 hpi Q u])

end
end SixVertex

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem finiteIntervalDensity_log_lipschitz (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q u v : ℝ) :
    |Real.log (finiteIntervalDensity lam h0 hpi Q v)-Real.log (finiteIntervalDensity lam h0 hpi Q u)| ≤
      kernelLogConstant lam*|v-u| := by
  have hd (x : ℝ) : HasDerivAt (fun y => Real.log (finiteIntervalDensity lam h0 hpi Q y))
      (finiteIntervalDensityPrimeFunction lam h0 hpi Q x/finiteIntervalDensity lam h0 hpi Q x) x :=
    (finiteIntervalDensity_hasDerivAt lam h0 hpi Q x).log (finiteIntervalDensity_pos lam h0 hhalf hpi Q x).ne'
  have hb (x : ℝ) : ‖finiteIntervalDensityPrimeFunction lam h0 hpi Q x/finiteIntervalDensity lam h0 hpi Q x‖ ≤ kernelLogConstant lam := by
    have hp := finiteIntervalDensity_pos lam h0 hhalf hpi Q x
    rw [Real.norm_eq_abs,abs_div,abs_of_pos hp]
    exact (div_le_iff₀ hp).mpr (finiteIntervalDensityPrime_relative_bound lam h0 hhalf hpi Q x)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (univ : Set ℝ)) => (hd x).hasDerivWithinAt)
    (fun x (_ : x ∈ (univ : Set ℝ)) => hb x)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ u) (mem_univ v)
  simpa only [Real.norm_eq_abs] using h

theorem finiteIntervalDensity_exponential_comparison (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q u v : ℝ) :
    Real.exp (-(kernelLogConstant lam*|v-u|))*finiteIntervalDensity lam h0 hpi Q u ≤
      finiteIntervalDensity lam h0 hpi Q v ∧
      finiteIntervalDensity lam h0 hpi Q v ≤
        Real.exp (kernelLogConstant lam*|v-u|)*finiteIntervalDensity lam h0 hpi Q u := by
  have hu := finiteIntervalDensity_pos lam h0 hhalf hpi Q u
  have hv := finiteIntervalDensity_pos lam h0 hhalf hpi Q v
  have hh := abs_le.mp (finiteIntervalDensity_log_lipschitz lam h0 hhalf hpi Q u v)
  have hlo := Real.exp_le_exp.mpr hh.1
  have hhi := Real.exp_le_exp.mpr hh.2
  rw [Real.exp_sub,Real.exp_log hv,Real.exp_log hu] at hlo hhi
  exact ⟨(le_div_iff₀ hu).mp hlo,(div_le_iff₀ hu).mp hhi⟩

end
end SixVertex
