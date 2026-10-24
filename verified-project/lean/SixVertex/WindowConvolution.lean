import SixVertex.CountingDiscrepancyKernel
import SixVertex.ConvolutionDerivative

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def windowedFunction (Q : ℝ) (f : BoundedRealFunction) : ℝ → ℝ :=
  (Icc (-Q) Q).indicator (fun x => f x)

theorem windowedFunction_integrable (Q : ℝ) (f : BoundedRealFunction) :
    Integrable (windowedFunction Q f) :=
  (f.continuous.integrableOn_Icc (μ := volume)).integrable_indicator measurableSet_Icc

theorem windowedFunction_norm_bound (Q : ℝ) (f : BoundedRealFunction) (x : ℝ) :
    ‖windowedFunction Q f x‖ ≤ ‖f‖ := by
  by_cases hx : x ∈ Icc (-Q) Q
  · change ‖(Icc (-Q) Q).indicator (fun x => f x) x‖ ≤ ‖f‖
    rw [Set.indicator_of_mem hx]
    exact f.norm_coe_le_norm x
  · rw [windowedFunction,Set.indicator_of_notMem hx,norm_zero]
    exact norm_nonneg _

def windowConvolutionValue (k : BoundedRealFunction) (Q : ℝ) (f : BoundedRealFunction) (u : ℝ) : ℝ :=
  ∫ v : ℝ, k (u-v)*windowedFunction Q f v

theorem windowConvolutionValue_eq_integral (k : BoundedRealFunction) (Q : ℝ)
    (f : BoundedRealFunction) (u : ℝ) :
    windowConvolutionValue k Q f u=∫ v in Icc (-Q) Q, k (u-v)*f v := by
  unfold windowConvolutionValue
  have he : (fun v : ℝ => k (u-v)*windowedFunction Q f v)=
      (Icc (-Q) Q).indicator (fun v => k (u-v)*f v) := by
    funext v
    by_cases hv : v ∈ Icc (-Q) Q <;> simp [windowedFunction,hv]
  rw [he,integral_indicator measurableSet_Icc]

theorem continuous_windowConvolutionValue (k : BoundedRealFunction) (Q : ℝ)
    (f : BoundedRealFunction) : Continuous (windowConvolutionValue k Q f) := by
  have he : windowConvolutionValue k Q f=boundedConvolutionValue (windowedFunction Q f) k := by
    funext u
    change (∫ v : ℝ, k (u-v)*windowedFunction Q f v)=∫ v : ℝ, windowedFunction Q f v*k (u-v)
    simp only [mul_comm]
  rw [he]
  exact continuous_boundedConvolutionValue _ (windowedFunction_integrable Q f) k

theorem windowConvolutionValue_bound (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) (f : BoundedRealFunction) (u : ℝ) :
    ‖windowConvolutionValue k Q f u‖ ≤ kernelL1Mass (fun x => k x)*‖f‖ :=
  bounded_measurable_convolution_bound (fun x => k x) (windowedFunction Q f) hk
    (windowedFunction_integrable Q f).aestronglyMeasurable ‖f‖ (windowedFunction_norm_bound Q f) u


def windowConvolution (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) (f : BoundedRealFunction) : BoundedRealFunction :=
  BoundedContinuousFunction.ofNormedAddCommGroup (windowConvolutionValue k Q f)
    (continuous_windowConvolutionValue k Q f) (kernelL1Mass (fun x => k x)*‖f‖)
    (windowConvolutionValue_bound k hk Q f)

theorem windowConvolution_norm_bound (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) (f : BoundedRealFunction) :
    ‖windowConvolution k hk Q f‖ ≤ kernelL1Mass (fun x => k x)*‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (kernelL1Mass_nonneg _) (norm_nonneg _))).mpr
  exact windowConvolutionValue_bound k hk Q f

def windowConvolutionLinear (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) : BoundedRealFunction →ₗ[ℝ] BoundedRealFunction where
  toFun := windowConvolution k hk Q
  map_add' := by
    intro f g
    ext u
    change (∫ v : ℝ, k (u-v)*windowedFunction Q (f+g) v)=
      (∫ v : ℝ, k (u-v)*windowedFunction Q f v)+(∫ v : ℝ, k (u-v)*windowedFunction Q g v)
    have he (v : ℝ) : k (u-v)*windowedFunction Q (f+g) v=
        k (u-v)*windowedFunction Q f v+k (u-v)*windowedFunction Q g v := by
      by_cases hv : v ∈ Icc (-Q) Q <;> simp [windowedFunction,hv,mul_add]
    simp_rw [he]
    apply integral_add
    · exact bounded_measurable_convolution_integrable (fun x => k x) _ hk
        (windowedFunction_integrable Q f).aestronglyMeasurable ‖f‖ (windowedFunction_norm_bound Q f) u
    · exact bounded_measurable_convolution_integrable (fun x => k x) _ hk
        (windowedFunction_integrable Q g).aestronglyMeasurable ‖g‖ (windowedFunction_norm_bound Q g) u
  map_smul' := by
    intro c f
    ext u
    change (∫ v : ℝ, k (u-v)*windowedFunction Q (c • f) v)=c*(∫ v : ℝ, k (u-v)*windowedFunction Q f v)
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro v
    by_cases hv : v ∈ Icc (-Q) Q <;> simp [windowedFunction,hv,mul_left_comm]

def windowConvolutionOperator (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) : BoundedRealFunction →L[ℝ] BoundedRealFunction :=
  (windowConvolutionLinear k hk Q).mkContinuous (kernelL1Mass (fun x => k x))
    (windowConvolution_norm_bound k hk Q)

theorem windowConvolutionOperator_apply (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) (f : BoundedRealFunction) (u : ℝ) :
    windowConvolutionOperator k hk Q f u=∫ v in Icc (-Q) Q, k (u-v)*f v :=
  windowConvolutionValue_eq_integral k Q f u

theorem windowConvolutionOperator_norm_bound (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) : ‖windowConvolutionOperator k hk Q‖ ≤ kernelL1Mass (fun x => k x) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (kernelL1Mass_nonneg _)
  exact windowConvolution_norm_bound k hk Q


def windowConvolutionInverse (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) : BoundedRealFunction →L[ℝ] BoundedRealFunction :=
  ∑' m : ℕ, (-(windowConvolutionOperator k hk Q))^m

theorem windowConvolutionInverse_left (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (hm : kernelL1Mass (fun x => k x) < 1) (Q : ℝ) :
    windowConvolutionInverse k hk Q*(1+windowConvolutionOperator k hk Q)=1 :=
  operator_neumann_left _ ((windowConvolutionOperator_norm_bound k hk Q).trans_lt hm)

theorem windowConvolutionInverse_right (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (hm : kernelL1Mass (fun x => k x) < 1) (Q : ℝ) :
    (1+windowConvolutionOperator k hk Q)*windowConvolutionInverse k hk Q=1 :=
  operator_neumann_right _ ((windowConvolutionOperator_norm_bound k hk Q).trans_lt hm)

theorem windowConvolutionInverse_norm_bound (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (hm : kernelL1Mass (fun x => k x) < 1) (Q : ℝ) :
    ‖windowConvolutionInverse k hk Q‖ ≤ (1-kernelL1Mass (fun x => k x))⁻¹ := by
  have hn := windowConvolutionOperator_norm_bound k hk Q
  apply (operator_neumann_norm_bound _ (hn.trans_lt hm)).trans
  simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hm) (sub_le_sub_left hn 1)

theorem windowConvolutionInverse_solves (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (hm : kernelL1Mass (fun x => k x) < 1) (Q : ℝ) (f : BoundedRealFunction) :
    windowConvolutionInverse k hk Q f+
      windowConvolutionOperator k hk Q (windowConvolutionInverse k hk Q f)=f := by
  exact congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T f)
    (windowConvolutionInverse_right k hk hm Q)

/-- The finite-interval physical inverse has one norm bound for every Q.
Its kernel operator is the actual set integral, not an abstract input. -/
theorem physical_window_kernel_bounded_inverse (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) :
    ∃ B : BoundedRealFunction →L[ℝ] BoundedRealFunction,
      B*(1+windowConvolutionOperator (physicalKernelFunction lam h0 hpi) (kernelK_integrable lam h0 hpi) Q)=1 ∧
      (1+windowConvolutionOperator (physicalKernelFunction lam h0 hpi) (kernelK_integrable lam h0 hpi) Q)*B=1 ∧
      ‖B‖ ≤ (1-|1-2*lam/Real.pi|)⁻¹ := by
  have hm : kernelL1Mass (fun x => physicalKernelFunction lam h0 hpi x)<1 := kernelK_L1_mass_lt_one lam h0 hpi
  refine ⟨windowConvolutionInverse _ (kernelK_integrable lam h0 hpi) Q,
    windowConvolutionInverse_left _ _ hm Q,windowConvolutionInverse_right _ _ hm Q,?_⟩
  have hb := windowConvolutionInverse_norm_bound _ (kernelK_integrable lam h0 hpi) hm Q
  change _ ≤ (1-(∫ t : ℝ, |kernelK lam t|))⁻¹ at hb
  rw [integral_abs_kernelK lam h0 hpi] at hb
  exact hb

end
end SixVertex
