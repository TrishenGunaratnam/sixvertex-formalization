import SixVertex.BoundedConvolution
import SixVertex.WeightedKernel

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- The kernel obtained by conjugation with exp(a*x). This uses the
signed spatial argument, as required by conjugation, not its modulus. -/
def weightedKernel (lam a u : ℝ) : ℝ := Real.exp (a*u)*kernelK lam u

theorem weightedKernel_abs_bound (lam a r u : ℝ) (ha : |a| ≤ r) :
    |weightedKernel lam a u| ≤ weightedKernelAbs lam r u := by
  have hp : a*u ≤ r*|u| := by
    calc
      _ ≤ |a*u| := le_abs_self _
      _ = |a| *|u| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_right ha (abs_nonneg _)
  unfold weightedKernel weightedKernelAbs
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hp) (abs_nonneg _)

theorem weightedKernel_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (r : ℝ) (hr : r ≤ 1) (a : ℝ) (ha : |a| ≤ r) : Integrable (weightedKernel lam a) := by
  have hk : Continuous (kernelK lam) :=
    continuous_phaseDensity lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  apply (weightedKernelAbs_integrable lam h0 hpi r hr).mono' (by unfold weightedKernel; fun_prop)
  exact Eventually.of_forall (fun u => by
    simpa only [Real.norm_eq_abs] using weightedKernel_abs_bound lam a r u ha)

theorem weightedKernel_mass_bound (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (r : ℝ) (hr : r ≤ 1) (a : ℝ) (ha : |a| ≤ r) :
    kernelL1Mass (weightedKernel lam a) ≤ weightedKernelMass lam r := by
  apply integral_mono_ae (weightedKernel_integrable lam h0 hpi r hr a ha).abs
    (weightedKernelAbs_integrable lam h0 hpi r hr)
  exact Eventually.of_forall (fun u => weightedKernel_abs_bound lam a r u ha)

/-- The same positive weight controls both conjugation signs, and every
intermediate exponent. All inverses are constructed by actual Neumann
series on bounded continuous functions with one common norm bound. -/
theorem exists_uniform_weighted_kernel_inverses (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ weightedKernelMass lam r < 1 ∧
      ∀ a : ℝ, |a| ≤ r → ∃ hk : Integrable (weightedKernel lam a),
        ∃ B : BoundedRealFunction →L[ℝ] BoundedRealFunction,
          B*(1+boundedConvolutionOperator (weightedKernel lam a) hk)=1 ∧
          (1+boundedConvolutionOperator (weightedKernel lam a) hk)*B=1 ∧
          ‖B‖ ≤ (1-weightedKernelMass lam r)⁻¹ := by
  obtain ⟨r,hr0,hr1,hi,hm⟩:=exists_positive_weight_kernel_contraction lam h0 hpi
  refine ⟨r,hr0,hr1,hm,?_⟩
  intro a ha
  have hk:=weightedKernel_integrable lam h0 hpi r hr1.le a ha
  have hmass:=weightedKernel_mass_bound lam h0 hpi r hr1.le a ha
  have hsmall : kernelL1Mass (weightedKernel lam a) < 1 := hmass.trans_lt hm
  refine ⟨hk,boundedConvolutionInverse _ hk,boundedConvolutionInverse_left _ hk hsmall,
    boundedConvolutionInverse_right _ hk hsmall,?_⟩
  apply (boundedConvolutionInverse_norm_bound _ hk hsmall).trans
  simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hm) (sub_le_sub_left hmass 1)

end
end SixVertex
