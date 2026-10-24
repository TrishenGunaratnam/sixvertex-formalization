import SixVertex.WindowConvolution
import SixVertex.PositiveNeumann

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set

def exteriorConvolutionOperator (k : BoundedRealFunction) (hk : Integrable (fun x => k x))
    (Q : ℝ) : BoundedRealFunction →L[ℝ] BoundedRealFunction :=
  boundedConvolutionOperator (fun x => k x) hk-windowConvolutionOperator k hk Q

/-- The actual complement-window integral represented by the operator. -/
theorem exteriorConvolutionOperator_apply (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (Q : ℝ) (f : BoundedRealFunction) (u : ℝ) :
    exteriorConvolutionOperator k hk Q f u=
      ∫ v in (Icc (-Q) Q)ᶜ,k (u-v)*f v := by
  have hi : Integrable (fun v : ℝ => k (u-v)*f v) :=
    (hk.comp_sub_left u).mul_bdd f.continuous.aestronglyMeasurable
      (Eventually.of_forall f.norm_coe_le_norm)
  have hw : boundedConvolutionOperator (fun x => k x) hk f u=
      ∫ v : ℝ,k (u-v)*f v := by
    change (∫ t : ℝ,k t*f (u-t))=_
    have he := integral_sub_left_eq_self (fun v : ℝ => k (u-v)*f v) volume u
    simpa only [sub_sub_cancel] using he
  change boundedConvolutionOperator (fun x => k x) hk f u-
    windowConvolutionOperator k hk Q f u=_
  rw [hw,windowConvolutionOperator_apply]
  have he := integral_add_compl (s := Icc (-Q) Q) measurableSet_Icc hi
  linarith

/-- The complement-window operator keeps the full kernel L1 bound. -/
theorem exteriorConvolutionOperator_value_bound (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (Q : ℝ) (f : BoundedRealFunction) (u : ℝ) :
    ‖exteriorConvolutionOperator k hk Q f u‖ ≤ kernelL1Mass (fun x => k x)*‖f‖ := by
  let F : ℝ → ℝ := (Icc (-Q) Q)ᶜ.indicator (fun v => f v)
  have hF : AEStronglyMeasurable F := f.continuous.aestronglyMeasurable.indicator measurableSet_Icc.compl
  have hb (v : ℝ) : ‖F v‖ ≤ ‖f‖ := by
    by_cases hv : v ∈ (Icc (-Q) Q)ᶜ
    · simpa only [F,indicator_of_mem hv] using f.norm_coe_le_norm v
    · simp only [F,indicator_of_notMem hv,norm_zero]
      exact norm_nonneg f
  have he : (fun v : ℝ => k (u-v)*F v)=
      (Icc (-Q) Q)ᶜ.indicator (fun v => k (u-v)*f v) := by
    funext v
    by_cases hv : v ∈ (Icc (-Q) Q)ᶜ <;> simp [F,hv]
  rw [exteriorConvolutionOperator_apply,← integral_indicator measurableSet_Icc.compl,← he]
  exact bounded_measurable_convolution_bound (fun x => k x) F hk hF ‖f‖ hb u

/-- Uniform operator bound independent of the cutoff. -/
theorem exteriorConvolutionOperator_norm_bound (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (Q : ℝ) :
    ‖exteriorConvolutionOperator k hk Q‖ ≤ kernelL1Mass (fun x => k x) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (kernelL1Mass_nonneg _)
  intro f
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (kernelL1Mass_nonneg _) (norm_nonneg f))).mpr
  exact exteriorConvolutionOperator_value_bound k hk Q f

/-- Positivity holds for the actual exterior integral. -/
theorem exteriorConvolutionOperator_nonnegative (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (hpos : ∀ x,0 ≤ k x) (Q : ℝ)
    (f : BoundedRealFunction) (hf : ∀ x,0 ≤ f x) (u : ℝ) :
    0 ≤ exteriorConvolutionOperator k hk Q f u := by
  rw [exteriorConvolutionOperator_apply]
  exact integral_nonneg (fun v => mul_nonneg (hpos (u-v)) (hf v))

end
end SixVertex
