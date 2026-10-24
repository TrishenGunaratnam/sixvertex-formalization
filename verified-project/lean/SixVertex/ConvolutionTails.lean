import SixVertex.PhysicalKernelTails
import SixVertex.ConvolutionDerivative

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter

/-- Translation of the actual half-line integral. -/
theorem kernelTail_translate (q : ℝ → ℝ) (Q v : ℝ) :
    (∫ u in Ioi Q, q (u-v))=kernelTail q (Q-v) := by
  have he : (fun u => (Ioi Q).indicator (fun u => q (u-v)) u)=
      fun u => (Ioi (Q-v)).indicator q (u-v) := by
    funext u
    by_cases hu : Q < u
    · have hv : Q-v < u-v := sub_lt_sub_right hu v
      simp [Set.indicator,hu,hv]
    · have hv : ¬Q-v < u-v := by linarith
      simp [Set.indicator,hu,hv]
  rw [← integral_indicator measurableSet_Ioi,he,integral_sub_right_eq_self]
  exact integral_indicator measurableSet_Ioi

/-- Fubini for the true half-line tail of a scalar convolution, together
with the integrability required for subsequent comparison estimates. -/
theorem kernelTail_convolution (f q : ℝ → ℝ) (hf : Integrable f) (hq : Integrable q) (Q : ℝ) :
    Integrable (fun v => f v*kernelTail q (Q-v)) ∧
    kernelTail (fun u => ∫ v : ℝ, f v*q (u-v)) Q=
      ∫ v : ℝ, f v*kernelTail q (Q-v) := by
  have hj : Integrable (fun p : ℝ×ℝ => f p.2*q (p.1-p.2)) (volume.prod volume) :=
    hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hq
  have hr : Integrable (fun p : ℝ×ℝ => f p.2*q (p.1-p.2))
      ((volume.restrict (Ioi Q)).prod volume) := by
    rw [Measure.restrict_prod_eq_prod_univ]
    exact hj.integrableOn
  have he (v : ℝ) : (∫ u in Ioi Q, f v*q (u-v))=f v*kernelTail q (Q-v) := by
    rw [integral_const_mul,kernelTail_translate]
  constructor
  · have hh := hr.integral_prod_right
    simpa only [he] using hh
  · change (∫ u in Ioi Q, ∫ v : ℝ, f v*q (u-v))=_
    rw [integral_integral_swap hr]
    simp_rw [he]

/-- A convolution tail is controlled by the input tail and its value at
the boundary, if the positive kernel's tail is bounded by the kernel. -/
theorem convolution_tail_boundary_bound (f q : ℝ → ℝ) (hf : Integrable f) (hq : Integrable q)
    (hfp : ∀ v, 0 ≤ f v) (hqp : ∀ v, 0 ≤ q v) (C Q : ℝ) (hC : 0 ≤ C)
    (htail : ∀ t, 0 ≤ t → kernelTail q t ≤ C*q t)
    (hboundary : Integrable (fun v => f v*q (Q-v))) :
    kernelTail (fun u => ∫ v : ℝ, f v*q (u-v)) Q ≤
      (∫ t : ℝ, q t)*kernelTail f Q+C*(∫ v : ℝ, f v*q (Q-v)) := by
  obtain ⟨hi,he⟩ := kernelTail_convolution f q hf hq Q
  rw [he]
  have hind : Integrable ((Ioi Q).indicator f) := hf.indicator measurableSet_Ioi
  calc
    _ ≤ ∫ v : ℝ, (∫ t : ℝ, q t)*((Ioi Q).indicator f v)+C*(f v*q (Q-v)) := by
      apply integral_mono hi ((hind.const_mul _).add (hboundary.const_mul C))
      intro v
      change f v*kernelTail q (Q-v) ≤ (∫ t : ℝ, q t)*((Ioi Q).indicator f v)+C*(f v*q (Q-v))
      by_cases hv : Q < v
      · rw [indicator_of_mem (show v ∈ Ioi Q from hv)]
        have ht : kernelTail q (Q-v) ≤ ∫ t : ℝ, q t :=
          setIntegral_le_integral hq (Eventually.of_forall hqp)
        nlinarith [mul_le_mul_of_nonneg_left ht (hfp v),mul_nonneg hC (mul_nonneg (hfp v) (hqp (Q-v)))]
      · rw [indicator_of_notMem (show v ∉ Ioi Q from hv),mul_zero,zero_add]
        have ht := mul_le_mul_of_nonneg_left (htail (Q-v) (by linarith)) (hfp v)
        nlinarith only [ht]
    _ = _ := by
      rw [integral_add (hind.const_mul _) (hboundary.const_mul C),integral_const_mul,integral_const_mul,
        integral_indicator measurableSet_Ioi]
      rfl

end
end SixVertex
