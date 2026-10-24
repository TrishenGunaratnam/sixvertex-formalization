import SixVertex.ExteriorConvolution

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set

/-- A bound only on the exterior input suffices for a positive exterior
kernel; the constant does not depend on the output point. -/
theorem exteriorConvolutionOperator_le_exterior_bound (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (hpos : ∀ x,0 ≤ k x) (Q : ℝ)
    (g : BoundedRealFunction) (M : ℝ) (hM : 0 ≤ M)
    (hg : ∀ v,v ∉ Icc (-Q) Q → g v ≤ M) (u : ℝ) :
    exteriorConvolutionOperator k hk Q g u ≤ (∫ t : ℝ,k t)*M := by
  have hi : Integrable (fun v : ℝ => k (u-v)*g v) :=
    (hk.comp_sub_left u).mul_bdd g.continuous.aestronglyMeasurable
      (Eventually.of_forall g.norm_coe_le_norm)
  have hc : Integrable (fun v : ℝ => k (u-v)*M) := (hk.comp_sub_left u).mul_const M
  rw [exteriorConvolutionOperator_apply]
  calc
    _ ≤ ∫ v in (Icc (-Q) Q)ᶜ,k (u-v)*M := by
      apply setIntegral_mono_on hi.integrableOn hc.integrableOn measurableSet_Icc.compl
      intro v hv
      exact mul_le_mul_of_nonneg_left (hg v hv) (hpos (u-v))
    _ ≤ ∫ v : ℝ,k (u-v)*M := setIntegral_le_integral hc
      (Eventually.of_forall (fun v => mul_nonneg (hpos (u-v)) hM))
    _ = _ := by rw [integral_mul_const,integral_sub_left_eq_self]

end
end SixVertex
