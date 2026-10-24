import SixVertex.CountingPrimitive
import SixVertex.ResolventDerivative

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem integral_kernelK_counting_jump (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u y : ℝ) :
    (∫ v in Ici y, kernelK lam (u-v))=countingTheta lam (u-y)+phaseEnd lam := by
  have hd : ∀ v, HasDerivAt (fun v : ℝ => countingTheta lam (u-v)) (-kernelK lam (u-v)) v := fun v => by
    simpa only [Function.comp_def,zero_sub,mul_neg_one] using!
      (hasDerivAt_countingTheta lam (u-v) h0 hpi).comp v
        ((hasDerivAt_const v u).sub (hasDerivAt_id v))
  have hi : Integrable (fun v : ℝ => kernelK lam (u-v)) := (kernelK_integrable lam h0 hpi).comp_sub_left u
  have harg : Tendsto (fun v : ℝ => u-v) atTop atBot := by
    convert tendsto_neg_atTop_atBot.comp (real_shift_tendsto_atTop u) using 1
    funext v
    change u-v= -(v-u)
    ring
  have ht : Tendsto (fun v : ℝ => countingTheta lam (u-v)) atTop (𝓝 (-phaseEnd lam)) :=
    barePhase_tendsto_atBot atTop (fun _ : ℝ => lam) (fun v : ℝ => u-v) lam h0 hpi tendsto_const_nhds harg
  have hh := integral_Ioi_of_hasDerivAt_of_tendsto' (a := y) (fun v _ => hd v) hi.neg.integrableOn ht
  change (∫ v in Ioi y, -kernelK lam (u-v))= -phaseEnd lam-countingTheta lam (u-y) at hh
  rw [integral_neg] at hh
  rw [integral_Ici_eq_integral_Ioi]
  linarith

theorem kernelK_rootCount_primitive {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Y : Fin n → ℝ) (u : ℝ) :
    (∫ v : ℝ, kernelK lam (u-v)*(rootCountLe Y v : ℝ))=atomicPrimitiveFunction lam Y u := by
  rw [atomicPrimitiveFunction_apply]
  simp_rw [rootCountLe_eq_sum_indicators,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    simp_rw [← Set.indicator_mul_right (Ici (Y j)) (fun v : ℝ => kernelK lam (u-v)) (fun _ : ℝ => (1 : ℝ))]
    rw [integral_indicator measurableSet_Ici]
    simpa only [mul_one] using integral_kernelK_counting_jump lam h0 hpi u (Y j)
  · intro j _
    simp_rw [← Set.indicator_mul_right (Ici (Y j)) (fun v : ℝ => kernelK lam (u-v)) (fun _ : ℝ => (1 : ℝ))]
    exact (((kernelK_integrable lam h0 hpi).comp_sub_left u).mul_const 1).indicator measurableSet_Ici

theorem countingPrimitive_eq_source_sub_atomic {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    countingPrimitiveFunction lam b L hL hfill Y hhalf hpi=
      sourcePrimitiveFunction lam b L-atomicPrimitiveFunction lam Y := by
  ext u
  change countingXi lam b L Y u+(n : ℝ)/2=sourcePrimitiveFunction lam b L u-atomicPrimitiveFunction lam Y u
  rw [sourcePrimitiveFunction_apply,atomicPrimitiveFunction_apply]
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_range,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have he : (L : ℝ)*phaseEnd (lam/2)-(n : ℝ)*phaseEnd lam=(n : ℝ)/2 := by
    change countingEnd lam L n=(n : ℝ)/2
    rw [hfill,countingEnd_half]
  unfold countingXi
  linarith

def countingPrimitiveSourceError {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) : BoundedRealFunction :=
  atomicPrimitiveFunction lam Y-
    boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam (by linarith [Real.pi_pos]) hpi)
      (countingPrimitiveFunction lam b L hL hfill Y hhalf hpi)

theorem countingPrimitiveSourceError_identity {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    countingPrimitiveSourceError lam b L hL hfill Y hhalf hpi u=
      ∫ v : ℝ, kernelK lam (u-v)*countingDiscrepancy lam b L Y v := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let P := countingPrimitiveFunction lam b L hL hfill Y hhalf hpi
  have hc := bounded_measurable_convolution_integrable (kernelK lam) (fun v => (rootCountLe Y v : ℝ))
    (kernelK_integrable lam h0 hpi) (rootCountLe_measurable Y).aestronglyMeasurable (n : ℝ)
    (rootCountLe_norm_bound Y) u
  have hP := bounded_measurable_convolution_integrable (kernelK lam) (fun v => P v)
    (kernelK_integrable lam h0 hpi) P.continuous.aestronglyMeasurable ‖P‖ P.norm_coe_le_norm u
  change atomicPrimitiveFunction lam Y u-(∫ t : ℝ, kernelK lam t*P (u-t))=
    ∫ v : ℝ, kernelK lam (u-v)*((rootCountLe Y v : ℝ)-P v)
  simp_rw [mul_sub]
  rw [integral_sub hc hP,kernelK_rootCount_primitive lam h0 hpi Y u,scalar_convolution_comm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => mul_comm _ _)

theorem countingPrimitiveSourceError_norm_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0) :
    ‖countingPrimitiveSourceError lam b L hL hfill Y hhalf hpi‖ ≤ kernelL1Mass (kernelK lam)/2 := by
  apply (BoundedContinuousFunction.norm_le (by unfold kernelL1Mass; positivity)).mpr
  intro u
  rw [countingPrimitiveSourceError_identity lam b L hL hfill Y hhalf hpi u]
  exact countingDiscrepancy_kernel_bound lam b L hL hfill Y hhalf hpi hroots (kernelK lam)
    (kernelK_integrable lam (by linarith [Real.pi_pos]) hpi) u


theorem countingPrimitive_inverse_difference {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    countingPrimitiveFunction lam b L hL hfill Y hhalf hpi-
      dressedSourcePrimitiveFunction lam (by linarith [Real.pi_pos]) hpi b L=
      -boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam (by linarith [Real.pi_pos]) hpi)
        (countingPrimitiveSourceError lam b L hL hfill Y hhalf hpi) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let A := boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
  let B := boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
  let P := countingPrimitiveFunction lam b L hL hfill Y hhalf hpi
  have he : P+A P=sourcePrimitiveFunction lam b L-countingPrimitiveSourceError lam b L hL hfill Y hhalf hpi := by
    change P+A P=sourcePrimitiveFunction lam b L-(atomicPrimitiveFunction lam Y-A P)
    have hh := countingPrimitive_eq_source_sub_atomic lam b L hL hfill Y hhalf hpi
    change P=sourcePrimitiveFunction lam b L-atomicPrimitiveFunction lam Y at hh
    rw [hh]
    abel
  have hi := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T P)
    (boundedConvolutionInverse_left (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi))
  change B (P+A P)=P at hi
  rw [he,map_sub] at hi
  rw [dressedSourcePrimitiveFunction_eq_inverse]
  change P-B (sourcePrimitiveFunction lam b L)= -B (countingPrimitiveSourceError lam b L hL hfill Y hhalf hpi)
  rw [← hi]
  abel

theorem countingPrimitive_discrepancy_norm_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0) :
    ‖countingPrimitiveFunction lam b L hL hfill Y hhalf hpi-
      dressedSourcePrimitiveFunction lam (by linarith [Real.pi_pos]) hpi b L‖ ≤
      (1-kernelL1Mass (kernelK lam))⁻¹*(kernelL1Mass (kernelK lam)/2) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let B := boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
  rw [countingPrimitive_inverse_difference,norm_neg]
  apply (B.le_opNorm _).trans
  exact mul_le_mul (boundedConvolutionInverse_norm_bound (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi))
    (countingPrimitiveSourceError_norm_bound lam b L hL hfill Y hhalf hpi hroots) (norm_nonneg _)
    (inv_nonneg.mpr (sub_pos.mpr (kernelK_L1_mass_lt_one lam h0 hpi)).le)

/-- The actual integrated density discrepancy is uniformly bounded on
the entire real line, with a constant depending only on lambda. -/
theorem half_filled_integrated_density_uniform_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0) (u : ℝ) :
    |∫ v in Iic u, countingSlope lam b L Y v-
      dressedBareDensityFunction lam (by linarith [Real.pi_pos]) hpi b L v| ≤
      (1-kernelL1Mass (kernelK lam))⁻¹*(kernelL1Mass (kernelK lam)/2) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  rw [integral_sub (countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi).integrableOn
      (dressedBareDensityFunction_integrable lam h0 hpi b L).integrableOn,
    integral_Iic_countingSlope_half lam b L hL hfill Y hhalf hpi u,
    integral_Iic_dressedBareDensityFunction lam h0 hpi b L u]
  have hb := (countingPrimitiveFunction lam b L hL hfill Y hhalf hpi-
    dressedSourcePrimitiveFunction lam h0 hpi b L).norm_coe_le_norm u
  exact hb.trans (countingPrimitive_discrepancy_norm_bound lam b L hL hfill Y hhalf hpi hroots)

end
end SixVertex
