import SixVertex.KernelTailProfile
import SixVertex.CountingSawtooth
import SixVertex.BoundedConvolution

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem kernelTail_kernelS (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u : ℝ) :
    kernelTail (kernelS lam) u=phaseEnd (lam/2)-countingS lam u := by
  exact integral_Ioi_of_hasDerivAt_of_tendsto' (a := u)
    (fun v _ => hasDerivAt_countingS lam v h0 hpi) (kernelS_integrable lam h0 hpi).integrableOn
    (countingS_tendsto_atTop atTop (fun _ : ℝ => lam) id lam h0 hpi tendsto_const_nhds tendsto_id)

theorem kernelTail_negativeKernel (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u : ℝ) :
    kernelTail (fun v => -kernelK lam v) u=countingTheta lam u-phaseEnd lam := by
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := u)
    (fun v _ => hasDerivAt_countingTheta lam v h0 hpi) (kernelK_integrable lam h0 hpi).integrableOn
    (countingTheta_tendsto_atTop atTop (fun _ : ℝ => lam) id lam h0 hpi tendsto_const_nhds tendsto_id)
  change (∫ v in Ioi u, -kernelK lam v)=_
  rw [integral_neg,h]
  ring

theorem integral_negativeKernel (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    (∫ v : ℝ, -kernelK lam v)=2*lam/Real.pi-1 := by
  rw [integral_neg,integral_kernelK lam h0 hpi]
  ring

theorem integral_negativeKernel_eq_mass (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    (∫ v : ℝ, -kernelK lam v)=kernelL1Mass (kernelK lam) := by
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => (abs_of_nonpos (kernelK_nonpos lam v hhalf hpi)).symm)

theorem kernelTail_negativeKernel_zero (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    kernelTail (fun v => -kernelK lam v) 0=kernelL1Mass (kernelK lam)/2 := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  rw [kernelTail_negativeKernel lam h0 hpi]
  have hm := integral_negativeKernel_eq_mass lam hhalf hpi
  rw [integral_negativeKernel lam h0 hpi] at hm
  simp only [countingTheta,barePhase_zero,zero_sub]
  unfold phaseEnd
  rw [show 2*lam/Real.pi=2*(lam/Real.pi) by ring] at hm
  linarith

theorem kernelTail_negativeKernel_le_mass (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    kernelTail (fun v => -kernelK lam v) u ≤ kernelL1Mass (kernelK lam) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hh : (∫ v in Ioi u, -kernelK lam v) ≤ ∫ v : ℝ, -kernelK lam v := by
    apply setIntegral_le_integral
    · exact (kernelK_integrable lam h0 hpi).neg
    · exact Eventually.of_forall (fun v => neg_nonneg.mpr (kernelK_nonpos lam v hhalf hpi))
  exact hh.trans_eq (integral_negativeKernel_eq_mass lam hhalf hpi)

/-- Exact decomposition of the actual counting tail into the positive
source and interaction tails, including the half-filling constant. -/
theorem countingTail_decomposition {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    (∫ v in Ioi u, countingSlope lam b L Y v)=
      (∑ a ∈ Finset.range L, kernelTail (kernelS lam) (u-b a))+
        ∑ j : Fin n, kernelTail (fun v => -kernelK lam v) (u-Y j) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  rw [integral_Ioi_countingSlope_half lam b L hL hfill Y hhalf hpi u]
  simp_rw [kernelTail_kernelS lam h0 hpi,kernelTail_negativeKernel lam h0 hpi]
  simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_range,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  have he : (L : ℝ)*phaseEnd (lam/2)-(n : ℝ)*phaseEnd lam=(n : ℝ)/2 := by
    change countingEnd lam L n=(n : ℝ)/2
    rw [hfill,countingEnd_half]
  unfold countingXi
  linarith

/-- The tail at a labelled root is its right-edge half-index. -/
theorem countingTail_at_root {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0) (j : Fin n) :
    (∫ v in Ioi (Y j), countingSlope lam b L Y v)=(n : ℝ)-(j.val : ℝ)-1/2 := by
  rw [integral_Ioi_countingSlope_half lam b L hL hfill Y hhalf hpi (Y j)]
  have hj : countingXi lam b L Y (Y j)=countingTarget n 0 j := congrFun hroots.2 j
  rw [hj]
  unfold countingTarget
  ring

end
end SixVertex
