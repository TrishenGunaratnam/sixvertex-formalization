import SixVertex.ConvolutionTails
import SixVertex.FullLineBoundaryDensity
import SixVertex.KernelValueTail

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter Topology

/-- The true right tail of the inverse-defined density is uniformly
comparable to its boundary value, without a closed-form evaluation. -/
theorem exists_fullLineDensity_tail_comparison (lam : ℝ) (hhalf : Real.pi/2 < lam)
    (hpi : lam < Real.pi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Q : ℝ, 0 ≤ Q →
      c*fullLineDensityFunction lam (by linarith [Real.pi_pos]) hpi Q ≤
        kernelTail (fun u => fullLineDensityFunction lam (by linarith [Real.pi_pos]) hpi u) Q ∧
      kernelTail (fun u => fullLineDensityFunction lam (by linarith [Real.pi_pos]) hpi u) Q ≤
        C*fullLineDensityFunction lam (by linarith [Real.pi_pos]) hpi Q := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have tail_bound {q : ℝ → ℝ} {c C : ℝ} (hd : PositiveKernelTailData q c C) (t : ℝ) (ht : 0 ≤ t) :
      kernelTail q t ≤ (C/(2*c))*q t := by
    have hp : 0 < 2*c/C := div_pos (mul_pos (by norm_num) hd.lower_pos) hd.upper_pos
    calc
      _ ≤ q t/(2*c/C) := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using hd.tail_le_value t ht)
      _ = _ := by field_simp [hd.lower_pos.ne',hd.upper_pos.ne'] <;> ring
  let r := fullLineDensityFunction lam h0 hpi
  let k : ℝ → ℝ := fun u => -kernelK lam u
  let s := kernelS lam
  let h : ℝ := kernelL1Mass (kernelK lam)
  have hs := kernelS_positive_tail_data lam h0 hpi
  have hk := negative_kernel_positive_tail_data lam hhalf hpi
  let Cs : ℝ := (2/(Real.pi*(Real.sin (lam/2))^2))/(2*(Real.sin lam/(2*Real.pi)))
  let Ck : ℝ := (2/(Real.pi*(Real.sin lam)^2))/(2*(|Real.sin (2*lam)|/(2*Real.pi)))
  let D : ℝ := max Cs Ck
  have hCs : 0 < Cs := div_pos hs.upper_pos (mul_pos (by norm_num) hs.lower_pos)
  have hCk : 0 < Ck := div_pos hk.upper_pos (mul_pos (by norm_num) hk.lower_pos)
  have hD : 0 < D := hCs.trans_le (le_max_left _ _)
  have hh : h < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  have hr := fullLineDensityFunction_integrable lam h0 hpi
  have hrp (u : ℝ) : 0 ≤ r u := (fullLineDensityFunction_pos lam h0 hhalf.le hpi u).le
  have hconv : Integrable (fun u => ∫ v : ℝ, r v*k (u-v)) :=
    hr.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hk.integrable
  have hbound (Q : ℝ) : Integrable (fun v : ℝ => r v*k (Q-v)) :=
    boundedConvolution_integrand_integrable (fun v => r v) hr (-(physicalKernelFunction lam h0 hpi)) Q
  refine ⟨Real.exp (-kernelLogConstant lam),D/(1-h),Real.exp_pos _,div_pos hD (by linarith),?_⟩
  intro Q hQ
  refine ⟨fullLineDensityFunction_tail_lower lam h0 hhalf.le hpi Q,?_⟩
  have hrenew (u : ℝ) : r u=s u+∫ v : ℝ, r v*k (u-v) := fullLineDensityFunction_renewal lam h0 hpi u
  have ht : kernelTail (fun u => r u) Q=kernelTail s Q+kernelTail (fun u => ∫ v : ℝ, r v*k (u-v)) Q := by
    change (∫ u in Ioi Q, r u)=_
    calc
      _ = ∫ u in Ioi Q, s u+(∫ v : ℝ, r v*k (u-v)) := integral_congr_ae (Eventually.of_forall hrenew)
      _ = _ := integral_add hs.integrable.integrableOn hconv.integrableOn
  have hct := convolution_tail_boundary_bound (fun u => r u) k hr hk.integrable hrp hk.nonnegative Ck Q hCk.le
    (fun t ht => tail_bound hk t ht) (hbound Q)
  have hmass : (∫ t : ℝ, k t)=h := integral_negativeKernel_eq_mass lam hhalf.le hpi
  rw [hmass] at hct
  have hst : kernelTail s Q ≤ Cs*s Q := tail_bound hs Q hQ
  have hsp : 0 ≤ s Q := hs.nonnegative Q
  have hcp : 0 ≤ ∫ v : ℝ, r v*k (Q-v) := integral_nonneg (fun v => mul_nonneg (hrp v) (hk.nonnegative (Q-v)))
  have hsD := mul_le_mul_of_nonneg_right (le_max_left Cs Ck) hsp
  have hkD := mul_le_mul_of_nonneg_right (le_max_right Cs Ck) hcp
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by linarith : 0 < 1-h)).mpr
  have hre := hrenew Q
  change kernelTail (fun u => r u) Q*(1-h) ≤ D*r Q
  change kernelTail (fun u => ∫ v : ℝ, r v*k (u-v)) Q ≤ h*kernelTail (fun u => r u) Q+Ck*(∫ v : ℝ, r v*k (Q-v)) at hct
  have hDr : D*r Q=D*s Q+D*(∫ v : ℝ, r v*k (Q-v)) := by rw [hre,mul_add]
  nlinarith only [ht,hct,hst,hsD,hkD,hDr]

end
end SixVertex
