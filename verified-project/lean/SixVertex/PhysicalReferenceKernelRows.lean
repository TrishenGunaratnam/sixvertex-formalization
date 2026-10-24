import SixVertex.PhysicalWeightedReferenceQuadrature
import SixVertex.ReferenceKernelRows

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Error constant for actual weighted rows in both physical regimes. -/
def physicalReferenceKernelRowErrorConstant (lam : ℝ) : ℝ :=
  (kernelL1Mass (kernelKPrime lam)+physicalDensityLogConstant lam*kernelL1Mass (kernelK lam))/2

theorem physicalReferenceKernelRowErrorConstant_nonneg (lam : ℝ) (h0 : 0 < lam) :
    0 ≤ physicalReferenceKernelRowErrorConstant lam := by
  unfold physicalReferenceKernelRowErrorConstant
  exact div_nonneg (add_nonneg (kernelL1Mass_nonneg _)
    (mul_nonneg (physicalDensityLogConstant_pos lam h0).le (kernelL1Mass_nonneg _))) (by norm_num)

/-- Actual absolute weighted-row estimate for either sign of K. -/
theorem reference_kernel_absolute_row_bound_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) (u : ℝ) :
    (∑ j : Fin n,|kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))|) ≤
      kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M := by
  have he := weighted_reference_kernel_error_all lam h0 hpi Q L Y R M hM hlower
    (physicalKernelFunction lam h0 hpi) (physicalKernelPrimeFunction lam h0 hpi)
    (kernelK_integrable lam h0 hpi) (kernelKPrime_integrable lam h0 hpi)
    (fun v => hasDerivAt_kernelK lam v h0 hpi) u
  change |(∑ j : Fin n,kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))-
      (∫ v in Icc (-Q) Q,kernelK lam (u-v))| ≤
      (kernelL1Mass (kernelKPrime lam)+physicalDensityLogConstant lam*kernelL1Mass (kernelK lam))/(2*M) at he
  have hC : (kernelL1Mass (kernelKPrime lam)+physicalDensityLogConstant lam*kernelL1Mass (kernelK lam))/(2*M)=
      physicalReferenceKernelRowErrorConstant lam/M := by unfold physicalReferenceKernelRowErrorConstant; ring
  rw [hC] at he
  let d : Fin n → ℝ := fun j => kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))
  have hp (j : Fin n) : 0 ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j) :=
    (mul_pos (Nat.cast_pos.mpr R.chain_pos) (finiteIntervalDensity_pos_all lam h0 hpi Q (Y j))).le
  have hs : (∑ j : Fin n,|d j|)=|∑ j : Fin n,d j| := by
    by_cases hh : Real.pi/2 ≤ lam
    · have hd (j : Fin n) : d j ≤ 0 := div_nonpos_of_nonpos_of_nonneg (kernelK_nonpos lam _ hh hpi) (hp j)
      rw [abs_of_nonpos (Finset.sum_nonpos (fun j _ => hd j))]
      simp_rw [abs_of_nonpos (hd _),Finset.sum_neg_distrib]
    · have hd (j : Fin n) : 0 ≤ d j := div_nonneg (kernelK_nonneg lam _ h0 (le_of_not_ge hh)) (hp j)
      rw [abs_of_nonneg (Finset.sum_nonneg (fun j _ => hd j))]
      simp_rw [abs_of_nonneg (hd _)]
  have hInt : |∫ v in Icc (-Q) Q,kernelK lam (u-v)| ≤ kernelL1Mass (kernelK lam) := by
    calc
      _ ≤ ∫ v in Icc (-Q) Q,|kernelK lam (u-v)| := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun v : ℝ => kernelK lam (u-v))
      _ ≤ ∫ v : ℝ,|kernelK lam (u-v)| :=
        setIntegral_le_integral ((kernelK_integrable lam h0 hpi).abs.comp_sub_left u)
          (Eventually.of_forall (fun _ => abs_nonneg _))
      _ = _ := integral_sub_left_eq_self (fun x : ℝ => |kernelK lam x|) volume u
  change (∑ j : Fin n,|d j|) ≤ _
  rw [hs]
  calc
    _ ≤ |(∑ j : Fin n,d j)-(∫ v in Icc (-Q) Q,kernelK lam (u-v))|+
      |∫ v in Icc (-Q) Q,kernelK lam (u-v)| := by
      simpa only [sub_add_cancel] using abs_add_le ((∑ j : Fin n,d j)-(∫ v in Icc (-Q) Q,kernelK lam (u-v)))
        (∫ v in Icc (-Q) Q,kernelK lam (u-v))
    _ ≤ _ := (add_le_add he hInt).trans_eq (by ring)

/-- Uniform norm bound for the actual finite weighted kernel matrix,
with its original operator definition preserved. -/
theorem referenceKernelOperator_norm_bound_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) :
    ‖referenceKernelOperator lam h0 hpi Q L Y‖ ≤
      kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M := by
  have hC : 0 ≤ kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M :=
    add_nonneg (kernelL1Mass_nonneg _) (div_nonneg (physicalReferenceKernelRowErrorConstant_nonneg lam h0) hM.le)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).mpr
  intro i
  rw [referenceKernelOperator_apply]
  calc
    _ ≤ ∑ j : Fin n,‖(kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))*v j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n,|kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))| *‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j : Fin n,|kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))|)*‖v‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (reference_kernel_absolute_row_bound_all lam h0 hpi Q L Y R M hM hlower (Y i)) (norm_nonneg _)

end
end SixVertex
