import SixVertex.WeightedReferenceQuadrature

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- The explicit error constant in the reference weighted row bound. -/
def referenceKernelRowErrorConstant (lam : ℝ) : ℝ :=
  (kernelL1Mass (kernelKPrime lam)+kernelLogConstant lam*kernelL1Mass (kernelK lam))/2

theorem referenceKernelRowErrorConstant_nonneg (lam : ℝ) : 0 ≤ referenceKernelRowErrorConstant lam := by
  unfold referenceKernelRowErrorConstant
  exact div_nonneg (add_nonneg (kernelL1Mass_nonneg _) (mul_nonneg (kernelLogConstant_nonneg _) (kernelL1Mass_nonneg _))) (by norm_num)

/-- Absolute weighted row bound derived from the actual reference
quadrature and the positive inverse-density weights. -/
theorem reference_kernel_absolute_row_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) (u : ℝ) :
    (∑ j : Fin n, |kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))|) ≤
      kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M := by
  have he := weighted_reference_kernel_error lam h0 hhalf hpi Q L Y R M hM hlower
    (physicalKernelFunction lam h0 hpi) (physicalKernelPrimeFunction lam h0 hpi)
    (kernelK_integrable lam h0 hpi) (kernelKPrime_integrable lam h0 hpi)
    (fun v => hasDerivAt_kernelK lam v h0 hpi) u
  change |(∑ j : Fin n, kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))-
      (∫ v in Icc (-Q) Q, kernelK lam (u-v))| ≤
      (kernelL1Mass (kernelKPrime lam)+kernelLogConstant lam*kernelL1Mass (kernelK lam))/(2*M) at he
  have hC : (kernelL1Mass (kernelKPrime lam)+kernelLogConstant lam*kernelL1Mass (kernelK lam))/(2*M)=
      referenceKernelRowErrorConstant lam/M := by unfold referenceKernelRowErrorConstant; ring
  rw [hC] at he
  have ha (j : Fin n) : |kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))|=
      -(kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) :=
    abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (kernelK_nonpos lam _ hhalf hpi)
      (mul_pos (Nat.cast_pos.mpr R.chain_pos) (finiteIntervalDensity_pos lam h0 hhalf hpi Q (Y j))).le)
  have hsum : (∑ j : Fin n, |kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))|)=
      -(∑ j : Fin n, kernelK lam (u-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) := by
    simp_rw [ha,Finset.sum_neg_distrib]
  have hInt : -(∫ v in Icc (-Q) Q, kernelK lam (u-v)) ≤ kernelL1Mass (kernelK lam) := by
    calc
      _ = ∫ v in Icc (-Q) Q, |kernelK lam (u-v)| := by
        rw [← integral_neg]
        apply integral_congr_ae
        exact Eventually.of_forall (fun v => (abs_of_nonpos (kernelK_nonpos lam _ hhalf hpi)).symm)
      _ ≤ ∫ v : ℝ, |kernelK lam (u-v)| :=
        setIntegral_le_integral ((kernelK_integrable lam h0 hpi).abs.comp_sub_left u) (Eventually.of_forall (fun _ => abs_nonneg _))
      _ = _ := integral_sub_left_eq_self (fun x : ℝ => |kernelK lam x|) volume u
  rw [hsum]
  have hh := (abs_le.mp he).1
  linarith

def referenceKernelMatrix {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))

def referenceKernelOperator {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (referenceKernelMatrix lam h0 hpi Q L Y).toLin'.toContinuousLinearMap

theorem referenceKernelOperator_apply {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) (v : Fin n → ℝ) (i : Fin n) :
    referenceKernelOperator lam h0 hpi Q L Y v i=
      ∑ j : Fin n, (kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))*v j := rfl

theorem referenceKernelOperator_norm_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) :
    ‖referenceKernelOperator lam h0 hpi Q L Y‖ ≤
      kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M := by
  have hC : 0 ≤ kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M :=
    add_nonneg (kernelL1Mass_nonneg _) (div_nonneg (referenceKernelRowErrorConstant_nonneg _) hM.le)
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).mpr
  intro i
  rw [referenceKernelOperator_apply]
  calc
    _ ≤ ∑ j : Fin n, ‖(kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))*v j‖ := norm_sum_le _ _
    _ ≤ ∑ j : Fin n, |kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))| *‖v‖ := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
    _ = (∑ j : Fin n, |kernelK lam (Y i-Y j)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))|)*‖v‖ := by rw [Finset.sum_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (reference_kernel_absolute_row_bound lam h0 hhalf hpi Q L Y R M hM hlower (Y i)) (norm_nonneg _)

/-- One strict contraction constant works before all finite reference
configurations once their actual scaled density exceeds one threshold. -/
theorem exists_referenceKernelOperator_contraction (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ M₀ κ : ℝ, 0 < M₀ ∧ 0 ≤ κ ∧ κ < 1 ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ v ∈ Icc (-Q) Q, M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) →
        ‖referenceKernelOperator lam h0 hpi Q L Y‖ ≤ κ := by
  let h := kernelL1Mass (kernelK lam)
  let B := referenceKernelRowErrorConstant lam
  let M₀ : ℝ := 1+2*B/(1-h)
  let κ : ℝ := (1+h)/2
  have hh : h < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  have hh0 : 0 ≤ h := kernelL1Mass_nonneg _
  have hB : 0 ≤ B := referenceKernelRowErrorConstant_nonneg _
  have hd : 0 < 1-h := sub_pos.mpr hh
  have hM : 0 < M₀ := by dsimp [M₀]; positivity
  have hEq : (1-h)*M₀=(1-h)+2*B := by dsimp [M₀]; field_simp [hd.ne']
  have hsmall : B/M₀ ≤ (1-h)/2 := by
    apply (div_le_iff₀ hM).mpr
    nlinarith
  refine ⟨M₀,κ,hM,by dsimp [κ]; positivity,by dsimp [κ]; linarith,?_⟩
  intro n Q L Y R hlower
  have hnorm := referenceKernelOperator_norm_bound lam h0 hhalf hpi Q L Y R M₀ hM hlower
  change ‖referenceKernelOperator lam h0 hpi Q L Y‖ ≤ h+B/M₀ at hnorm
  dsimp [κ]
  linarith

end
end SixVertex
