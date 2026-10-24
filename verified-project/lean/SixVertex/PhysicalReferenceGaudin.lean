import SixVertex.PhysicalReferenceKernelRows
import SixVertex.PhysicalReferenceResidual
import SixVertex.ReferenceGaudin

namespace SixVertex
noncomputable section
open MeasureTheory Set

def physicalReferenceGaudinErrorConstant (lam : ℝ) : ℝ :=
  physicalReferenceKernelRowErrorConstant lam+kernelL1Mass (kernelKPrime lam)/2

theorem physicalReferenceGaudinErrorConstant_nonneg (lam : ℝ) (h0 : 0 < lam) :
    0 ≤ physicalReferenceGaudinErrorConstant lam :=
  add_nonneg (physicalReferenceKernelRowErrorConstant_nonneg lam h0)
    (div_nonneg (kernelL1Mass_nonneg _) (by norm_num))

theorem referenceGaudinDiagonalError_norm_bound_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) :
    ‖referenceGaudinDiagonalError lam h0 hpi Q L Y‖ ≤ kernelL1Mass (kernelKPrime lam)/(2*M) := by
  apply finiteDiagonalOperator_norm_bound _ _ (div_nonneg (kernelL1Mass_nonneg _) (by positivity))
  intro j
  let w := (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
  have hw : M ≤ w := hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
  have hwp : 0 < w := hM.trans_le hw
  have hid : countingSlope lam (fun _ => 0) L Y (Y j)/w-1=
      (countingSlope lam (fun _ => 0) L Y (Y j)-w)/w := by field_simp
  change |countingSlope lam (fun _ => 0) L Y (Y j)/w-1| ≤ _
  rw [hid,abs_div,abs_of_pos hwp]
  calc
    _ ≤ (kernelL1Mass (kernelKPrime lam)/2)/M :=
      div_le_div₀ (div_nonneg (kernelL1Mass_nonneg _) (by norm_num)) (reference_density_uniform_error_all lam h0 hpi Q L Y R (Y j)) hM hw
    _ = _ := by ring

theorem referenceGaudinPerturbation_norm_bound_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) :
    ‖referenceGaudinPerturbation lam h0 hpi Q L Y‖ ≤
      kernelL1Mass (kernelK lam)+physicalReferenceGaudinErrorConstant lam/M := by
  apply (norm_add_le _ _).trans
  have h := add_le_add (referenceKernelOperator_norm_bound_all lam h0 hpi Q L Y R M hM hlower)
    (referenceGaudinDiagonalError_norm_bound_all lam h0 hpi Q L Y R M hM hlower)
  apply h.trans_eq
  unfold physicalReferenceGaudinErrorConstant
  ring

/-- A uniform two-sided inverse for the actual scaled reference Jacobian.
The density threshold and inverse bound are chosen before all finite data. -/
theorem exists_uniform_referenceGaudin_inverse_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ M₀ C : ℝ, 0 < M₀ ∧ 0 < C ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ v ∈ Icc (-Q) Q, M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) →
      referenceGaudinInverse lam h0 hpi Q L Y*referenceScaledGaudin lam h0 hpi Q L Y=1 ∧
      referenceScaledGaudin lam h0 hpi Q L Y*referenceGaudinInverse lam h0 hpi Q L Y=1 ∧
      ‖referenceGaudinInverse lam h0 hpi Q L Y‖ ≤ C := by
  let h := kernelL1Mass (kernelK lam)
  let B := physicalReferenceGaudinErrorConstant lam
  let M₀ : ℝ := 1+2*B/(1-h)
  let κ : ℝ := (1+h)/2
  have hh : h < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  have hh0 : 0 ≤ h := kernelL1Mass_nonneg _
  have hB : 0 ≤ B := physicalReferenceGaudinErrorConstant_nonneg _ h0
  have hd : 0 < 1-h := sub_pos.mpr hh
  have hM : 0 < M₀ := by dsimp [M₀]; positivity
  have hEq : (1-h)*M₀=(1-h)+2*B := by dsimp [M₀]; field_simp [hd.ne']
  have hsmall : B/M₀ ≤ (1-h)/2 := by
    apply (div_le_iff₀ hM).mpr
    nlinarith
  have hk : κ < 1 := by dsimp [κ]; linarith
  refine ⟨M₀,(1-κ)⁻¹,hM,inv_pos.mpr (sub_pos.mpr hk),?_⟩
  intro n Q L Y R hlower
  let A := referenceGaudinPerturbation lam h0 hpi Q L Y
  have hnorm : ‖A‖ ≤ κ := by
    have hn := referenceGaudinPerturbation_norm_bound_all lam h0 hpi Q L Y R M₀ hM hlower
    change ‖A‖ ≤ h+B/M₀ at hn
    dsimp [κ]
    linarith
  have hA : ‖A‖ < 1 := hnorm.trans_lt hk
  have hdec : referenceScaledGaudin lam h0 hpi Q L Y=1+A :=
    referenceScaledGaudin_decomposition lam h0 hpi Q L Y
  refine ⟨?_,?_,?_⟩
  · rw [hdec]
    exact finite_operator_neumann_left A hA
  · rw [hdec]
    exact finite_operator_neumann_right A hA
  · apply (finite_operator_neumann_norm_bound A hA).trans
    simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hk) (sub_le_sub_left hnorm 1)

end
end SixVertex
