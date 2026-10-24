import SixVertex.ReferenceKernelRows
import SixVertex.ReferenceResidual
import SixVertex.FiniteNeumann

namespace SixVertex
noncomputable section
open MeasureTheory Set

def finiteDiagonalOperator {n : ℕ} (d : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (Matrix.diagonal d).toLin'.toContinuousLinearMap

theorem finiteDiagonalOperator_apply {n : ℕ} (d v : Fin n → ℝ) (i : Fin n) :
    finiteDiagonalOperator d v i=d i*v i := by
  change (Matrix.diagonal d).mulVec v i=d i*v i
  rw [Matrix.mulVec_diagonal]

theorem finiteDiagonalOperator_norm_bound {n : ℕ} (d : Fin n → ℝ) (C : ℝ)
    (hC : 0 ≤ C) (hd : ∀ i, |d i| ≤ C) : ‖finiteDiagonalOperator d‖ ≤ C := by
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).mpr
  intro i
  rw [finiteDiagonalOperator_apply,norm_mul,Real.norm_eq_abs]
  exact mul_le_mul (hd i) (norm_le_pi_norm v i) (norm_nonneg _) hC

def referenceInverseDensityOperator {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  finiteDiagonalOperator (fun j => ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))⁻¹)

def referenceGaudinDiagonalError {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  finiteDiagonalOperator (fun j => countingSlope lam (fun _ => 0) L Y (Y j)/
    ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))-1)

theorem referenceGaudinDiagonalError_norm_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
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
      div_le_div₀ (div_nonneg (kernelL1Mass_nonneg _) (by norm_num)) (reference_density_uniform_error lam h0 hhalf hpi Q L Y R (Y j)) hM hw
    _ = _ := by ring

def referenceScaledGaudin {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  (gaudinCLM lam (fun _ => 0) L Y).comp (referenceInverseDensityOperator lam h0 hpi Q L Y)

theorem referenceScaledGaudin_decomposition {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) :
    referenceScaledGaudin lam h0 hpi Q L Y =
      1+(referenceKernelOperator lam h0 hpi Q L Y+referenceGaudinDiagonalError lam h0 hpi Q L Y) := by
  classical
  apply ContinuousLinearMap.ext
  intro v
  funext i
  change (gaudinMatrix lam (fun _ => 0) L Y).mulVec
    (referenceInverseDensityOperator lam h0 hpi Q L Y v) i = _
  simp only [Matrix.mulVec,dotProduct,gaudinMatrix,Matrix.of_apply,
    referenceInverseDensityOperator,finiteDiagonalOperator_apply,add_mul,Finset.sum_add_distrib]
  simp only [ite_mul,zero_mul,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.one_apply,
    Pi.add_apply,referenceKernelOperator_apply,referenceGaudinDiagonalError,finiteDiagonalOperator_apply]
  simp_rw [div_eq_mul_inv]
  ring

/-- Reference Gaudin perturbation, including the actual diagonal error. -/
def referenceGaudinPerturbation {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  referenceKernelOperator lam h0 hpi Q L Y+referenceGaudinDiagonalError lam h0 hpi Q L Y

def referenceGaudinErrorConstant (lam : ℝ) : ℝ :=
  referenceKernelRowErrorConstant lam+kernelL1Mass (kernelKPrime lam)/2

theorem referenceGaudinErrorConstant_nonneg (lam : ℝ) : 0 ≤ referenceGaudinErrorConstant lam :=
  add_nonneg (referenceKernelRowErrorConstant_nonneg _) (div_nonneg (kernelL1Mass_nonneg _) (by norm_num))

theorem referenceGaudinPerturbation_norm_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) :
    ‖referenceGaudinPerturbation lam h0 hpi Q L Y‖ ≤
      kernelL1Mass (kernelK lam)+referenceGaudinErrorConstant lam/M := by
  apply (norm_add_le _ _).trans
  have h := add_le_add (referenceKernelOperator_norm_bound lam h0 hhalf hpi Q L Y R M hM hlower)
    (referenceGaudinDiagonalError_norm_bound lam h0 hhalf hpi Q L Y R M hM hlower)
  apply h.trans_eq
  unfold referenceGaudinErrorConstant
  ring

def referenceGaudinInverse {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) :=
  ∑' m : ℕ, (-(referenceGaudinPerturbation lam h0 hpi Q L Y))^m

/-- A uniform two-sided inverse for the actual scaled reference Jacobian.
The density threshold and inverse bound are chosen before all finite data. -/
theorem exists_uniform_referenceGaudin_inverse (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ M₀ C : ℝ, 0 < M₀ ∧ 0 < C ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ v ∈ Icc (-Q) Q, M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) →
      referenceGaudinInverse lam h0 hpi Q L Y*referenceScaledGaudin lam h0 hpi Q L Y=1 ∧
      referenceScaledGaudin lam h0 hpi Q L Y*referenceGaudinInverse lam h0 hpi Q L Y=1 ∧
      ‖referenceGaudinInverse lam h0 hpi Q L Y‖ ≤ C := by
  let h := kernelL1Mass (kernelK lam)
  let B := referenceGaudinErrorConstant lam
  let M₀ : ℝ := 1+2*B/(1-h)
  let κ : ℝ := (1+h)/2
  have hh : h < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  have hh0 : 0 ≤ h := kernelL1Mass_nonneg _
  have hB : 0 ≤ B := referenceGaudinErrorConstant_nonneg _
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
    have hn := referenceGaudinPerturbation_norm_bound lam h0 hhalf hpi Q L Y R M₀ hM hlower
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
