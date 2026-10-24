import SixVertex.PhysicalConfigurationVariation
import SixVertex.ReferenceShiftDrift

namespace SixVertex
noncomputable section
open Set

/-- Weighted diagonal variation of the actual Gaudin matrix near actual
reference quantiles, uniformly in root number and cutoff. -/
theorem weighted_configuration_gaudin_diagonal_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (radius : ℝ) (hrad : 0 ≤ radius)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) (i : Fin n) :
    |countingSlope lam (fun _ => 0) L X (X i)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i))-
      countingSlope lam (fun _ => 0) L Y (Y i)/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i))| ≤
    (kernelL1Mass (kernelKPrime lam)+
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M))/M+
      physicalDensityLogConstant lam*Real.exp (physicalDensityLogConstant lam*(radius/M))*(radius/M) := by
  let f := finiteIntervalDensity lam h0 hpi Q
  let w := (L : ℝ)*f (Y i)
  let D := kernelL1Mass (kernelKPrime lam)/2
  let V := (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)
  let A := physicalDensityLogConstant lam*Real.exp (physicalDensityLogConstant lam*(radius/M))*(radius/M)
  have hw : M ≤ w := hlower (Y i) ⟨(R.location i).1.le,(R.location i).2.le⟩
  have hwp : 0 < w := hM.trans_le hw
  have hD : 0 ≤ D := div_nonneg (kernelL1Mass_nonneg _) (by norm_num)
  have hV : 0 ≤ V := by
    dsimp [V]
    exact mul_nonneg (mul_nonneg (mul_nonneg (kernelLogConstant_nonneg _) (Real.exp_pos _).le) hrad)
      (add_nonneg (kernelL1Mass_nonneg _) (div_nonneg (physicalReferenceKernelRowErrorConstant_nonneg lam h0) hM.le))
  have hdist : |X i-Y i| ≤ radius/M := (hclose i).trans (div_le_div₀ hrad le_rfl hM hw)
  have hp := finiteIntervalDensity_relative_translation_error_all lam h0 hpi Q (Y i) (X i) (radius/M) hdist
  have hprofile : |(L : ℝ)*f (X i)-(L : ℝ)*f (Y i)| ≤ A*w := by
    rw [← mul_sub,abs_mul,abs_of_nonneg (Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    have hp' := hp.trans (mul_le_mul_of_nonneg_left hdist (by
      exact mul_nonneg (mul_nonneg (physicalDensityLogConstant_pos lam h0).le (Real.exp_pos _).le)
        (finiteIntervalDensity_pos_all lam h0 hpi Q (Y i)).le))
    exact (mul_le_mul_of_nonneg_left hp' (Nat.cast_nonneg L : (0 : ℝ) ≤ L)).trans_eq (by dsimp [A,w,f]; ring)
  have hx : |countingSlope lam (fun _ => 0) L X (X i)-(L : ℝ)*f (X i)| ≤ D+V :=
    weighted_configuration_density_error_all lam h0 hpi Q L Y X R M hM hlower radius hrad hclose (X i)
  have hy : |(L : ℝ)*f (Y i)-countingSlope lam (fun _ => 0) L Y (Y i)| ≤ D := by
    rw [abs_sub_comm]
    exact reference_density_uniform_error_all lam h0 hpi Q L Y R (Y i)
  have ht : |countingSlope lam (fun _ => 0) L X (X i)-countingSlope lam (fun _ => 0) L Y (Y i)| ≤
      (2*D+V)+A*w := by
    have ht₁ := abs_add_le
      (countingSlope lam (fun _ => 0) L X (X i)-(L : ℝ)*f (X i))
      ((L : ℝ)*f (X i)-(L : ℝ)*f (Y i))
    rw [sub_add_sub_cancel] at ht₁
    have ht₂ := abs_add_le
      (countingSlope lam (fun _ => 0) L X (X i)-(L : ℝ)*f (Y i))
      ((L : ℝ)*f (Y i)-countingSlope lam (fun _ => 0) L Y (Y i))
    rw [sub_add_sub_cancel] at ht₂
    exact (ht₂.trans (add_le_add (ht₁.trans (add_le_add hx hprofile)) hy)).trans_eq (by ring)
  change |countingSlope lam (fun _ => 0) L X (X i)/w-countingSlope lam (fun _ => 0) L Y (Y i)/w| ≤ _
  rw [← sub_div,abs_div,abs_of_pos hwp]
  calc
    _ ≤ ((2*D+V)+A*w)/w := div_le_div_of_nonneg_right ht hwp.le
    _ = (2*D+V)/w+A := by field_simp
    _ ≤ (2*D+V)/M+A := add_le_add (div_le_div₀ (by positivity) le_rfl hM hw) le_rfl
    _ = _ := by dsimp [D,V,A]; ring

/-- Actual weighted interaction-row variation for both signs of the
physical kernel. No finite equations or ordering of X are assumed. -/
theorem weighted_configuration_kernel_row_difference_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (radius : ℝ) (hrad : 0 ≤ radius)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) (i : Fin n) :
    (∑ j : Fin n, |(kernelK lam (X i-X j)-kernelK lam (Y i-Y j))/
      ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))|) ≤
    (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(2*(radius/M)))*(2*(radius/M)))*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) := by
  let w : Fin n → ℝ := fun j => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
  let A := kernelLogConstant lam*Real.exp (kernelLogConstant lam*(2*(radius/M)))*(2*(radius/M))
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg (mul_nonneg (kernelLogConstant_nonneg _) (Real.exp_pos _).le)
      (mul_nonneg (by norm_num) (div_nonneg hrad hM.le))
  have hw (j : Fin n) : M ≤ w j := hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
  have hwp (j : Fin n) : 0 < w j := hM.trans_le (hw j)
  have hphysical (j : Fin n) : |X j-Y j| ≤ radius/M :=
    (hclose j).trans (div_le_div₀ hrad le_rfl hM (hw j))
  have hp (j : Fin n) : |(kernelK lam (X i-X j)-kernelK lam (Y i-Y j))/w j| ≤
      A*|kernelK lam (Y i-Y j)/w j| := by
    have hk := kernelK_relative_translation_error lam h0 hpi (Y i-Y j) (X i-X j) (2*(radius/M))
      (configuration_difference_distance Y X (radius/M) hphysical i j)
    have ht := hk.trans (mul_le_mul_of_nonneg_left
      (configuration_difference_distance Y X (radius/M) hphysical i j)
      (mul_nonneg (mul_nonneg (kernelLogConstant_nonneg _) (Real.exp_pos _).le) (abs_nonneg _)))
    rw [abs_div,abs_of_pos (hwp j),abs_div,abs_of_pos (hwp j)]
    apply (div_le_div_of_nonneg_right ht (hwp j).le).trans_eq
    dsimp [A]
    ring
  calc
    _ ≤ ∑ j : Fin n,A*|kernelK lam (Y i-Y j)/w j| := Finset.sum_le_sum (fun j _ => hp j)
    _ = A*(∑ j : Fin n,|kernelK lam (Y i-Y j)/w j|) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reference_kernel_absolute_row_bound_all lam h0 hpi Q L Y R M hM hlower (Y i)) hA

/-- Explicit Jacobian perturbation bound; all constants are independent
of the number of roots, chain length and continuum cutoff. -/
def physicalJacobianVariationBound (lam radius M : ℝ) : ℝ :=
  (kernelL1Mass (kernelKPrime lam)+
    (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M))/M+
    physicalDensityLogConstant lam*Real.exp (physicalDensityLogConstant lam*(radius/M))*(radius/M)+
    (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(2*(radius/M)))*(2*(radius/M)))*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)

/-- The actual scaled nonlinear Jacobian is uniformly close to the
actual reference Gaudin operator throughout a weighted neighborhood. -/
theorem weighted_configuration_gaudin_norm_difference_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (radius : ℝ) (hrad : 0 ≤ radius)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) :
    ‖(gaudinCLM lam (fun _ => 0) L X).comp (referenceInverseDensityOperator lam h0 hpi Q L Y)-
      referenceScaledGaudin lam h0 hpi Q L Y‖ ≤ physicalJacobianVariationBound lam radius M := by
  let w : Fin n → ℝ := fun j => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
  let A := (kernelL1Mass (kernelKPrime lam)+
    (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M))/M+
    physicalDensityLogConstant lam*Real.exp (physicalDensityLogConstant lam*(radius/M))*(radius/M)
  let B := (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(2*(radius/M)))*(2*(radius/M)))*
      (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)
  have hk : 0 ≤ kernelLogConstant lam := kernelLogConstant_nonneg lam
  have hf : 0 ≤ physicalDensityLogConstant lam := (physicalDensityLogConstant_pos lam h0).le
  have hb : 0 ≤ physicalReferenceKernelRowErrorConstant lam := physicalReferenceKernelRowErrorConstant_nonneg lam h0
  have hm : 0 ≤ kernelL1Mass (kernelK lam) := kernelL1Mass_nonneg _
  have hd : 0 ≤ kernelL1Mass (kernelKPrime lam) := kernelL1Mass_nonneg _
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  change ‖_‖ ≤ A+B
  apply ContinuousLinearMap.opNorm_le_bound _ (add_nonneg hA hB)
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (add_nonneg hA hB) (norm_nonneg v))).mpr
  intro i
  have heq :
      ((gaudinCLM lam (fun _ => 0) L X).comp (referenceInverseDensityOperator lam h0 hpi Q L Y)-
        referenceScaledGaudin lam h0 hpi Q L Y) v i =
      (countingSlope lam (fun _ => 0) L X (X i)/w i-
        countingSlope lam (fun _ => 0) L Y (Y i)/w i)*v i+
        ∑ j : Fin n,((kernelK lam (X i-X j)-kernelK lam (Y i-Y j))/w j)*v j := by
    simp only [ContinuousLinearMap.sub_apply,Pi.sub_apply,ContinuousLinearMap.comp_apply,
      referenceScaledGaudin,gaudinCLM_coordinate,referenceInverseDensityOperator,finiteDiagonalOperator_apply]
    simp only [div_eq_mul_inv,sub_mul,Finset.sum_sub_distrib,mul_assoc,w]
    ring
  rw [heq]
  have hdiag : ‖(countingSlope lam (fun _ => 0) L X (X i)/w i-
        countingSlope lam (fun _ => 0) L Y (Y i)/w i)*v i‖ ≤ A*‖v‖ := by
    rw [norm_mul,Real.norm_eq_abs]
    exact mul_le_mul (weighted_configuration_gaudin_diagonal_error_all lam h0 hpi Q L Y X R M hM hlower radius hrad hclose i)
      (norm_le_pi_norm v i) (norm_nonneg _) hA
  have hrow : ‖∑ j : Fin n,((kernelK lam (X i-X j)-kernelK lam (Y i-Y j))/w j)*v j‖ ≤ B*‖v‖ := by
    calc
      _ ≤ ∑ j : Fin n,‖((kernelK lam (X i-X j)-kernelK lam (Y i-Y j))/w j)*v j‖ := norm_sum_le _ _
      _ ≤ ∑ j : Fin n,|(kernelK lam (X i-X j)-kernelK lam (Y i-Y j))/w j| *‖v‖ := by
        apply Finset.sum_le_sum
        intro j _
        rw [norm_mul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
      _ = (∑ j : Fin n,|(kernelK lam (X i-X j)-kernelK lam (Y i-Y j))/w j|)*‖v‖ := by rw [Finset.sum_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (weighted_configuration_kernel_row_difference_all lam h0 hpi Q L Y X R M hM hlower radius hrad hclose i) (norm_nonneg v)
  exact ((norm_add_le _ _).trans (add_le_add hdiag hrow)).trans_eq (by ring)


/-- The actual uniform Jacobian error tends to zero in the dense-scale
parameter, for each fixed physical parameter and weighted radius. -/
theorem physicalJacobianVariationBound_tendsto_zero (lam radius : ℝ) :
    Filter.Tendsto (physicalJacobianVariationBound lam radius) Filter.atTop (nhds 0) := by
  have hδ : Filter.Tendsto (fun M : ℝ => radius/M) Filter.atTop (nhds 0) :=
    Filter.Tendsto.const_div_atTop Filter.tendsto_id radius
  have hb : Filter.Tendsto (fun M : ℝ => physicalReferenceKernelRowErrorConstant lam/M)
      Filter.atTop (nhds 0) := Filter.Tendsto.const_div_atTop Filter.tendsto_id _
  have he : Filter.Tendsto (fun M : ℝ => Real.exp (kernelLogConstant lam*(radius/M)))
      Filter.atTop (nhds 1) := by
    simpa only [mul_zero,Real.exp_zero,Function.comp_def] using (Real.continuous_exp.tendsto _).comp (hδ.const_mul (kernelLogConstant lam))
  have he₂ : Filter.Tendsto (fun M : ℝ => Real.exp (kernelLogConstant lam*(2*(radius/M))))
      Filter.atTop (nhds 1) := by
    simpa only [mul_zero,Real.exp_zero,Function.comp_def] using (Real.continuous_exp.tendsto _).comp ((hδ.const_mul 2).const_mul (kernelLogConstant lam))
  have hef : Filter.Tendsto (fun M : ℝ => Real.exp (physicalDensityLogConstant lam*(radius/M)))
      Filter.atTop (nhds 1) := by
    simpa only [mul_zero,Real.exp_zero,Function.comp_def] using (Real.continuous_exp.tendsto _).comp (hδ.const_mul (physicalDensityLogConstant lam))
  have hv := ((he.const_mul (kernelLogConstant lam)).mul_const radius).mul
    (hb.const_add (kernelL1Mass (kernelK lam)))
  have ht := (hv.const_add (kernelL1Mass (kernelKPrime lam))).div_atTop Filter.tendsto_id
  have hf := (hef.const_mul (physicalDensityLogConstant lam)).mul hδ
  have hr := ((he₂.const_mul (kernelLogConstant lam)).mul (hδ.const_mul 2)).mul
    (hb.const_add (kernelL1Mass (kernelK lam)))
  convert (ht.add hf).add hr using 1 <;> try simp
  funext M
  rfl

/-- A threshold chosen before all finite data makes the actual Jacobian
perturbation as small as any prescribed positive tolerance. -/
theorem exists_physicalJacobianVariation_threshold (lam radius eps : ℝ) (heps : 0 < eps) :
    ∃ M₀ : ℝ, 0 < M₀ ∧ ∀ M : ℝ,M₀ ≤ M → physicalJacobianVariationBound lam radius M < eps := by
  have he := (physicalJacobianVariationBound_tendsto_zero lam radius).eventually
    (gt_mem_nhds heps)
  obtain ⟨m,hm⟩ := Filter.eventually_atTop.1 he
  refine ⟨max m 1,lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _),?_⟩
  intro M hM
  exact hm M ((le_max_left _ _).trans hM)

end
end SixVertex
