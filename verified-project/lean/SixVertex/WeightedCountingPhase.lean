import SixVertex.HomogeneousRootConstruction

namespace SixVertex
noncomputable section
open Set

/-- Relative phase variation uses the actual derivative K, including at
the free point, and does not assume an integrable scattering phase. -/
theorem countingTheta_relative_increment_bound (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (eps u v : ℝ) (hd : |v-u| ≤ eps) :
    |countingTheta lam v-countingTheta lam u| ≤
      Real.exp (kernelLogConstant lam*eps)*|kernelK lam u| *|v-u| := by
  have hbound (x : ℝ) (hx : x ∈ uIcc u v) :
      ‖kernelK lam x‖ ≤ Real.exp (kernelLogConstant lam*eps)*|kernelK lam u| := by
    have hh := (exponential_comparison_of_distance_le (fun x => -kernelK lam x) (kernelLogConstant lam) eps u x
      (kernelLogConstant_nonneg lam) (neg_nonneg.mpr (kernelK_nonpos lam _ hhalf hpi))
      ((abs_sub_left_of_mem_uIcc hx).trans hd) (negative_kernelK_exponential_comparison lam hhalf hpi u x)).2
    simpa only [Real.norm_eq_abs,abs_of_nonpos (kernelK_nonpos lam _ hhalf hpi)] using hh
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ uIcc u v) => (hasDerivAt_countingTheta lam x h0 hpi).hasDerivWithinAt)
    hbound (convex_uIcc u v) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hh

/-- Actual finite counting functions have a uniform displacement bound
from the density-scaled coordinate estimate and weighted kernel rows. -/
theorem reference_weighted_countingXi_displacement_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y Z : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M radius : ℝ) (hM : 0 < M) (hrad : 0 ≤ radius)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (hdis : ∀ j, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)*|Z j-Y j| ≤ radius) (u : ℝ) :
    |countingXi lam (fun _ => 0) L Z u-countingXi lam (fun _ => 0) L Y u| ≤
      Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M) := by
  let w : Fin n → ℝ := fun j => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
  let A := Real.exp (kernelLogConstant lam*(radius/M))
  have hA : 0 ≤ A := (Real.exp_pos _).le
  have hw (j : Fin n) : M ≤ w j := hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
  have hwp (j : Fin n) : 0 < w j := hM.trans_le (hw j)
  have hd (j : Fin n) : |Z j-Y j| ≤ radius/w j := by
    apply (le_div_iff₀ (hwp j)).mpr
    have hh := hdis j
    change w j*|Z j-Y j| ≤ radius at hh
    nlinarith only [hh]
  have hpoint (j : Fin n) : |countingTheta lam (u-Z j)-countingTheta lam (u-Y j)| ≤
      A*radius*|kernelK lam (u-Y j)/w j| := by
    have hdiff : (u-Z j)-(u-Y j)=-(Z j-Y j) := by ring
    have hde : |(u-Z j)-(u-Y j)| ≤ radius/M := by
      rw [hdiff,abs_neg]
      exact (hd j).trans (div_le_div₀ hrad le_rfl hM (hw j))
    have he := countingTheta_relative_increment_bound lam h0 hhalf hpi (radius/M) (u-Y j) (u-Z j) hde
    rw [hdiff,abs_neg] at he
    have hp := mul_le_mul_of_nonneg_left (hd j) (mul_nonneg hA (abs_nonneg (kernelK lam (u-Y j))))
    apply he.trans
    rw [abs_div,abs_of_pos (hwp j)]
    exact hp.trans_eq (by ring)
  have hid : countingXi lam (fun _ => 0) L Z u-countingXi lam (fun _ => 0) L Y u=
      -(∑ j : Fin n, (countingTheta lam (u-Z j)-countingTheta lam (u-Y j))) := by
    unfold countingXi
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid,abs_neg]
  calc
    _ ≤ ∑ j : Fin n, |countingTheta lam (u-Z j)-countingTheta lam (u-Y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, A*radius*|kernelK lam (u-Y j)/w j| := Finset.sum_le_sum (fun j _ => hpoint j)
    _ = (A*radius)*(∑ j : Fin n, |kernelK lam (u-Y j)/w j|) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (reference_kernel_absolute_row_bound lam h0 hhalf hpi Q L Y R M hM hlower u) (mul_nonneg hA hrad)

/-- The exact finite counting function has bounded whole-line discrepancy
from the actual finite-interval density primitive, uniformly before Q,L,n. -/
theorem uniform_corrected_counting_primitive_error (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ M C : ℝ, 0 < M ∧ 0 ≤ C ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y Z : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) →
      countingSystem lam (fun _ => 0) L Z=countingTarget n 0 → ∀ u : ℝ,
      |countingXi lam (fun _ => 0) L Z u-
        ((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)| ≤ C := by
  obtain ⟨M,radius,hM,hrad,hcorr⟩ := uniform_reference_weighted_root_displacement lam h0 hhalf hpi
  let A := Real.exp (kernelLogConstant lam*(radius/M))*radius*
    (kernelL1Mass (kernelK lam)+referenceKernelRowErrorConstant lam/M)
  let E := kernelL1Mass (kernelK lam)/2
  have hA : 0 ≤ A := mul_nonneg (mul_nonneg (Real.exp_pos _).le hrad.le)
    (add_nonneg (kernelL1Mass_nonneg _) (div_nonneg (referenceKernelRowErrorConstant_nonneg _) hM.le))
  have hE : 0 ≤ E := div_nonneg (kernelL1Mass_nonneg _) (by norm_num)
  refine ⟨M,A+E,hM,add_nonneg hA hE,?_⟩
  intro n Q L Y Z R hlower hZ u
  have hd := hcorr n Q L Y Z R hlower hZ
  have hv := reference_weighted_countingXi_displacement_bound lam h0 hhalf hpi Q L Y Z R M radius hM hrad.le hlower hd u
  have href : |countingXi lam (fun _ => 0) L Y u-
      ((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)| ≤ E := by
    dsimp [E]
    rw [kernelL1Mass,integral_abs_kernelK lam h0 hpi]
    exact reference_counting_uniform_error lam h0 hhalf hpi Q L Y R u
  have heq : countingXi lam (fun _ => 0) L Z u-((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)=
      (countingXi lam (fun _ => 0) L Z u-countingXi lam (fun _ => 0) L Y u)+
      (countingXi lam (fun _ => 0) L Y u-((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)) := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (add_le_add hv href)

end
end SixVertex
