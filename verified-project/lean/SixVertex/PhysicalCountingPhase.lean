import SixVertex.PhysicalRegularRoots
import SixVertex.WeightedCountingPhase

namespace SixVertex
noncomputable section
open Set

/-- Relative phase variation uses the actual derivative K, including at
the free point, and does not assume an integrable scattering phase. -/
theorem countingTheta_relative_increment_bound_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (eps u v : ℝ) (hd : |v-u| ≤ eps) :
    |countingTheta lam v-countingTheta lam u| ≤
      Real.exp (kernelLogConstant lam*eps)*|kernelK lam u| *|v-u| := by
  have hbound (x : ℝ) (hx : x ∈ uIcc u v) :
      ‖kernelK lam x‖ ≤ Real.exp (kernelLogConstant lam*eps)*|kernelK lam u| := by
    have hs := (kernelK_abs_exponential_comparison_all lam h0 hpi u x).2
    have hd' := (abs_sub_left_of_mem_uIcc hx).trans hd
    rw [Real.norm_eq_abs]
    exact hs.trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd' (kernelLogConstant_nonneg lam))) (abs_nonneg _))
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ uIcc u v) => (hasDerivAt_countingTheta lam x h0 hpi).hasDerivWithinAt)
    hbound (convex_uIcc u v) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using hh

/-- Actual finite counting functions have a uniform displacement bound
from the density-scaled coordinate estimate and weighted kernel rows. -/
theorem reference_weighted_countingXi_displacement_bound_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y Z : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M radius : ℝ) (hM : 0 < M) (hrad : 0 ≤ radius)
    (hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (hdis : ∀ j, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)*|Z j-Y j| ≤ radius) (u : ℝ) :
    |countingXi lam (fun _ => 0) L Z u-countingXi lam (fun _ => 0) L Y u| ≤
      Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) := by
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
    have he := countingTheta_relative_increment_bound_all lam h0 hpi (radius/M) (u-Y j) (u-Z j) hde
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
      (reference_kernel_absolute_row_bound_all lam h0 hpi Q L Y R M hM hlower u) (mul_nonneg hA hrad)

/-- Actual weighted root closeness gives a whole-line counting-primitive
error, including the endpoint counting extensions, for both kernel signs. -/
theorem weighted_configuration_counting_primitive_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M radius : ℝ) (hM : 0 < M) (hrad : 0 ≤ radius)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) (u : ℝ) :
    |countingXi lam (fun _ => 0) L X u-
      ((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)| ≤
      Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+|1-2*lam/Real.pi|/2 := by
  have hdis (j : Fin n) : (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)*|X j-Y j| ≤ radius := by
    have hw : 0 < (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j) :=
      hM.trans_le (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩)
    exact (mul_comm _ _).trans_le ((le_div_iff₀ hw).mp (hclose j))
  have hv := reference_weighted_countingXi_displacement_bound_all lam h0 hpi Q L Y X R M radius hM hrad hlower hdis u
  have href := reference_counting_uniform_error_all lam h0 hpi Q L Y R u
  have hid : countingXi lam (fun _ => 0) L X u-((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)=
      (countingXi lam (fun _ => 0) L X u-countingXi lam (fun _ => 0) L Y u)+
      (countingXi lam (fun _ => 0) L Y u-((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hv href)

/-- Both finite continuum endpoints have bounded actual counting
extensions, with the same explicit uniform primitive bound. -/
theorem weighted_configuration_endpoint_counting_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M radius : ℝ) (hM : 0 < M) (hrad : 0 ≤ radius)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) :
    |countingXi lam (fun _ => 0) L X (-Q)+(n : ℝ)/2| ≤
      Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+|1-2*lam/Real.pi|/2 ∧
    |countingXi lam (fun _ => 0) L X Q-(n : ℝ)/2| ≤
      Real.exp (kernelLogConstant lam*(radius/M))*radius*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)+|1-2*lam/Real.pi|/2 := by
  have hl := weighted_configuration_counting_primitive_error_all lam h0 hpi Q L Y X R M radius hM hrad hlower hclose (-Q)
  have hr := weighted_configuration_counting_primitive_error_all lam h0 hpi Q L Y X R M radius hM hrad hlower hclose Q
  rw [finiteIntervalCumulative_left,mul_zero,zero_sub,sub_neg_eq_add] at hl
  rw [finiteIntervalCumulative_right lam h0 hpi Q R.interval_nonneg,R.mass] at hr
  have hid : (n : ℝ)-(n : ℝ)/2=(n : ℝ)/2 := by ring
  rw [hid] at hr
  exact ⟨hl,hr⟩

end
end SixVertex
