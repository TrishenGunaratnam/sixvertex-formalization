import SixVertex.RelativeKernelVariation
import SixVertex.PhysicalReferenceKernelRows
import SixVertex.PhysicalReferenceResidual

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter

/-- Absolute physical-kernel spatial comparison covering both signs and
the identically zero free-point kernel. -/
theorem kernelK_abs_exponential_comparison_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (u v : ℝ) :
    Real.exp (-(kernelLogConstant lam*|v-u|))*|kernelK lam u| ≤ |kernelK lam v| ∧
      |kernelK lam v| ≤ Real.exp (kernelLogConstant lam*|v-u|)*|kernelK lam u| := by
  by_cases hh : Real.pi/2 ≤ lam
  · simpa only [abs_of_nonpos (kernelK_nonpos lam u hh hpi),abs_of_nonpos (kernelK_nonpos lam v hh hpi)] using
      negative_kernelK_exponential_comparison lam hh hpi u v
  · have hp (x : ℝ) : 0 < kernelK lam x := by
      unfold kernelK phaseDensity
      exact div_pos (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith))
        (mul_pos Real.pi_pos (phase_denominator_pos lam x (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'))
    have he := positive_function_exponential_comparison (kernelK lam) (kernelKPrime lam) (kernelLogConstant lam)
      hp (fun x => hasDerivAt_kernelK lam x h0 hpi) (fun x => by
        have hb := kernelKPrime_relative_bound lam x h0 hpi
        rw [abs_of_pos (hp x)] at hb
        apply hb.trans
        apply mul_le_mul_of_nonneg_right _ (hp x).le
        unfold kernelLogConstant
        have hs : 0 ≤ 2/(Real.sin (lam/2))^2 := by positivity
        linarith) u v
    simpa only [abs_of_pos (hp u),abs_of_pos (hp v)] using he

/-- A genuine mean-value estimate for translating the physical kernel,
relative to its original absolute value and with the actual displacement
retained. This is used for weighted configuration perturbations. -/
theorem kernelK_relative_translation_error (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (a b eps : ℝ) (hdist : |b-a| ≤ eps) :
    |kernelK lam b-kernelK lam a| ≤
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*eps)*|kernelK lam a|)*|b-a| := by
  let C := kernelLogConstant lam
  let B := C*Real.exp (C*eps)*|kernelK lam a|
  have hC : 0 ≤ C := kernelLogConstant_nonneg lam
  have hCb : 2/(Real.sin lam)^2 ≤ C := by
    dsimp [C,kernelLogConstant]
    have hs : 0 ≤ 2/(Real.sin (lam/2))^2 := by positivity
    linarith
  have hb (x : ℝ) (hx : x ∈ uIcc a b) : ‖kernelKPrime lam x‖ ≤ B := by
    have hd : |x-a| ≤ eps := (abs_sub_left_of_mem_uIcc hx).trans hdist
    have hs := (kernelK_abs_exponential_comparison_all lam h0 hpi a x).2
    have hu : |kernelK lam x| ≤ Real.exp (C*eps)*|kernelK lam a| :=
      hs.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hC)) (abs_nonneg _))
    have hr : |kernelKPrime lam x| ≤ C*|kernelK lam x| :=
      (kernelKPrime_relative_bound lam x h0 hpi).trans (mul_le_mul_of_nonneg_right hCb (abs_nonneg _))
    rw [Real.norm_eq_abs]
    exact hr.trans ((mul_le_mul_of_nonneg_left hu hC).trans_eq (by dsimp [B]; ring))
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ uIcc a b) => (hasDerivAt_kernelK lam x h0 hpi).hasDerivWithinAt)
    hb (convex_uIcc a b : Convex ℝ (uIcc a b)) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using he

/-- Weighted closeness to actual reference quantiles controls the actual
counting-density perturbation uniformly on the whole line. The source
terms cancel before the estimate, preserving the dense-edge scale. -/
theorem weighted_configuration_countingSlope_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (radius : ℝ) (hrad : 0 ≤ radius)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) (u : ℝ) :
    |countingSlope lam (fun _ => 0) L X u-countingSlope lam (fun _ => 0) L Y u| ≤
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) := by
  let w : Fin n → ℝ := fun j => (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
  let C := kernelLogConstant lam
  let E := Real.exp (C*(radius/M))
  have hC : 0 ≤ C := kernelLogConstant_nonneg lam
  have hw (j : Fin n) : M ≤ w j := hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩
  have hwp (j : Fin n) : 0 < w j := hM.trans_le (hw j)
  have hphysical (j : Fin n) : |X j-Y j| ≤ radius/M :=
    (hclose j).trans (div_le_div₀ hrad le_rfl hM (hw j))
  have hpoint (j : Fin n) : |kernelK lam (u-X j)-kernelK lam (u-Y j)| ≤
      (C*E*radius)*|kernelK lam (u-Y j)/w j| := by
    have hd : (u-X j)-(u-Y j)=Y j-X j := by ring
    have hk := kernelK_relative_translation_error lam h0 hpi (u-Y j) (u-X j) (radius/M)
      (by rw [hd,abs_sub_comm]; exact hphysical j)
    rw [hd,abs_sub_comm (Y j) (X j)] at hk
    have hm := mul_le_mul_of_nonneg_left (hclose j)
      (show 0 ≤ C*E*|kernelK lam (u-Y j)| by dsimp [E]; positivity)
    apply (hk.trans hm).trans_eq
    rw [abs_div,abs_of_pos (hwp j)]
    ring
  have hsum : |(∑ j : Fin n,kernelK lam (u-X j))-(∑ j : Fin n,kernelK lam (u-Y j))| ≤
      (C*E*radius)*(kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) := by
    calc
      _ = |∑ j : Fin n,(kernelK lam (u-X j)-kernelK lam (u-Y j))| := by rw [Finset.sum_sub_distrib]
      _ ≤ ∑ j : Fin n,|kernelK lam (u-X j)-kernelK lam (u-Y j)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin n,(C*E*radius)*|kernelK lam (u-Y j)/w j| := Finset.sum_le_sum (fun j _ => hpoint j)
      _ = (C*E*radius)*(∑ j : Fin n,|kernelK lam (u-Y j)/w j|) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left (reference_kernel_absolute_row_bound_all lam h0 hpi Q L Y R M hM hlower u)
        (by dsimp [E]; positivity)
  have he : countingSlope lam (fun _ => 0) L X u-countingSlope lam (fun _ => 0) L Y u=
      -((∑ j : Fin n,kernelK lam (u-X j))-(∑ j : Fin n,kernelK lam (u-Y j))) := by
    unfold countingSlope
    ring
  rw [he,abs_neg]
  exact hsum

/-- The actual counting density near reference quantiles equals L*r_Q
with a uniform explicit error, for either sign of the physical kernel. -/
theorem weighted_configuration_density_error_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (radius : ℝ) (hrad : 0 ≤ radius)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) (u : ℝ) :
    |countingSlope lam (fun _ => 0) L X u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤
      kernelL1Mass (kernelKPrime lam)/2+
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) := by
  have ht := abs_add_le
    (countingSlope lam (fun _ => 0) L X u-countingSlope lam (fun _ => 0) L Y u)
    (countingSlope lam (fun _ => 0) L Y u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u)
  rw [sub_add_sub_cancel] at ht
  apply ht.trans
  exact (add_le_add (weighted_configuration_countingSlope_error_all lam h0 hpi Q L Y X R M hM hlower radius hrad hclose u)
    (reference_density_uniform_error_all lam h0 hpi Q L Y R u)).trans_eq (by ring)

/-- Actual finite-window profile variation on a bounded displacement,
relative to the original profile value. This keeps the cancellation scale
needed in the diagonal Gaudin perturbation estimate. -/
theorem finiteIntervalDensity_relative_translation_error_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q a b eps : ℝ) (hdist : |b-a| ≤ eps) :
    |finiteIntervalDensity lam h0 hpi Q b-finiteIntervalDensity lam h0 hpi Q a| ≤
      (physicalDensityLogConstant lam*Real.exp (physicalDensityLogConstant lam*eps)*
        finiteIntervalDensity lam h0 hpi Q a)*|b-a| := by
  let C := physicalDensityLogConstant lam
  let B := C*Real.exp (C*eps)*finiteIntervalDensity lam h0 hpi Q a
  have hC : 0 ≤ C := (physicalDensityLogConstant_pos lam h0).le
  have hb (x : ℝ) (hx : x ∈ uIcc a b) : ‖finiteIntervalDensityPrimeFunction lam h0 hpi Q x‖ ≤ B := by
    have hd : |x-a| ≤ eps := (abs_sub_left_of_mem_uIcc hx).trans hdist
    have hs := (finiteIntervalDensity_exponential_comparison_all lam h0 hpi Q a x).2
    have hu : finiteIntervalDensity lam h0 hpi Q x ≤
        Real.exp (C*eps)*finiteIntervalDensity lam h0 hpi Q a :=
      hs.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hC))
        (finiteIntervalDensity_pos_all lam h0 hpi Q a).le)
    rw [Real.norm_eq_abs]
    exact (finiteIntervalDensityPrime_relative_bound_all lam h0 hpi Q x).trans
      ((mul_le_mul_of_nonneg_left hu hC).trans_eq (by dsimp [B]; ring))
  have he := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ uIcc a b) => (finiteIntervalDensity_hasDerivAt lam h0 hpi Q x).hasDerivWithinAt)
    hb (convex_uIcc a b : Convex ℝ (uIcc a b)) left_mem_uIcc right_mem_uIcc
  simpa only [Real.norm_eq_abs] using he

end
end SixVertex
