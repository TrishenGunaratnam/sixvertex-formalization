import SixVertex.CompactTestApproximation
import SixVertex.SmoothQuadrature
import SixVertex.QuadratureLocalMass

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter

/-- Uniform approximation of compact tests transfers to their integrals
against the actual reciprocal-density atomic measure. -/
theorem rootQuadrature_integral_approximation_error {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Z : Fin n → ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi)
    (hZ : ConsecutiveRoots lam b L Z 0) (phi psi : BoundedRealFunction)
    (a z eps : ℝ) (haz : a ≤ z) (heps : 0 ≤ eps)
    (hsphi : ∀ x, x ∉ Icc a z → phi x=0) (hspsi : ∀ x, x ∉ Icc a z → psi x=0)
    (hnear : ‖phi-psi‖ ≤ eps) :
    |(∫ x, phi x ∂rootQuadratureMeasure lam b L Z)-(∫ x, psi x ∂rootQuadratureMeasure lam b L Z)| ≤
      eps*((Real.exp (kernelLogConstant lam*(z-a)))^2*(z-a)+
        Real.exp (kernelLogConstant lam*(z-a))/(-kernelK lam 0)) := by
  classical
  rw [integral_rootQuadratureMeasure lam b L hL Z hhalf.le hpi,
    integral_rootQuadratureMeasure lam b L hL Z hhalf.le hpi,← Finset.sum_sub_distrib]
  let s := rootsInInterval Z a z
  have hn (x : ℝ) : |phi x-psi x| ≤ eps := by
    have hh := (phi-psi).norm_coe_le_norm x
    change ‖phi x-psi x‖ ≤ ‖phi-psi‖ at hh
    have hh' : |phi x-psi x| ≤ ‖phi-psi‖ := by simpa only [Real.norm_eq_abs] using hh
    exact hh'.trans hnear
  have hp (j : Fin n) : |phi (Z j)/countingSlope lam b L Z (Z j)-psi (Z j)/countingSlope lam b L Z (Z j)| ≤
      if j ∈ s then eps*(countingSlope lam b L Z (Z j))⁻¹ else 0 := by
    have hr := countingSlope_pos_nonpositiveK lam b L hL Z (Z j) hhalf.le hpi
    by_cases hj : j ∈ s
    · rw [if_pos hj,← sub_div,abs_div,abs_of_pos hr]
      exact (div_le_div_of_nonneg_right (hn (Z j)) hr.le).trans_eq (div_eq_mul_inv _ _)
    · have hnot : Z j ∉ Icc a z := by
        intro hh
        exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ j,hh⟩)
      simp [hj,hsphi (Z j) hnot,hspsi (Z j) hnot]
  have hfilter : (Finset.univ.filter (fun j : Fin n => j ∈ s))=s := by ext j; simp
  calc
    _ ≤ ∑ j : Fin n, |phi (Z j)/countingSlope lam b L Z (Z j)-psi (Z j)/countingSlope lam b L Z (Z j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, if j ∈ s then eps*(countingSlope lam b L Z (Z j))⁻¹ else 0 :=
      Finset.sum_le_sum (fun j _ => hp j)
    _ = eps*(∑ j ∈ s, (countingSlope lam b L Z (Z j))⁻¹) := by rw [← Finset.sum_filter,hfilter,← Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (quadrature_interval_mass_bound lam b L hL Z hhalf hpi hZ a z haz) heps

/-- The Lebesgue integral has the matching uniform compact-test error. -/
theorem lebesgue_integral_approximation_error (phi psi : BoundedRealFunction)
    (a z eps : ℝ) (haz : a ≤ z) (heps : 0 ≤ eps)
    (hsphi : ∀ x, x ∉ Icc a z → phi x=0) (hspsi : ∀ x, x ∉ Icc a z → psi x=0)
    (hnear : ‖phi-psi‖ ≤ eps) :
    |(∫ x : ℝ, phi x)-(∫ x : ℝ, psi x)| ≤ eps*(z-a) := by
  have hphi : (∫ x : ℝ, phi x)=∫ x in Icc a z, phi x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hsphi).symm
  have hpsi : (∫ x : ℝ, psi x)=∫ x in Icc a z, psi x :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero hspsi).symm
  rw [hphi,hpsi,← integral_sub phi.continuous.integrableOn_Icc psi.continuous.integrableOn_Icc]
  have hn (x : ℝ) : ‖phi x-psi x‖ ≤ eps := by
    have hh := (phi-psi).norm_coe_le_norm x
    change ‖phi x-psi x‖ ≤ ‖phi-psi‖ at hh
    exact hh.trans hnear
  have hh := norm_integral_le_of_norm_le_const (μ := volume.restrict (Icc a z)) (Eventually.of_forall hn)
  have hm : (volume.restrict (Icc a z)).real univ=z-a := by
    simpa only [measureReal_def,Measure.restrict_apply_univ] using Real.volume_real_Icc_of_le haz
  rw [hm] at hh
  simpa only [Real.norm_eq_abs] using hh

/-- A genuine stability estimate for the actual quadrature error,
independent of chain length, filling, array and interval position. -/
theorem compact_quadrature_error_transfer {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Z : Fin n → ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi)
    (hZ : ConsecutiveRoots lam b L Z 0) (phi psi : BoundedRealFunction)
    (a z eps : ℝ) (haz : a ≤ z) (heps : 0 ≤ eps)
    (hsphi : ∀ x, x ∉ Icc a z → phi x=0) (hspsi : ∀ x, x ∉ Icc a z → psi x=0)
    (hnear : ‖phi-psi‖ ≤ eps) :
    |(∫ x, phi x ∂rootQuadratureMeasure lam b L Z)-(∫ x : ℝ, phi x)| ≤
      |(∫ x, psi x ∂rootQuadratureMeasure lam b L Z)-(∫ x : ℝ, psi x)|+
      eps*((Real.exp (kernelLogConstant lam*(z-a)))^2*(z-a)+
        Real.exp (kernelLogConstant lam*(z-a))/(-kernelK lam 0)+(z-a)) := by
  have hr := rootQuadrature_integral_approximation_error lam b L hL Z hhalf hpi hZ phi psi a z eps haz heps hsphi hspsi hnear
  have hv := lebesgue_integral_approximation_error phi psi a z eps haz heps hsphi hspsi hnear
  let I (f : BoundedRealFunction) := ∫ x, f x ∂rootQuadratureMeasure lam b L Z
  let V (f : BoundedRealFunction) := ∫ x : ℝ, f x
  change |I phi-I psi| ≤ _ at hr
  have heq : I phi-V phi=(I phi-I psi)+(I psi-V psi)+(V psi-V phi) := by ring
  change |I phi-V phi| ≤ |I psi-V psi|+_
  rw [heq]
  have hh := (abs_add_le ((I phi-I psi)+(I psi-V psi)) (V psi-V phi)).trans
    (add_le_add_left (abs_add_le (I phi-I psi) (I psi-V psi)) _)
  have hv' : |V psi-V phi| ≤ eps*(z-a) := by rw [abs_sub_comm]; exact hv
  nlinarith only [hh,hr,hv']

end
end SixVertex
