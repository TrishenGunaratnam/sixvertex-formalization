import SixVertex.RootIntervalCount
import SixVertex.DensityRegularity

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- The actual reciprocal-density root weights have uniformly bounded
mass on every fixed interval, throughout the strict negative-kernel
regime and at every filling. No density asymptotics or terminal-edge
location is assumed. -/
theorem quadrature_interval_mass_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0) (a z : ℝ) (haz : a ≤ z) :
    (∑ j ∈ rootsInInterval Y a z, (countingSlope lam b L Y (Y j))⁻¹) ≤
      (Real.exp (kernelLogConstant lam*(z-a)))^2*(z-a)+
        Real.exp (kernelLogConstant lam*(z-a))/(-kernelK lam 0) := by
  classical
  let s := rootsInInterval Y a z
  let R : ℝ := z-a
  let E : ℝ := Real.exp (kernelLogConstant lam*R)
  have hR : 0 ≤ R := sub_nonneg.mpr haz
  have hE : 0 < E := Real.exp_pos _
  have hk0 : 0 < -kernelK lam 0 := neg_pos.mpr (kernelK_strict_neg lam 0 hhalf hpi)
  change (∑ j ∈ s, (countingSlope lam b L Y (Y j))⁻¹) ≤ E^2*R+E/(-kernelK lam 0)
  by_cases hs : s.Nonempty
  · obtain ⟨j0,hj0⟩ := hs
    have hy0 : a ≤ Y j0 ∧ Y j0 ≤ z := (Finset.mem_filter.mp hj0).2
    let p : ℝ := countingSlope lam b L Y (Y j0)
    have hp : 0 < p := countingSlope_pos_nonpositiveK lam b L hL Y _ hhalf.le hpi
    have hself : -kernelK lam 0 ≤ p := countingSlope_root_lower_bound lam b L Y hhalf.le hpi j0
    have hdist (v : ℝ) (hv : v ∈ Icc a z) : |v-Y j0| ≤ R := by
      apply abs_le.mpr
      dsimp [R]
      constructor <;> linarith [hv.1,hv.2,hy0.1,hy0.2]
    have hup (v : ℝ) (hv : v ∈ Icc a z) : countingSlope lam b L Y v ≤ E*p := by
      have hh := (countingSlope_exponential_comparison lam b L hL Y hhalf.le hpi (Y j0) v).2
      have he : Real.exp (kernelLogConstant lam*|v-Y j0|) ≤ E := Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left (hdist v hv) (kernelLogConstant_nonneg lam))
      exact hh.trans (mul_le_mul_of_nonneg_right he hp.le)
    have hweight (j : Fin n) (hj : j ∈ s) : (countingSlope lam b L Y (Y j))⁻¹ ≤ E/p := by
      have hv : Y j ∈ Icc a z := (Finset.mem_filter.mp hj).2
      have hq : 0 < countingSlope lam b L Y (Y j) := countingSlope_pos_nonpositiveK lam b L hL Y _ hhalf.le hpi
      have hh := (countingSlope_exponential_comparison lam b L hL Y hhalf.le hpi (Y j) (Y j0)).2
      have he : Real.exp (kernelLogConstant lam*|Y j0-Y j|) ≤ E := by
        rw [abs_sub_comm]
        exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hdist (Y j) hv) (kernelLogConstant_nonneg lam))
      have hpq : p ≤ E*countingSlope lam b L Y (Y j) := hh.trans
        (mul_le_mul_of_nonneg_right he hq.le)
      apply (le_div_iff₀ hp).mpr
      have hd := (div_le_iff₀ hq).mpr hpq
      simpa only [div_eq_mul_inv,mul_comm] using hd
    have hxi := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun v (_ : v ∈ Icc a z) =>
        (hasDerivAt_countingXi lam b L Y v (by linarith [Real.pi_pos]) hpi).hasDerivWithinAt)
      (fun v (hv : v ∈ Icc a z) => by
        rw [Real.norm_of_nonneg (countingSlope_pos_nonpositiveK lam b L hL Y v hhalf.le hpi).le]
        exact hup v hv)
      (convex_Icc a z) (left_mem_Icc.mpr haz) (right_mem_Icc.mpr haz)
    have hdiff : countingXi lam b L Y z-countingXi lam b L Y a ≤ E*p*R := by
      have hh := (le_abs_self (countingXi lam b L Y z-countingXi lam b L Y a)).trans hxi
      simpa only [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr haz)] using hh
    have hcount : (s.card : ℝ) ≤ E*p*R+1 :=
      (consecutive_roots_interval_count lam b L hL Y hhalf.le hpi hroots a z haz).trans (add_le_add hdiff le_rfl)
    calc
      _ ≤ ∑ _j ∈ s, E/p := Finset.sum_le_sum hweight
      _ = (s.card : ℝ)*(E/p) := by rw [Finset.sum_const,nsmul_eq_mul]
      _ ≤ (E*p*R+1)*(E/p) := mul_le_mul_of_nonneg_right hcount (div_nonneg hE.le hp.le)
      _ = E^2*R+E/p := by field_simp [hp.ne']
      _ ≤ _ := add_le_add le_rfl (div_le_div_of_nonneg_left hE.le hk0 hself)
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    rw [he,Finset.sum_empty]
    positivity

end
end SixVertex
