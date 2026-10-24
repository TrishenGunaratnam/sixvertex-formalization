import SixVertex.LipschitzIntegration

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal

/-- Exact atomic integration by parts for a compact Lipschitz function.
Every jump is integrated using the absolutely continuous FTC. -/
theorem integral_deriv_compact_rootCount {n : ℕ} (Y : Fin n → ℝ)
    (f : ℝ → ℝ) (K : ℝ≥0) (hLip : LipschitzWith K f)
    (a z : ℝ) (haz : a ≤ z) (hs : ∀ x, x ∉ Icc a z → f x=0) :
    (∫ x : ℝ, deriv f x*(rootCountLe Y x : ℝ))= -(∑ j : Fin n, f (Y j)) := by
  have hi := lipschitz_compact_deriv_integrable f K hLip a z haz hs
  simp_rw [rootCountLe_eq_sum_indicators,Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [← Set.indicator_mul_right (Ici _) (deriv f) (fun _ : ℝ => (1 : ℝ))]
    simp_rw [integral_indicator measurableSet_Ici,mul_one,
      integral_deriv_Ici_lipschitz_compact f K hLip a z haz hs]
    rw [Finset.sum_neg_distrib]
  · intro j _
    simp_rw [← Set.indicator_mul_right (Ici (Y j)) (deriv f) (fun _ : ℝ => (1 : ℝ))]
    exact (hi.mul_const 1).indicator measurableSet_Ici

/-- Bounded-Lipschitz discrete/smooth error, proved directly from absolute
continuity rather than replacing Lipschitz tests by C1 tests. -/
theorem counting_lipschitz_discrete_smooth_error {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0)
    (f : BoundedRealFunction) (K : ℝ≥0) (hLip : LipschitzWith K (fun x => f x))
    (a z : ℝ) (haz : a ≤ z) (hs : ∀ x, x ∉ Icc a z → f x=0)
    (hwindow : ∀ x ∈ Icc a z, -(n : ℝ)/2 ≤ countingXi lam b L Y x ∧
      countingXi lam b L Y x ≤ (n : ℝ)/2) :
    |(∑ j : Fin n, f (Y j))-(∫ x : ℝ, f x*countingSlope lam b L Y x)| ≤ (z-a)*(K : ℝ)/2 := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let P := generalCountingPrimitiveFunction lam b L Y
  let p := finiteCountingFunction lam h0 hpi b L Y
  have hp : Integrable (fun x => p x) := by
    simp_rw [show ∀ x, p x=countingSlope lam b L Y x from fun x => finiteCountingFunction_apply lam h0 hpi b L Y x]
    exact countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi
  have hdP : ∀ x, HasDerivAt (fun v => P v) (p x) x := by
    intro x
    rw [show p x=countingSlope lam b L Y x from finiteCountingFunction_apply lam h0 hpi b L Y x]
    exact generalCountingPrimitiveFunction_hasDerivAt lam b L Y h0 hpi x
  have he := integral_lipschitz_compact_primitive f P p K hLip a z haz hs hp hdP
  simp_rw [show ∀ x, p x=countingSlope lam b L Y x from fun x => finiteCountingFunction_apply lam h0 hpi b L Y x] at he
  have hdint := lipschitz_compact_deriv_integrable (fun x => f x) K hLip a z haz hs
  have hc := hdint.mul_bdd (rootCountLe_measurable Y).aestronglyMeasurable
    (Eventually.of_forall (rootCountLe_norm_bound Y))
  have hP := hdint.mul_bdd P.continuous.aestronglyMeasurable (Eventually.of_forall P.norm_coe_le_norm)
  have hidentity : (∫ x : ℝ, deriv (fun v => f v) x*countingDiscrepancy lam b L Y x)=
      -((∑ j : Fin n, f (Y j))-(∫ x : ℝ, f x*countingSlope lam b L Y x)) := by
    have ha (x : ℝ) : countingDiscrepancy lam b L Y x=(rootCountLe Y x : ℝ)-P x := by
      rw [show P x=countingXi lam b L Y x+(n : ℝ)/2 from generalCountingPrimitiveFunction_apply lam b L Y x]
      rfl
    simp_rw [ha,mul_sub]
    rw [integral_sub hc hP,integral_deriv_compact_rootCount Y (fun x => f x) K hLip a z haz hs]
    linarith [he]
  have hsupport : ∀ x, x ∉ Icc a z → deriv (fun v => f v) x*countingDiscrepancy lam b L Y x=0 := by
    intro x hx
    rw [deriv_zero_outside_Icc (fun v => f v) a z hs x hx,zero_mul]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc a z)
    (f := fun x : ℝ => deriv (fun v => f v) x*countingDiscrepancy lam b L Y x)
    (C := (K : ℝ)/2) (isCompact_Icc.measure_lt_top) (by
      intro x hx
      rw [norm_mul,Real.norm_eq_abs (countingDiscrepancy lam b L Y x)]
      have hw := hwindow x hx
      have hF := countingDiscrepancy_bound_in_window lam b L hL Y hhalf hpi hroots x hw.1 hw.2
      calc
        _ ≤ ‖deriv (fun v => f v) x‖*(1/2) := mul_le_mul_of_nonneg_left hF (norm_nonneg _)
        _ ≤ (K : ℝ)*(1/2) := mul_le_mul_of_nonneg_right (norm_deriv_le_of_lipschitz hLip) (by norm_num)
        _ = (K : ℝ)/2 := by ring)
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hsupport,hidentity,norm_neg,Real.norm_eq_abs] at hb
  rw [Real.volume_real_Icc_of_le haz] at hb
  convert hb using 1 <;> ring

end
end SixVertex
