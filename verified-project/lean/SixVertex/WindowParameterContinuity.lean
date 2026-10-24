import SixVertex.FiniteIntervalDensity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- A moving symmetric interval changes the integral of a bounded
continuous function by at most its sup bound times the moved length. -/
theorem symmetric_interval_integral_norm_sub_le (g : ℝ → ℝ) (hg : Continuous g)
    (C : ℝ) (hC : ∀ x, ‖g x‖ ≤ C) (Q T : ℝ) (hQ : 0 ≤ Q) (hT : 0 ≤ T) :
    ‖(∫ u in Icc (-Q) Q, g u)-(∫ u in Icc (-T) T, g u)‖ ≤ 2*C*|Q-T| := by
  have hI (P : ℝ) (hP : 0 ≤ P) : (∫ u in Icc (-P) P, g u)=∫ u in -P..P, g u := by
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  rw [hI Q hQ,hI T hT]
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (a := -Q) (b := Q)) (hg.intervalIntegrable (μ := volume) (a := Q) (b := T))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (hg.intervalIntegrable (μ := volume) (a := -T) (b := -Q)) (hg.intervalIntegrable (μ := volume) (a := -Q) (b := T))
  have he : (∫ u in -Q..Q, g u)-(∫ u in -T..T, g u)=
      -(∫ u in -T..-Q, g u)-(∫ u in Q..T, g u) := by linarith
  rw [he]
  have hleft := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -T) (b := -Q) (fun x _ => hC x)
  have hright := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := Q) (b := T) (fun x _ => hC x)
  rw [show -Q-(-T)=T-Q by ring] at hleft
  rw [abs_sub_comm T Q] at hleft hright
  calc
    _ ≤ ‖∫ u in -T..-Q, g u‖+‖∫ u in Q..T, g u‖ := by
      simpa only [norm_neg] using norm_sub_le (-(∫ u in -T..-Q, g u)) (∫ u in Q..T, g u)
    _ ≤ C*|Q-T|+C*|Q-T| := add_le_add hleft hright
    _ = _ := by ring

/-- Uniform operator-norm continuity in the interval endpoint. -/
theorem windowConvolutionOperator_lipschitz_Q (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (Q T : ℝ) (hQ : 0 ≤ Q) (hT : 0 ≤ T) :
    ‖windowConvolutionOperator k hk Q-windowConvolutionOperator k hk T‖ ≤ 2*‖k‖*|Q-T| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  apply (BoundedContinuousFunction.norm_le (by positivity : 0 ≤ (2*‖k‖*|Q-T|)*‖f‖)).mpr
  intro u
  change ‖windowConvolutionOperator k hk Q f u-windowConvolutionOperator k hk T f u‖ ≤ _
  rw [windowConvolutionOperator_apply,windowConvolutionOperator_apply]
  have hg : Continuous (fun v : ℝ => k (u-v)*f v) :=
    (k.continuous.comp (continuous_const.sub continuous_id)).mul f.continuous
  have hb (v : ℝ) : ‖k (u-v)*f v‖ ≤ ‖k‖*‖f‖ := by
    rw [norm_mul]
    exact mul_le_mul (k.norm_coe_le_norm _) (f.norm_coe_le_norm _) (norm_nonneg _) (norm_nonneg _)
  have he := symmetric_interval_integral_norm_sub_le _ hg (‖k‖*‖f‖) hb Q T hQ hT
  convert he using 1 <;> ring

end
end SixVertex
