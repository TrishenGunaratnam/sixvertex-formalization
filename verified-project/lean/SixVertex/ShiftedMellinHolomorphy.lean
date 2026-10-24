import SixVertex.ShiftedMellinIntegrability
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Analytic.IsolatedZeros

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

/-- Genuine complex differentiation under the shifted Mellin integral,
with the local denominator bound supplying one integrable majorant. -/
theorem hasDerivAt_shifted_mellin_integral (z a : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1)
    (ha : a ∈ Complex.slitPlane) :
    HasDerivAt (fun b : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/((t : ℂ)+b))
      (∫ t in Ioi (0 : ℝ), -(t : ℂ)^(z-1)/((t : ℂ)+a)^2) a := by
  obtain ⟨delta,c,hd,hc,hbound⟩ := exists_local_slit_mellin_denominator_bound a ha
  have hne (b : ℂ) (hb : b ∈ Metric.ball a delta) (t : ℝ) (ht : 0 ≤ t) : (t : ℂ)+b ≠ 0 := by
    apply norm_pos_iff.mp
    exact (mul_pos hc (by linarith : 0 < 1+t)).trans_le (hbound b hb t ht)
  have haBall : a ∈ Metric.ball a delta := Metric.mem_ball_self hd
  have hmeas : ∀ᶠ b in 𝓝 a, AEStronglyMeasurable (fun t : ℝ => (t : ℂ)^(z-1)/((t : ℂ)+b)) (volume.restrict (Ioi (0 : ℝ))) := by
    filter_upwards [Metric.ball_mem_nhds a hd] with b hb
    exact (continuousOn_shifted_mellin_kernel z b (hne b hb)).aestronglyMeasurable measurableSet_Ioi
  have hdmeas := (continuousOn_shifted_mellin_derivative z a (hne a haBall)).aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hbint := (integrableOn_euler_mellin z h0 h1).norm.const_mul (1/c^2)
  have hmajor : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi (0 : ℝ)), ∀ b ∈ Metric.ball a delta,
      ‖-(t : ℂ)^(z-1)/((t : ℂ)+b)^2‖ ≤ (1/c^2)*‖(t : ℂ)^(z-1)/(1+(t : ℂ))‖ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro b hb
    exact shifted_mellin_deriv_norm_bound z b c t hc ht.le (hbound b hb t ht.le)
  have hdiff : ∀ᵐ (t : ℝ) ∂volume.restrict (Ioi (0 : ℝ)), ∀ b ∈ Metric.ball a delta,
      HasDerivAt (fun w : ℂ => (t : ℂ)^(z-1)/((t : ℂ)+w)) (-(t : ℂ)^(z-1)/((t : ℂ)+b)^2) b := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    intro b hb
    have hh := (hasDerivAt_const b ((t : ℂ)^(z-1))).fun_div
      ((hasDerivAt_const b (t : ℂ)).add (hasDerivAt_id b)) (hne b hb t ht.le)
    simpa using! hh
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun b : ℂ => fun t : ℝ => (t : ℂ)^(z-1)/((t : ℂ)+b))
    (F' := fun b : ℂ => fun t : ℝ => -(t : ℂ)^(z-1)/((t : ℂ)+b)^2)
    (bound := fun t : ℝ => (1/c^2)*‖(t : ℂ)^(z-1)/(1+(t : ℂ))‖)
    (μ := volume.restrict (Ioi (0 : ℝ))) (Metric.ball_mem_nhds a hd) hmeas
    (integrableOn_shifted_mellin_kernel z a h0 h1 ha) hdmeas hmajor hbint hdiff).2

/-- Holomorphic dependence holds on the entire genuine slit parameter plane. -/
theorem differentiableOn_shifted_mellin_integral (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) :
    DifferentiableOn ℂ (fun a : ℂ => ∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/((t : ℂ)+a)) Complex.slitPlane := by
  intro a ha
  exact (hasDerivAt_shifted_mellin_integral z a h0 h1 ha).differentiableAt.differentiableWithinAt

end
end SixVertex
