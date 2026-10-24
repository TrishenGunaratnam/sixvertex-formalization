import SixVertex.SlitMellinBounds
import Mathlib.Analysis.Calculus.ParametricIntegral

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

/-- A linear denominator lower bound yields an actual integrable
Euler-kernel majorant for the shifted Mellin integrand. -/
theorem shifted_mellin_kernel_norm_bound (z a : ℂ) (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (hden : c*(1+t) ≤ ‖(t : ℂ)+a‖) :
    ‖(t : ℂ)^(z-1)/((t : ℂ)+a)‖ ≤ (1/c)*‖(t : ℂ)^(z-1)/(1+(t : ℂ))‖ := by
  have hp : 0 < 1+t := by linarith
  have hn : ‖(1 : ℂ)+(t : ℂ)‖=1+t := by
    rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_of_nonneg hp.le]
  rw [norm_div,norm_div,hn]
  calc
    _ ≤ ‖(t : ℂ)^(z-1)‖/(c*(1+t)) := div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos hc hp) hden
    _ = _ := by field_simp

/-- The parameter derivative has the same Euler majorant,up to c^-2. -/
theorem shifted_mellin_deriv_norm_bound (z a : ℂ) (c t : ℝ) (hc : 0 < c) (ht : 0 ≤ t)
    (hden : c*(1+t) ≤ ‖(t : ℂ)+a‖) :
    ‖-(t : ℂ)^(z-1)/((t : ℂ)+a)^2‖ ≤ (1/c^2)*‖(t : ℂ)^(z-1)/(1+(t : ℂ))‖ := by
  have hp : 0 < 1+t := by linarith
  have hs : c^2*(1+t) ≤ ‖(t : ℂ)+a‖^2 := by
    have hsq := mul_nonneg (sub_nonneg.mpr hden)
      (add_nonneg (norm_nonneg ((t : ℂ)+a)) (mul_nonneg hc.le hp.le))
    have hsp : c^2*(1+t) ≤ (c*(1+t))^2 := by nlinarith [sq_nonneg c,mul_nonneg (sq_nonneg c) ht,sq_nonneg (c*t)]
    nlinarith only [hsq,hsp]
  have hn : ‖(1 : ℂ)+(t : ℂ)‖=1+t := by
    rw [← Complex.ofReal_one,← Complex.ofReal_add,Complex.norm_of_nonneg hp.le]
  rw [norm_div,norm_neg,norm_pow,norm_div,hn]
  calc
    _ ≤ ‖(t : ℂ)^(z-1)‖/(c^2*(1+t)) :=
      div_le_div_of_nonneg_left (norm_nonneg _) (mul_pos (sq_pos_of_pos hc) hp) hs
    _ = _ := by field_simp

private lemma continuousOn_mellin_power (z : ℂ) :
    ContinuousOn (fun t : ℝ => (t : ℂ)^(z-1)) (Ioi (0 : ℝ)) := by
  apply continuousOn_of_forall_continuousAt
  intro t ht
  apply ContinuousAt.cpow (by fun_prop) (by fun_prop)
  exact Complex.ofReal_mem_slitPlane.mpr ht

/-- Continuity on the integration half-line follows from the genuine
nonvanishing denominator and the principal complex-power branch. -/
theorem continuousOn_shifted_mellin_kernel (z a : ℂ)
    (hne : ∀ t : ℝ, 0 ≤ t → (t : ℂ)+a ≠ 0) :
    ContinuousOn (fun t : ℝ => (t : ℂ)^(z-1)/((t : ℂ)+a)) (Ioi (0 : ℝ)) := by
  apply (continuousOn_mellin_power z).div (by fun_prop)
  intro t ht
  exact hne t ht.le

/-- Continuity of the genuine parameter derivative on the integration half-line. -/
theorem continuousOn_shifted_mellin_derivative (z a : ℂ)
    (hne : ∀ t : ℝ, 0 ≤ t → (t : ℂ)+a ≠ 0) :
    ContinuousOn (fun t : ℝ => -(t : ℂ)^(z-1)/((t : ℂ)+a)^2) (Ioi (0 : ℝ)) := by
  apply (continuousOn_mellin_power z).neg.div ((by fun_prop : ContinuousOn (fun t : ℝ => (t : ℂ)+a) (Ioi (0 : ℝ))).pow 2)
  intro t ht
  exact pow_ne_zero 2 (hne t ht.le)

/-- The actual shifted Mellin integrand is absolutely integrable
throughout the slit parameter plane and open Mellin convergence strip. -/
theorem integrableOn_shifted_mellin_kernel (z a : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1)
    (ha : a ∈ Complex.slitPlane) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(z-1)/((t : ℂ)+a)) (Ioi (0 : ℝ)) := by
  obtain ⟨c,hc,hbound⟩ := exists_slit_mellin_denominator_bound a ha
  have hne (t : ℝ) (ht : 0 ≤ t) : (t : ℂ)+a ≠ 0 := by
    apply norm_pos_iff.mp
    exact (mul_pos hc (by linarith : 0 < 1+t)).trans_le (hbound t ht)
  apply ((integrableOn_euler_mellin z h0 h1).norm.const_mul (1/c)).mono'
    ((continuousOn_shifted_mellin_kernel z a hne).aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  exact shifted_mellin_kernel_norm_bound z a c t hc ht.le (hbound t ht.le)

end
end SixVertex
