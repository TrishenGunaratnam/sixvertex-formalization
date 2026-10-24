import SixVertex.MobiusIntegralSubstitution
import SixVertex.MellinJacobian
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- The true positive-half-line Mellin integral equals the beta integral,
by the actual Mobius Jacobian, with no integral assigned by definition. -/
theorem integral_euler_mellin_eq_beta (z : ℂ) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/(1+(t : ℂ)))=Complex.betaIntegral z (1-z) := by
  rw [← integral_mobius_positive_half_line]
  rw [Complex.betaIntegral,intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  have he : (1-z)-1=-z := by ring
  rw [he]
  exact mellin_mobius_jacobian z x hx

/-- Integrability of the actual Mellin kernel throughout its convergence strip. -/
theorem integrableOn_euler_mellin (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) :
    IntegrableOn (fun t : ℝ => (t : ℂ)^(z-1)/(1+(t : ℂ))) (Ioi (0 : ℝ)) := by
  have hz : 0 < (1-z).re := by simpa only [Complex.sub_re,Complex.one_re] using sub_pos.mpr h1
  have hb := (intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num : (0 : ℝ) ≤ 1)).mp
    (Complex.betaIntegral_convergent h0 hz)
  apply (integrable_mobius_positive_half_line _).mp
  apply hb.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have he : (1-z)-1=-z := by ring
  change (x : ℂ)^(z-1)*(1-(x : ℂ))^((1-z)-1)=_
  rw [he]
  exact (mellin_mobius_jacobian z x hx).symm

/-- Euler's Mellin integral, genuinely evaluated using the proved beta
and gamma reflection formulas in the open convergence strip. -/
theorem integral_euler_mellin (z : ℂ) (h0 : 0 < z.re) (h1 : z.re < 1) :
    (∫ t in Ioi (0 : ℝ), (t : ℂ)^(z-1)/(1+(t : ℂ)))=(Real.pi : ℂ)/Complex.sin ((Real.pi : ℂ)*z) := by
  have hz : 0 < (1-z).re := by simpa only [Complex.sub_re,Complex.one_re] using sub_pos.mpr h1
  rw [integral_euler_mellin_eq_beta,Complex.betaIntegral_eq_Gamma_mul_div z (1-z) h0 hz,
    show z+(1-z)=1 by ring,Complex.Gamma_one,div_one,Complex.Gamma_mul_Gamma_one_sub]

end
end SixVertex
