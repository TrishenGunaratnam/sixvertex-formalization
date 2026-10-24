import SixVertex.MellinBeta
import SixVertex.SechMellinAlgebra

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter

/-- Absolute integrability of the genuine secant Fourier integrand,
transported from the proved open-strip beta integral. -/
theorem integrable_sech_fourier (a : ℝ) :
    Integrable (fun x : ℝ => Complex.exp (-Complex.I*(a : ℂ)*(x : ℂ))/(2*(Real.cosh x : ℂ))) := by
  let z : ℂ := (1-Complex.I*(a : ℂ))/2
  have hz : z.re=1/2 := by norm_num [z,Complex.div_re,Complex.mul_re,Complex.mul_im]
  have hm := integrableOn_euler_mellin z (by rw [hz]; norm_num) (by rw [hz]; norm_num)
  have hi := (integrable_comp_exp _).mpr hm
  have hs : Integrable (fun t : ℝ => Complex.exp (-Complex.I*(a : ℂ)*(t/2 : ℝ))/(2*(Real.cosh (t/2) : ℂ))) := by
    apply hi.congr
    exact Eventually.of_forall (fun t => mellin_exp_sech_identity a t)
  exact (integrable_comp_div_iff _ (by norm_num : (2 : ℝ) ≠ 0)).mp hs

/-- Fourier transform of the actual hyperbolic secant function with
unnormalized frequency, derived from Euler's Mellin integral. -/
theorem integral_sech_fourier (a : ℝ) :
    (∫ x : ℝ, Complex.exp (-Complex.I*(a : ℂ)*(x : ℂ))/(2*(Real.cosh x : ℂ)))=
      (Real.pi : ℂ)/(2*(Real.cosh (Real.pi*a/2) : ℂ)) := by
  let z : ℂ := (1-Complex.I*(a : ℂ))/2
  have hz : z.re=1/2 := by norm_num [z,Complex.div_re,Complex.mul_re,Complex.mul_im]
  have hm := integral_euler_mellin z (by rw [hz]; norm_num) (by rw [hz]; norm_num)
  rw [sin_mellin_half_line a] at hm
  have ht : (∫ t : ℝ, Complex.exp (-Complex.I*(a : ℂ)*(t/2 : ℝ))/(2*(Real.cosh (t/2) : ℂ)))=
      (Real.pi : ℂ)/(Real.cosh (Real.pi*a/2) : ℂ) := by
    calc
      _ = ∫ t : ℝ, (Real.exp t : ℝ) • (((Real.exp t : ℝ) : ℂ)^(z-1)/(1+((Real.exp t : ℝ) : ℂ))) :=
        integral_congr_ae (Eventually.of_forall (fun t => (mellin_exp_sech_identity a t).symm))
      _ = _ := (integral_comp_exp _).trans hm
  rw [Measure.integral_comp_div (fun x : ℝ => Complex.exp (-Complex.I*(a : ℂ)*(x : ℂ))/(2*(Real.cosh x : ℂ))) (2 : ℝ)] at ht
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 2)] at ht
  change (2 : ℂ)*(∫ x : ℝ, Complex.exp (-Complex.I*(a : ℂ)*(x : ℂ))/(2*(Real.cosh x : ℂ)))=_ at ht
  have hh : (∫ x : ℝ, Complex.exp (-Complex.I*(a : ℂ)*(x : ℂ))/(2*(Real.cosh x : ℂ)))=
      ((Real.pi : ℂ)/(Real.cosh (Real.pi*a/2) : ℂ))/2 :=
    (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).mpr (by simpa only [mul_comm] using ht)
  rw [hh,div_div]
  congr 1
  ring

end
end SixVertex
