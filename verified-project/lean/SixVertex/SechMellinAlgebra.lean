import SixVertex.KernelMass
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Complex.Trigonometric

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- The actual exponential Jacobian converts the middle-line Mellin
kernel into the Fourier integrand of the hyperbolic secant profile. -/
theorem mellin_exp_sech_identity (a t : ℝ) :
    (Real.exp t : ℝ) • (((Real.exp t : ℝ) : ℂ)^(((1-Complex.I*(a : ℂ))/2)-1)/(1+((Real.exp t : ℝ) : ℂ)))=
      Complex.exp (-Complex.I*(a : ℂ)*(t/2 : ℝ))/(2*(Real.cosh (t/2) : ℂ)) := by
  let E : ℂ := Complex.exp ((t : ℂ)/2)
  have hE : E ≠ 0 := Complex.exp_ne_zero _
  have he : ((Real.exp t : ℝ) : ℂ)=E^2 := by
    rw [Complex.ofReal_exp]
    dsimp [E]
    rw [pow_two,← Complex.exp_add]
    congr 1
    ring
  have hc : (2 : ℂ)*(Real.cosh (t/2) : ℂ)=E+E⁻¹ := by
    rw [Real.cosh_eq]
    push_cast
    dsimp [E]
    rw [Complex.exp_neg]
    ring
  have hn : 1+E^2 ≠ 0 := by
    rw [← he,← Complex.ofReal_one,← Complex.ofReal_add]
    exact Complex.ofReal_ne_zero.mpr (by positivity)
  have hl : Complex.log ((Real.exp t : ℝ) : ℂ)=(t : ℂ) := by
    rw [← Complex.ofReal_log (Real.exp_pos t).le,Real.log_exp]
  have hp : ((Real.exp t : ℝ) : ℂ)^(((1-Complex.I*(a : ℂ))/2)-1)=
      Complex.exp (-Complex.I*(a : ℂ)*(t/2 : ℝ))/E := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (Real.exp_pos t).ne'),hl]
    dsimp [E]
    rw [← Complex.exp_sub]
    congr 1
    push_cast
    ring
  change ((Real.exp t : ℝ) : ℂ)*(((Real.exp t : ℝ) : ℂ)^(((1-Complex.I*(a : ℂ))/2)-1)/(1+((Real.exp t : ℝ) : ℂ)))=_
  rw [hp,he,hc]
  have hquad : E+E⁻¹=(1+E^2)/E := by field_simp [hE]; ring
  rw [hquad]
  field_simp [hE,hn]

/-- Gamma reflection at the center of the Mellin strip produces the
actual hyperbolic denominator, with the paper's unnormalized frequency. -/
theorem sin_mellin_half_line (a : ℝ) :
    Complex.sin ((Real.pi : ℂ)*((1-Complex.I*(a : ℂ))/2))=
      (Real.cosh (Real.pi*a/2) : ℂ) := by
  have he : (Real.pi : ℂ)*((1-Complex.I*(a : ℂ))/2)=
      (Real.pi : ℂ)/2-((Real.pi*a/2 : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [he,Complex.sin_pi_div_two_sub,Complex.cos_mul_I,← Complex.ofReal_cosh]

end
end SixVertex
