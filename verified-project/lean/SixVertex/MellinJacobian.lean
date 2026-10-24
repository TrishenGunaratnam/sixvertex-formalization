import SixVertex.KernelMass
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- The true Mobius Jacobian converts the positive-half-line Mellin
integrand into the beta-integral integrand, with principal complex powers. -/
theorem mellin_mobius_jacobian (z : ℂ) (x : ℝ) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1/(1-x)^2 : ℝ) • ((((x/(1-x) : ℝ) : ℂ))^(z-1)/(1+((x/(1-x) : ℝ) : ℂ)))=
      (x : ℂ)^(z-1)*(1-(x : ℂ))^(-z) := by
  have hd : 0 < 1-x := by linarith [hx.2]
  have hB : ((1-x : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hd.ne'
  have hcast : (1 : ℂ)-(x : ℂ)=((1-x : ℝ) : ℂ) := by push_cast; rfl
  change ((1/(1-x)^2 : ℝ) : ℂ)*((((x/(1-x) : ℝ) : ℂ))^(z-1)/(1+((x/(1-x) : ℝ) : ℂ)))=_
  rw [hcast]
  simp only [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_one]
  rw [Complex.div_cpow_ofReal_nonneg hx.1.le hd.le,Complex.cpow_sub z 1 hB,Complex.cpow_one,Complex.cpow_neg]
  have hp : (((1-x : ℝ) : ℂ))^z ≠ 0 := (Complex.cpow_ne_zero_iff).mpr (Or.inl hB)
  field_simp [hB,hp]
  push_cast
  ring

end
end SixVertex
