import SixVertex.PositiveDressingKernel
import SixVertex.FullLineDensityFourier

namespace SixVertex
noncomputable section
open MeasureTheory Filter

private theorem angular_real_zero (f : ℝ → ℝ) :
    paperFourier (fun u => (f u : ℂ)) 0=((∫ u : ℝ,f u : ℝ) : ℂ) := by
  simp [paperFourier,integral_complex_ofReal]

/-- The actual J and density transforms satisfy the physical resolvent
equation, including frequency zero with its true integral value. -/
theorem positiveDressingKernel_resolvent_multiplier (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (p : ℝ) :
    (1+paperFourier (fun u => (kernelK lam u : ℂ)) p)*
      (paperFourier (fun u => (positiveDressingKernel lam u : ℂ)) p*
        paperFourier (fun u => (fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) u : ℂ)) p)=
      paperFourier (fun u => (kernelK lam u : ℂ)) p := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  by_cases hp : p=0
  · subst p
    rw [angular_real_zero,angular_real_zero,angular_real_zero,
      integral_kernelK lam h0 hpi,integral_positiveDressingKernel lam h0 hh,
      integral_fullLineDensityFunction lam h0 hpi]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
      show (Real.pi : ℂ)-(lam : ℂ) ≠ 0 by exact_mod_cast (show Real.pi-lam ≠ 0 by linarith)]
    <;> ring
  · have hk : paperFourier (fun u => (kernelK lam u : ℂ)) p=
        ((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ) :=
      kernelK_fourier_nonzero lam h0 hpi p hp
    rw [hk,positiveDressingKernel_fourier_nonzero lam h0 hh p hp,
      fullLineDensityFunction_fourier lam h0 hpi p]
    have hm : (1+((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ))*
        (1/(2*(Real.cosh (lam*p/2) : ℂ)))=
        ((Real.sinh ((Real.pi-lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ) := by
      exact_mod_cast density_fourier_multiplier lam h0 hpi p hp
    have hb : (Real.sinh ((Real.pi-lam)*p/2) : ℂ) ≠ 0 := by
      exact Complex.ofReal_ne_zero.mpr (Real.sinh_ne_zero.mpr
        (div_ne_zero (mul_ne_zero (show Real.pi-lam ≠ 0 by linarith) hp) (by norm_num)))
    calc
      _ = ((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh ((Real.pi-lam)*p/2) : ℝ) : ℂ)*
        ((1+((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ))*
          (1/(2*(Real.cosh (lam*p/2) : ℂ)))) := by ring
      _ = _ := by
        rw [hm,Complex.ofReal_div,Complex.ofReal_div,Complex.ofReal_div]
        exact div_mul_div_cancel₀ hb

end
end SixVertex
