import SixVertex.PhysicalKernelFourier

namespace SixVertex
noncomputable section

/-- The exact hyperbolic identity behind the density resolvent multiplier. -/
theorem density_sinh_sum (lam p : ℝ) :
    Real.sinh (Real.pi*p/2)+Real.sinh ((Real.pi-2*lam)*p/2)=
      2*Real.sinh ((Real.pi-lam)*p/2)*Real.cosh (lam*p/2) := by
  rw [show Real.pi*p/2=(Real.pi-lam)*p/2+lam*p/2 by ring,
    show (Real.pi-2*lam)*p/2=(Real.pi-lam)*p/2-lam*p/2 by ring,
    Real.sinh_add,Real.sinh_sub]
  ring

/-- Exact cancellation of the nonzero-frequency physical kernel and
source multipliers. -/
theorem density_fourier_multiplier (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (p : ℝ) (hp : p ≠ 0) :
    (1+Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2))*
      (1/(2*Real.cosh (lam*p/2)))=
      Real.sinh ((Real.pi-lam)*p/2)/Real.sinh (Real.pi*p/2) := by
  have hd : Real.sinh (Real.pi*p/2) ≠ 0 := Real.sinh_ne_zero.mpr
    (div_ne_zero (mul_ne_zero Real.pi_ne_zero hp) (by norm_num))
  have hc := (Real.cosh_pos (lam*p/2)).ne'
  field_simp [hd,hc]
  rw [show p*(Real.pi-lam)/2=(Real.pi-lam)*p/2 by ring]
  nlinarith only [density_sinh_sum lam p]

/-- The physical resolvent multiplier has no real nonzero-frequency zero. -/
theorem density_fourier_multiplier_ne_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (p : ℝ) (hp : p ≠ 0) :
    1+Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) ≠ 0 := by
  have hd : Real.sinh (Real.pi*p/2) ≠ 0 := Real.sinh_ne_zero.mpr
    (div_ne_zero (mul_ne_zero Real.pi_ne_zero hp) (by norm_num))
  have hn : Real.sinh ((Real.pi-lam)*p/2) ≠ 0 := Real.sinh_ne_zero.mpr
    (div_ne_zero (mul_ne_zero (sub_pos.mpr hpi).ne' hp) (by norm_num))
  intro he
  have hi := density_fourier_multiplier lam h0 hpi p hp
  rw [he,zero_mul] at hi
  exact (div_ne_zero hn hd) hi.symm

end
end SixVertex
