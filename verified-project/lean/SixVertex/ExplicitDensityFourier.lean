import SixVertex.SechFourier

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter

/-- The explicit profile displayed in the manuscript. Equality with the
inverse-defined fullLineDensityFunction is proved separately in
ExplicitDensityIdentification.lean. -/
def explicitDensityProfile (lam u : ℝ) : ℝ :=
  1/(2*lam*Real.cosh (u/(lam/Real.pi)))

/-- The exact rescaling of the actual secant Fourier integrand. -/
theorem explicitDensityProfile_fourier_rescaling (lam : ℝ) (h0 : 0 < lam) (p u : ℝ) :
    Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(explicitDensityProfile lam u : ℂ)=
      (1/(lam : ℂ))*(Complex.exp (-Complex.I*((p*(lam/Real.pi) : ℝ) : ℂ)*((u/(lam/Real.pi) : ℝ) : ℂ))/
        (2*(Real.cosh (u/(lam/Real.pi)) : ℂ))) := by
  have he : lam/Real.pi ≠ 0 := (div_pos h0 Real.pi_pos).ne'
  have hl : (lam : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h0.ne'
  have hc : (Real.cosh (u/(lam/Real.pi)) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne'
  have hp : -Complex.I*((p*(lam/Real.pi) : ℝ) : ℂ)*((u/(lam/Real.pi) : ℝ) : ℂ)=
      -Complex.I*(p : ℂ)*(u : ℂ) := by
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr h0.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  rw [hp]
  unfold explicitDensityProfile
  push_cast
  field_simp [hl,hc]

/-- Genuine absolute integrability of every frequency of the displayed
profile's Fourier integrand. No inverse-density identity is used. -/
theorem explicitDensityProfile_fourier_integrable (lam : ℝ) (h0 : 0 < lam) (p : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(explicitDensityProfile lam u : ℂ)) := by
  have he : lam/Real.pi ≠ 0 := (div_pos h0 Real.pi_pos).ne'
  have hs := ((integrable_sech_fourier (p*(lam/Real.pi))).comp_div he).const_mul (1/(lam : ℂ))
  apply hs.congr
  exact Eventually.of_forall (fun u => (explicitDensityProfile_fourier_rescaling lam h0 p u).symm)

/-- The displayed profile's Fourier transform in the exact manuscript
normalization. Equality with the density constructed as an inverse of
I+K* is proved separately in ExplicitDensityIdentification.lean. -/
theorem integral_explicitDensityProfile_fourier (lam : ℝ) (h0 : 0 < lam) (p : ℝ) :
    (∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(explicitDensityProfile lam u : ℂ))=
      1/(2*(Real.cosh (lam*p/2) : ℂ)) := by
  let eta : ℝ := lam/Real.pi
  have he : 0 < eta := div_pos h0 Real.pi_pos
  have hp : Real.pi*(p*eta)/2=lam*p/2 := by dsimp [eta]; field_simp [Real.pi_ne_zero]
  calc
    _ = ∫ u : ℝ, (1/(lam : ℂ))*(Complex.exp (-Complex.I*((p*eta : ℝ) : ℂ)*((u/eta : ℝ) : ℂ))/(2*(Real.cosh (u/eta) : ℂ))) :=
      integral_congr_ae (Eventually.of_forall (fun u => explicitDensityProfile_fourier_rescaling lam h0 p u))
    _ = (1/(lam : ℂ))*((eta : ℝ) • ((Real.pi : ℂ)/(2*(Real.cosh (Real.pi*(p*eta)/2) : ℂ)))) := by
      rw [integral_const_mul,Measure.integral_comp_div (fun x : ℝ => Complex.exp (-Complex.I*((p*eta : ℝ) : ℂ)*(x : ℂ))/(2*(Real.cosh x : ℂ))) eta,abs_of_pos he,integral_sech_fourier]
    _ = _ := by
      rw [hp]
      change (1/(lam : ℂ))*((eta : ℂ)*((Real.pi : ℂ)/(2*(Real.cosh (lam*p/2) : ℂ))))=_
      dsimp [eta]
      push_cast
      field_simp [Complex.ofReal_ne_zero.mpr h0.ne',Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,
        Complex.ofReal_ne_zero.mpr (Real.cosh_pos (lam*p/2)).ne']

/-- The displayed real density is genuinely integrable. -/
theorem explicitDensityProfile_integrable (lam : ℝ) (h0 : 0 < lam) :
    Integrable (explicitDensityProfile lam) := by
  have hh := (explicitDensityProfile_fourier_integrable lam h0 0).re
  simpa using hh

end
end SixVertex
