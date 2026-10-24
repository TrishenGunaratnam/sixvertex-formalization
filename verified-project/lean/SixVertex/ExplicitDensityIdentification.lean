import SixVertex.FullLineDensityFourier
import SixVertex.ExplicitDensityFourier
import Mathlib.Analysis.Fourier.Inversion

namespace SixVertex
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

/-- Continuity of the actual displayed hyperbolic profile. -/
theorem explicitDensityProfile_continuous (lam : ℝ) (h0 : 0 < lam) :
    Continuous (explicitDensityProfile lam) := by
  unfold explicitDensityProfile
  apply Continuous.div continuous_const (by fun_prop)
  intro u
  exact mul_ne_zero (mul_ne_zero (by norm_num) h0.ne') (Real.cosh_pos _).ne'

private theorem profile_normalized_fourier (lam : ℝ) (h0 : 0 < lam) (xi : ℝ) :
    𝓕 (fun u => (explicitDensityProfile lam u : ℂ)) xi=
      1/(2*(Real.cosh (Real.pi*lam*xi) : ℂ)) := by
  have hh := integral_explicitDensityProfile_fourier lam h0 (2*Real.pi*xi)
  change paperFourier (fun u => (explicitDensityProfile lam u : ℂ)) (2*Real.pi*xi)=_ at hh
  rw [paperFourier_eq_fourier,
    show (2*Real.pi*xi)/(2*Real.pi)=xi by field_simp [Real.pi_ne_zero],
    show lam*(2*Real.pi*xi)/2=Real.pi*lam*xi by ring] at hh
  exact hh

private theorem density_normalized_fourier (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (xi : ℝ) :
    𝓕 (fun u => (fullLineDensityFunction lam h0 hpi u : ℂ)) xi=
      1/(2*(Real.cosh (Real.pi*lam*xi) : ℂ)) := by
  have hh := fullLineDensityFunction_fourier lam h0 hpi (2*Real.pi*xi)
  rw [paperFourier_eq_fourier,
    show (2*Real.pi*xi)/(2*Real.pi)=xi by field_simp [Real.pi_ne_zero],
    show lam*(2*Real.pi*xi)/2=Real.pi*lam*xi by ring] at hh
  exact hh

/-- The transform used in Fourier inversion is genuinely integrable. -/
theorem explicitDensityProfile_fourier_transform_integrable (lam : ℝ) (h0 : 0 < lam) :
    Integrable (𝓕 (fun u => (explicitDensityProfile lam u : ℂ))) := by
  have hi : Integrable (fun x : ℝ => (1 : ℂ)/(2*(Real.cosh x : ℂ))) := by
    simpa using integrable_sech_fourier 0
  have hs := hi.comp_mul_left' (mul_ne_zero Real.pi_ne_zero h0.ne')
  apply hs.congr
  filter_upwards with xi
  exact (profile_normalized_fourier lam h0 xi).symm

/-- The manuscript's displayed full-line density equals the actual density
constructed by the bounded-continuous inverse. This uses Fourier inversion
with proved continuity and integrability on both sides. -/
theorem fullLineDensityFunction_eq_explicitDensityProfile (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (u : ℝ) :
    fullLineDensityFunction lam h0 hpi u=explicitDensityProfile lam u := by
  let f : ℝ → ℂ := fun v => (fullLineDensityFunction lam h0 hpi v : ℂ)
  let g : ℝ → ℂ := fun v => (explicitDensityProfile lam v : ℂ)
  have he : 𝓕 f=𝓕 g := by
    funext xi
    exact (density_normalized_fourier lam h0 hpi xi).trans (profile_normalized_fourier lam h0 xi).symm
  have hgi : Integrable (𝓕 g) := explicitDensityProfile_fourier_transform_integrable lam h0
  have hfi : Integrable (𝓕 f) := by rw [he]; exact hgi
  have hfc : Continuous f := Complex.continuous_ofReal.comp (fullLineDensityFunction lam h0 hpi).continuous
  have hgc : Continuous g := Complex.continuous_ofReal.comp (explicitDensityProfile_continuous lam h0)
  have hif := hfc.fourierInv_fourier_eq (fullLineDensityFunction_integrable lam h0 hpi).ofReal hfi
  have hig := hgc.fourierInv_fourier_eq (explicitDensityProfile_integrable lam h0).ofReal hgi
  have hfg : f=g := hif.symm.trans ((congrArg (fun h : ℝ → ℂ => 𝓕⁻ h) he).trans hig)
  have hp := congrArg (fun h : ℝ → ℂ => (h u).re) hfg
  exact hp

end
end SixVertex
