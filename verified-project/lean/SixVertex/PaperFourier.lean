import Mathlib.Analysis.Fourier.Convolution

namespace SixVertex
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform Convolution

/-- The manuscript's Fourier convention, with angular frequency p. -/
def paperFourier (f : ℝ → ℂ) (p : ℝ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*f u

/-- Exact conversion to Mathlib's frequency convention. -/
theorem paperFourier_eq_fourier (f : ℝ → ℂ) (p : ℝ) :
    paperFourier f p = 𝓕 f (p/(2*Real.pi)) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  apply integral_congr_ae
  filter_upwards with u
  simp only [smul_eq_mul]
  congr 2
  push_cast
  field_simp [Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]

/-- Absolute convergence of the angular-frequency transform of an L1 function. -/
theorem paperFourier_integrable {f : ℝ → ℂ} (hf : Integrable f) (p : ℝ) :
    Integrable (fun u : ℝ => Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*f u) := by
  apply hf.mono ((by fun_prop : Continuous (fun u : ℝ =>
    Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ)))).aestronglyMeasurable.mul hf.aestronglyMeasurable)
  filter_upwards with u
  have he : ‖Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))‖=1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re,Complex.mul_im]
  change ‖Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*f u‖ ≤ ‖f u‖
  rw [norm_mul,he,one_mul]

/-- Linearity for actual absolutely integrable functions. -/
theorem paperFourier_add {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (p : ℝ) :
    paperFourier (fun u => f u+g u) p=paperFourier f p+paperFourier g p := by
  unfold paperFourier
  simp_rw [mul_add]
  exact integral_add (paperFourier_integrable hf p) (paperFourier_integrable hg p)

/-- The convolution theorem in precisely the manuscript's normalization. -/
theorem paperFourier_convolution {f g : ℝ → ℂ} (hf : Integrable f) (hg : Integrable g) (p : ℝ) :
    paperFourier (fun u => ∫ t : ℝ, f t*g (u-t)) p=paperFourier f p*paperFourier g p := by
  change paperFourier (f ⋆[ContinuousLinearMap.mul ℂ ℂ] g) p=_
  rw [paperFourier_eq_fourier,paperFourier_eq_fourier,paperFourier_eq_fourier]
  exact Real.fourier_mul_convolution_eq hf hg _

end
end SixVertex
