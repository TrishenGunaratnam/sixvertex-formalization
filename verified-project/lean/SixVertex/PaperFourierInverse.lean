import SixVertex.PaperFourier
import Mathlib.Analysis.Fourier.Inversion

namespace SixVertex
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

/-- Complexification commutes with the actual real convolution transform. -/
theorem paperFourier_real_convolution {k f : ℝ → ℝ} (hk : Integrable k)
    (hf : Integrable f) (p : ℝ) :
    paperFourier (fun u => ((∫ t : ℝ,k t*f (u-t) : ℝ) : ℂ)) p=
      paperFourier (fun u => (k u : ℂ)) p*paperFourier (fun u => (f u : ℂ)) p := by
  have he : (fun u => ((∫ t : ℝ,k t*f (u-t) : ℝ) : ℂ))=
      (fun u => ∫ t : ℝ,(k t : ℂ)*(f (u-t) : ℂ)) := by
    funext u
    rw [← integral_complex_ofReal]
    simp only [Complex.ofReal_mul]
  rw [he]
  exact paperFourier_convolution hk.ofReal hf.ofReal p

/-- The Fourier equation of an actual real integral equation f+k*f=s. -/
theorem paperFourier_real_equation {k f s : ℝ → ℝ} (hk : Integrable k)
    (hf : Integrable f) (heq : ∀ u, f u+(∫ t : ℝ,k t*f (u-t))=s u) (p : ℝ) :
    (1+paperFourier (fun u => (k u : ℂ)) p)*paperFourier (fun u => (f u : ℂ)) p=
      paperFourier (fun u => (s u : ℂ)) p := by
  have hc : Integrable (fun u : ℝ => (∫ t : ℝ,k t*f (u-t) : ℝ)) :=
    hk.integrable_convolution (L := ContinuousLinearMap.mul ℝ ℝ) hf
  have he : (fun u => (f u : ℂ)+((∫ t : ℝ,k t*f (u-t) : ℝ) : ℂ))=
      (fun u => (s u : ℂ)) := by
    funext u
    simpa only [Complex.ofReal_add] using congrArg Complex.ofReal (heq u)
  have ht := congrArg (fun g : ℝ → ℂ => paperFourier g p) he
  have hfc : Integrable (fun u : ℝ => (f u : ℂ)) := hf.ofReal
  have hcc : Integrable (fun u : ℝ => ((∫ t : ℝ,k t*f (u-t) : ℝ) : ℂ)) := hc.ofReal
  rw [paperFourier_add hfc hcc p] at ht
  rw [paperFourier_real_convolution hk hf p] at ht
  calc
    _ = paperFourier (fun u => (f u : ℂ)) p+
      paperFourier (fun u => (k u : ℂ)) p*paperFourier (fun u => (f u : ℂ)) p := by ring
    _ = _ := ht

/-- The actual transform is bounded by the L1 norm. -/
theorem paperFourier_norm_le (f : ℝ → ℂ) (p : ℝ) :
    ‖paperFourier f p‖ ≤ ∫ u : ℝ,‖f u‖ := by
  rw [paperFourier_eq_fourier]
  exact Real.norm_fourier_le_integral_norm f _

/-- Continuity of the angular-frequency transform of an L1 function. -/
theorem paperFourier_continuous {f : ℝ → ℂ} (hf : Integrable f) :
    Continuous (paperFourier f) := by
  have hc : Continuous (𝓕 f) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hf
  have he : paperFourier f=(fun p => 𝓕 f (p/(2*Real.pi))) := funext (paperFourier_eq_fourier f)
  rw [he]
  exact hc.comp (by fun_prop)

/-- Fourier uniqueness for continuous integrable functions when one
common transform is integrable; every premise is explicit. -/
theorem eq_of_paperFourier_eq {f g : ℝ → ℂ} (hfc : Continuous f) (hgc : Continuous g)
    (hf : Integrable f) (hg : Integrable g) (hF : Integrable (𝓕 f))
    (he : ∀ p : ℝ,paperFourier f p=paperFourier g p) : f=g := by
  have hfg : 𝓕 f=𝓕 g := by
    funext xi
    have hh := he (2*Real.pi*xi)
    rw [paperFourier_eq_fourier,paperFourier_eq_fourier,
      show (2*Real.pi*xi)/(2*Real.pi)=xi by field_simp [Real.pi_ne_zero]] at hh
    exact hh
  have hG : Integrable (𝓕 g) := by rw [← hfg]; exact hF
  exact (hfc.fourierInv_fourier_eq hf hF).symm.trans
    ((congrArg (fun h : ℝ → ℂ => 𝓕⁻ h) hfg).trans (hgc.fourierInv_fourier_eq hg hG))

end
end SixVertex
