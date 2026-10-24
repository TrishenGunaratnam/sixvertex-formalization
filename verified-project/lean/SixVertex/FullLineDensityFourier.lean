import SixVertex.PaperFourier
import SixVertex.PhysicalKernelFourier
import SixVertex.DensityFourierAlgebra
import SixVertex.FullLineDensity

namespace SixVertex
noncomputable section
open MeasureTheory Filter

/-- Taking the actual angular-frequency transform of the proved
inverse-density integral equation, with its convolution justified in L1. -/
theorem fullLineDensityFunction_fourier_equation (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (p : ℝ) :
    (1+paperFourier (fun u => (kernelK lam u : ℂ)) p)*
      paperFourier (fun u => (fullLineDensityFunction lam h0 hpi u : ℂ)) p=
      paperFourier (fun u => (kernelS lam u : ℂ)) p := by
  let r := fullLineDensityFunction lam h0 hpi
  let k := kernelK lam
  have hr : Integrable (fun u : ℝ => (r u : ℂ)) :=
    (fullLineDensityFunction_integrable lam h0 hpi).ofReal
  have hk : Integrable (fun u : ℝ => (k u : ℂ)) :=
    (kernelK_integrable lam h0 hpi).ofReal
  have hc : Integrable (fun u : ℝ => ∫ t : ℝ, (k t : ℂ)*(r (u-t) : ℂ)) :=
    hk.integrable_convolution (L := ContinuousLinearMap.mul ℂ ℂ) hr
  have he : (fun u : ℝ => (r u : ℂ)+(∫ t : ℝ,(k t : ℂ)*(r (u-t) : ℂ)))=
      (fun u : ℝ => (kernelS lam u : ℂ)) := by
    funext u
    have hh := congrArg (fun f : BoundedRealFunction => f u)
      (fullLineDensityFunction_equation lam h0 hpi)
    change r u+(∫ t : ℝ,k t*r (u-t))=_ at hh
    rw [physicalSourceFunction_apply] at hh
    have hj := congrArg Complex.ofReal hh
    rw [Complex.ofReal_add,← integral_complex_ofReal] at hj
    simpa only [Complex.ofReal_mul] using hj
  have ht := congrArg (fun f : ℝ → ℂ => paperFourier f p) he
  rw [paperFourier_add hr hc p,paperFourier_convolution hk hr p] at ht
  change (1+paperFourier (fun u => (k u : ℂ)) p)*paperFourier (fun u => (r u : ℂ)) p=_
  calc
    _ = paperFourier (fun u => (r u : ℂ)) p+
      paperFourier (fun u => (k u : ℂ)) p*paperFourier (fun u => (r u : ℂ)) p := by ring
    _ = _ := ht

/-- The actual inverse-defined density has the manuscript's hyperbolic
secant transform at every real frequency, including zero. -/
theorem fullLineDensityFunction_fourier (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (p : ℝ) :
    paperFourier (fun u => (fullLineDensityFunction lam h0 hpi u : ℂ)) p=
      1/(2*(Real.cosh (lam*p/2) : ℂ)) := by
  by_cases hp : p=0
  · subst p
    unfold paperFourier
    simp only [Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,one_mul,
      Real.cosh_zero,Complex.ofReal_one]
    rw [integral_complex_ofReal,integral_fullLineDensityFunction lam h0 hpi]
    norm_num
  · have he := fullLineDensityFunction_fourier_equation lam h0 hpi p
    change (1+(∫ u : ℝ,Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(kernelK lam u : ℂ)))*
      paperFourier (fun u => (fullLineDensityFunction lam h0 hpi u : ℂ)) p=
      (∫ u : ℝ,Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(kernelS lam u : ℂ)) at he
    rw [kernelK_fourier_formula lam h0 hpi p,kernelS_fourier_formula lam h0 hpi p] at he
    simp only [if_neg hp] at he
    have hn : (1+((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ)) ≠ 0 := by
      exact_mod_cast density_fourier_multiplier_ne_zero lam h0 hpi p hp
    have hm : (1+((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ))*
        (1/(2*(Real.cosh (lam*p/2) : ℂ)))=
        ((Real.sinh ((Real.pi-lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ) := by
      exact_mod_cast density_fourier_multiplier lam h0 hpi p hp
    apply mul_left_cancel₀ hn
    exact he.trans hm.symm

end
end SixVertex
