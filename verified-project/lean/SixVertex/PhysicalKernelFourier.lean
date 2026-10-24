import SixVertex.KernelDampedMellin
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

private lemma mellin_sine_denominator_zero (p : ℝ) :
    Complex.sin ((Real.pi : ℂ)*(1-Complex.I*(p : ℂ)/2))=
      (Real.sinh (Real.pi*p/2) : ℂ)*Complex.I := by
  have he : (Real.pi : ℂ)*(1-Complex.I*(p : ℂ)/2)=
      (Real.pi : ℂ)-((Real.pi*p/2 : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [he,Complex.sin_pi_sub,Complex.sin_mul_I,← Complex.ofReal_sinh]

private lemma mellin_sine_numerator_zero (alpha p : ℝ) :
    Complex.sin ((alpha : ℂ)*(-Complex.I*(p : ℂ)/2))=
      -(Real.sinh (alpha*p/2) : ℂ)*Complex.I := by
  have he : (alpha : ℂ)*(-Complex.I*(p : ℂ)/2)=
      -((alpha*p/2 : ℝ) : ℂ)*Complex.I := by push_cast; ring
  rw [he,Complex.sin_mul_I,Complex.sinh_neg,← Complex.ofReal_sinh]

/-- The actual physical interaction-kernel transform at every nonzero
real frequency,obtained by a genuine limit of the evaluated damped integrals. -/
theorem kernelK_fourier_nonzero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (p : ℝ) (hp : p ≠ 0) :
    (∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(kernelK lam u : ℂ))=
      ((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ) := by
  let f : ℝ → ℂ := fun eps => ∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*
    ((Real.exp (-2*eps*u)*kernelK lam u : ℝ) : ℂ)
  let g : ℝ → ℂ := fun eps =>
    Complex.sin (((2*lam-Real.pi : ℝ) : ℂ)*(-(eps : ℂ)-Complex.I*(p : ℂ)/2))/
      Complex.sin ((Real.pi : ℂ)*(1-(eps : ℂ)-Complex.I*(p : ℂ)/2))
  have hs : Real.sinh (Real.pi*p/2) ≠ 0 := Real.sinh_ne_zero.mpr
    (div_ne_zero (mul_ne_zero Real.pi_ne_zero hp) (by norm_num))
  have hsc : (Real.sinh (Real.pi*p/2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hs
  have hd : Complex.sin ((Real.pi : ℂ)*(1-(0 : ℂ)-Complex.I*(p : ℂ)/2)) ≠ 0 := by
    rw [sub_zero,mellin_sine_denominator_zero]
    exact mul_ne_zero hsc Complex.I_ne_zero
  have hg : ContinuousAt g 0 := by
    dsimp [g]
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    exact hd
  have hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    (kernelK_damped_fourier_continuousAt_zero lam h0 hpi p).tendsto.mono_left nhdsWithin_le_nhds
  have hgt : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) := hg.tendsto.mono_left nhdsWithin_le_nhds
  have he : f =ᶠ[𝓝[>] (0 : ℝ)] g := by
    have he1 : ∀ᶠ eps in 𝓝[>] (0 : ℝ), eps < 1 :=
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
    have he0 : ∀ᶠ eps in 𝓝[>] (0 : ℝ), 0 < eps := self_mem_nhdsWithin
    filter_upwards [he0,he1] with eps heps heps1
    exact integral_damped_kernelK_mellin lam h0 hpi eps heps heps1 p
  have heq : f 0=g 0 := tendsto_nhds_unique (hf.congr' he) hgt
  have hf0 : f 0=(∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(kernelK lam u : ℂ)) := by
    dsimp [f]
    simp
  have hg0 : g 0=((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ) := by
    dsimp [g]
    simp only [Complex.ofReal_zero,neg_zero,zero_sub,sub_zero]
    rw [show -(Complex.I*(p : ℂ)/2)= -Complex.I*(p : ℂ)/2 by ring]
    rw [mellin_sine_numerator_zero,mellin_sine_denominator_zero]
    rw [show (2*lam-Real.pi)*p/2= -((Real.pi-2*lam)*p/2) by ring,
      Real.sinh_neg,Complex.ofReal_neg,neg_neg,Complex.ofReal_div]
    field_simp [hsc,Complex.I_ne_zero]
  exact hf0.symm.trans (heq.trans hg0)

/-- All real frequencies,with the paper's continuous zero-frequency
value encoded explicitly rather than a literal sinh(0)/sinh(0). -/
theorem kernelK_fourier_formula (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (p : ℝ) :
    (∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(kernelK lam u : ℂ))=
      ((if p=0 then 1-2*lam/Real.pi else Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ) := by
  by_cases hp : p=0
  · subst p
    simp only [Complex.ofReal_zero,mul_zero,zero_mul,neg_zero,Complex.exp_zero,one_mul]
    simp only [ite_true]
    rw [integral_complex_ofReal,integral_kernelK lam h0 hpi]
  · simp only [if_neg hp]
    exact kernelK_fourier_nonzero lam h0 hpi p hp

/-- The actual source-kernel transform follows from its proved physical
half-parameter identity,including the continuous zero-frequency value. -/
theorem kernelS_fourier_formula (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (p : ℝ) :
    (∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(kernelS lam u : ℂ))=
      ((if p=0 then 1-lam/Real.pi else Real.sinh ((Real.pi-lam)*p/2)/Real.sinh (Real.pi*p/2) : ℝ) : ℂ) := by
  have he : kernelS lam=kernelK (lam/2) := funext (kernelS_eq_phaseDensity lam)
  rw [he,kernelK_fourier_formula (lam/2) (by linarith) (by linarith [Real.pi_pos]) p]
  have hh : 2*(lam/2)=lam := by ring
  rw [hh]

end
end SixVertex
