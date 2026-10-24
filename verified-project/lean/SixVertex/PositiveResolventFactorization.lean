import SixVertex.PositiveDressingMultiplier
import SixVertex.PaperFourierInverse
import SixVertex.ExplicitDensityIdentification

namespace SixVertex
noncomputable section
open MeasureTheory Filter
open scoped FourierTransform

/-- The actual positive convolution J*r from the manuscript. -/
def positiveResolventCandidate (lam : ℝ) (h0 : 0 < lam) (hh : lam < Real.pi/2) :
    BoundedRealFunction :=
  boundedConvolution (positiveDressingKernel lam) (positiveDressingKernel_integrable lam h0 hh)
    (fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]))

/-- Absolute integrability of the actual positive convolution. -/
theorem positiveResolventCandidate_integrable (lam : ℝ) (h0 : 0 < lam) (hh : lam < Real.pi/2) :
    Integrable (fun u => positiveResolventCandidate lam h0 hh u) :=
  (positiveDressingKernel_integrable lam h0 hh).integrable_convolution
    (L := ContinuousLinearMap.mul ℝ ℝ)
    (fullLineDensityFunction_integrable lam h0 (by linarith [Real.pi_pos]))

/-- Its actual Fourier transform is the product, with both factors in L1. -/
theorem positiveResolventCandidate_fourier (lam : ℝ) (h0 : 0 < lam) (hh : lam < Real.pi/2)
    (p : ℝ) :
    paperFourier (fun u => (positiveResolventCandidate lam h0 hh u : ℂ)) p=
      paperFourier (fun u => (positiveDressingKernel lam u : ℂ)) p*
        paperFourier (fun u => (fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) u : ℂ)) p :=
  paperFourier_real_convolution (positiveDressingKernel_integrable lam h0 hh)
    (fullLineDensityFunction_integrable lam h0 (by linarith [Real.pi_pos])) p

/-- Fourier inversion applies to J*r: its actual transform is integrable. -/
theorem positiveResolventCandidate_fourier_integrable (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    Integrable (𝓕 (fun u => (positiveResolventCandidate lam h0 hh u : ℂ))) := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  let j : ℝ → ℂ := fun u => (positiveDressingKernel lam u : ℂ)
  let r : ℝ → ℂ := fun u => (fullLineDensityFunction lam h0 hpi u : ℂ)
  have hj : Integrable j := (positiveDressingKernel_integrable lam h0 hh).ofReal
  have hjc : Continuous (𝓕 j) :=
    VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar (innerSL ℝ).continuous₂ hj
  have hr : Integrable (𝓕 r) := by
    have he : r=(fun u => (explicitDensityProfile lam u : ℂ)) := by
      funext u
      exact congrArg Complex.ofReal (fullLineDensityFunction_eq_explicitDensityProfile lam h0 hpi u)
    rw [he]
    exact explicitDensityProfile_fourier_transform_integrable lam h0
  have hb := hr.mul_bdd hjc.aestronglyMeasurable
    (Eventually.of_forall (fun xi => Real.norm_fourier_le_integral_norm j xi))
  apply hb.congr
  filter_upwards with xi
  have he := positiveResolventCandidate_fourier lam h0 hh (2*Real.pi*xi)
  rw [paperFourier_eq_fourier,paperFourier_eq_fourier,paperFourier_eq_fourier,
    show (2*Real.pi*xi)/(2*Real.pi)=xi by field_simp [Real.pi_ne_zero]] at he
  simpa only [mul_comm] using he.symm

/-- The actual Neumann resolvent has the same real-frequency transform
as J*r; the multiplier cancellation is justified, including zero. -/
theorem physicalResolventKernel_fourier_eq_positiveCandidate (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (p : ℝ) :
    paperFourier (fun u => (physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) u : ℂ)) p=
      paperFourier (fun u => (positiveResolventCandidate lam h0 hh u : ℂ)) p := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have he := paperFourier_real_equation (kernelK_integrable lam h0 hpi)
    (physicalResolventKernel_decay lam h0 hpi).1 (physicalResolventKernel_equation lam h0 hpi) p
  have hm := positiveDressingKernel_resolvent_multiplier lam h0 hh p
  have hn : (1+paperFourier (fun u => (kernelK lam u : ℂ)) p) ≠ 0 := by
    by_cases hp : p=0
    · subst p
      unfold paperFourier
      simp only [Complex.ofReal_zero,mul_zero,zero_mul,Complex.exp_zero,one_mul]
      rw [integral_complex_ofReal,integral_kernelK lam h0 hpi]
      have hl : 0 < 1+(1-2*lam/Real.pi) := by
        have hd := (div_lt_one Real.pi_pos).mpr hpi
        rw [show 2*lam/Real.pi=2*(lam/Real.pi) by ring]
        linarith
      exact_mod_cast hl.ne'
    · change (1+(∫ u : ℝ,Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*(kernelK lam u : ℂ))) ≠ 0
      rw [kernelK_fourier_nonzero lam h0 hpi p hp]
      exact_mod_cast density_fourier_multiplier_ne_zero lam h0 hpi p hp
  apply mul_left_cancel₀ hn
  rw [positiveResolventCandidate_fourier]
  exact he.trans hm.symm

/-- Fourier inversion identifies the actual constructed resolvent with
the positive convolution, as functions and not merely as multipliers. -/
theorem physicalResolventKernel_eq_positiveCandidate (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    physicalResolventKernel lam h0 (by linarith [Real.pi_pos])=positiveResolventCandidate lam h0 hh := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have he : (fun u => (positiveResolventCandidate lam h0 hh u : ℂ))=
      (fun u => (physicalResolventKernel lam h0 hpi u : ℂ)) :=
    eq_of_paperFourier_eq
      (Complex.continuous_ofReal.comp (positiveResolventCandidate lam h0 hh).continuous)
      (Complex.continuous_ofReal.comp (physicalResolventKernel lam h0 hpi).continuous)
      (positiveResolventCandidate_integrable lam h0 hh).ofReal
      (physicalResolventKernel_decay lam h0 hpi).1.ofReal
      (positiveResolventCandidate_fourier_integrable lam h0 hh)
      (fun p => (physicalResolventKernel_fourier_eq_positiveCandidate lam h0 hh p).symm)
  ext u
  have hu := congrArg (fun f : ℝ → ℂ => (f u).re) he
  exact hu.symm

/-- Positivity of the actual resolvent kernel in the positive-K regime. -/
theorem physicalResolventKernel_nonneg_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (u : ℝ) :
    0 ≤ physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) u := by
  rw [physicalResolventKernel_eq_positiveCandidate lam h0 hh]
  change 0 ≤ ∫ t : ℝ,positiveDressingKernel lam t*
    fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) (u-t)
  apply integral_nonneg
  intro t
  apply mul_nonneg (positiveDressingKernel_nonneg lam h0 hh t)
  rw [fullLineDensityFunction_eq_explicitDensityProfile]
  unfold explicitDensityProfile
  positivity

/-- The actual positive resolvent mass in the manuscript normalization. -/
theorem integral_physicalResolventKernel_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    (∫ u : ℝ,physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) u)=
      (1-2*lam/Real.pi)/(1+(1-2*lam/Real.pi)) := by
  rw [physicalResolventKernel_eq_positiveCandidate lam h0 hh]
  change (∫ u : ℝ,∫ t : ℝ,positiveDressingKernel lam t*
    fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) (u-t))=_
  have he : (∫ u : ℝ,∫ t : ℝ,positiveDressingKernel lam t*
      fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) (u-t))=
      (∫ t : ℝ,positiveDressingKernel lam t)*(∫ u : ℝ,fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) u) :=
    integral_convolution (ContinuousLinearMap.mul ℝ ℝ)
      (positiveDressingKernel_integrable lam h0 hh)
      (fullLineDensityFunction_integrable lam h0 (by linarith [Real.pi_pos]))
  rw [he,integral_positiveDressingKernel lam h0 hh,integral_fullLineDensityFunction]
  have hd : 1+(1-2*lam/Real.pi)=(2*(Real.pi-lam))/Real.pi := by
    field_simp [Real.pi_ne_zero]
    <;> ring
  have hn : 1-2*lam/Real.pi=(Real.pi-2*lam)/Real.pi := by
    field_simp [Real.pi_ne_zero]
  rw [hd,hn,div_div_div_cancel_right₀ Real.pi_ne_zero,mul_one_div,div_div,
    mul_comm (Real.pi-lam) 2]

/-- The actual L1 mass of the positive resolvent is h/(1+h), not merely
an upper bound for a formal multiplier. -/
theorem physicalResolventKernel_L1_mass_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    kernelL1Mass (fun u => physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) u)=
      kernelL1Mass (kernelK lam)/(1+kernelL1Mass (kernelK lam)) := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have he : kernelL1Mass (fun u => physicalResolventKernel lam h0 hpi u)=
      ∫ u : ℝ,physicalResolventKernel lam h0 hpi u := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun u => abs_of_nonneg (physicalResolventKernel_nonneg_positiveK lam h0 hh u))
  rw [he,integral_physicalResolventKernel_positiveK lam h0 hh]
  have hk : kernelL1Mass (kernelK lam)=1-2*lam/Real.pi := by
    change (∫ u : ℝ,|kernelK lam u|)=_
    rw [integral_abs_kernelK lam h0 hpi]
    rw [abs_of_nonneg]
    apply sub_nonneg.mpr
    apply (div_le_one Real.pi_pos).mpr
    linarith
  rw [hk]

/-- The strict contraction threshold used by the exterior positive
Neumann construction. -/
theorem physicalResolventKernel_L1_mass_lt_half_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    kernelL1Mass (fun u => physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) u)<1/2 := by
  rw [physicalResolventKernel_L1_mass_positiveK lam h0 hh]
  have hn := kernelL1Mass_nonneg (kernelK lam)
  have hl := kernelK_L1_mass_lt_one lam h0 (show lam < Real.pi by linarith [Real.pi_pos])
  change kernelL1Mass (kernelK lam) < 1 at hl
  apply (div_lt_iff₀ (show 0 < 1+kernelL1Mass (kernelK lam) by linarith)).mpr
  linarith

end
end SixVertex
