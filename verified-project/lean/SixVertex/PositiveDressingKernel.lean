import SixVertex.PhysicalKernelFourier
import SixVertex.PaperFourier

namespace SixVertex
noncomputable section
open MeasureTheory Filter

private theorem angular_scaled_transform (f : ℝ → ℂ) (c : ℝ) (hc : 0 < c) (p : ℝ) :
    paperFourier (fun u => (c : ℂ)*f (c*u)) p=paperFourier f (p/c) := by
  let g : ℝ → ℂ := fun v => Complex.exp (-Complex.I*((p/c : ℝ) : ℂ)*(v : ℂ))*f v
  have he (u : ℝ) : Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*((c : ℂ)*f (c*u))=
      (c : ℂ)*g (c*u) := by
    have hp : -Complex.I*((p/c : ℝ) : ℂ)*((c*u : ℝ) : ℂ)=
        -Complex.I*(p : ℂ)*(u : ℂ) := by push_cast; field_simp [Complex.ofReal_ne_zero.mpr hc.ne']
    dsimp [g]
    rw [hp]
    ring
  unfold paperFourier
  calc
    _ = ∫ u : ℝ,(c : ℂ)*g (c*u) := integral_congr_ae (Eventually.of_forall he)
    _ = (c : ℂ)*(|c⁻¹| • ∫ v : ℝ,g v) := by
      rw [integral_const_mul,Measure.integral_comp_mul_left g c]
    _ = _ := by
      rw [abs_of_pos (inv_pos.mpr hc)]
      change (c : ℂ)*(((c⁻¹ : ℝ) : ℂ)*(∫ v : ℝ,g v))=∫ v : ℝ,g v
      rw [Complex.ofReal_inv,← mul_assoc,mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hc.ne'),one_mul]

/-- The actual auxiliary kernel displayed in the positive-kernel
finite-interval argument of Lemma 3.1. -/
def positiveDressingKernel (lam u : ℝ) : ℝ :=
  Real.sin (Real.pi*lam/(Real.pi-lam))/((Real.pi-lam)*
    (Real.cosh (2*Real.pi*u/(Real.pi-lam))-Real.cos (Real.pi*lam/(Real.pi-lam))))

/-- Exact rescaling of the physical bare kernel, not an assumed transform. -/
theorem positiveDressingKernel_rescaling (lam : ℝ) (hpi : lam ≠ Real.pi) (u : ℝ) :
    positiveDressingKernel lam u=(Real.pi/(Real.pi-lam))*
      kernelK (Real.pi*lam/(2*(Real.pi-lam))) ((Real.pi/(Real.pi-lam))*u) := by
  have hl : Real.pi-lam ≠ 0 := sub_ne_zero.mpr (Ne.symm hpi)
  unfold positiveDressingKernel kernelK phaseDensity
  rw [show 2*(Real.pi*lam/(2*(Real.pi-lam)))=Real.pi*lam/(Real.pi-lam) by field_simp [hl],
    show 2*(Real.pi/(Real.pi-lam)*u)=2*Real.pi*u/(Real.pi-lam) by ring]
  by_cases hd : Real.cosh (2*Real.pi*u/(Real.pi-lam))-Real.cos (Real.pi*lam/(Real.pi-lam))=0
  · simp [hd]
  · field_simp [hl,hd,Real.pi_ne_zero]

private theorem positive_dressing_parameters (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    0 < Real.pi/(Real.pi-lam) ∧
    0 < Real.pi*lam/(2*(Real.pi-lam)) ∧
    Real.pi*lam/(2*(Real.pi-lam)) < Real.pi/2 := by
  have hl : 0 < Real.pi-lam := by linarith [Real.pi_pos]
  refine ⟨div_pos Real.pi_pos hl,div_pos (mul_pos Real.pi_pos h0) (by positivity),?_⟩
  apply (div_lt_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hl)).mpr
  have he := mul_lt_mul_of_pos_left (show lam < Real.pi-lam by linarith) Real.pi_pos
  nlinarith only [he]

/-- The displayed J kernel is nonnegative throughout the positive-K range. -/
theorem positiveDressingKernel_nonneg (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (u : ℝ) : 0 ≤ positiveDressingKernel lam u := by
  obtain ⟨hc,ha,ha'⟩ := positive_dressing_parameters lam h0 hh
  rw [positiveDressingKernel_rescaling lam (by linarith [Real.pi_pos]) u]
  exact mul_nonneg hc.le (kernelK_nonneg _ _ ha ha'.le)

/-- Absolute integrability of the actual displayed J kernel. -/
theorem positiveDressingKernel_integrable (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) : Integrable (positiveDressingKernel lam) := by
  obtain ⟨hc,ha,ha'⟩ := positive_dressing_parameters lam h0 hh
  have hi := ((kernelK_integrable _ ha (by linarith [Real.pi_pos])).comp_mul_left' hc.ne').const_mul
    (Real.pi/(Real.pi-lam))
  apply hi.congr
  filter_upwards with u
  exact (positiveDressingKernel_rescaling lam (by linarith [Real.pi_pos]) u).symm

/-- The actual mass of the auxiliary positive kernel, with no Fourier
interpretation needed at frequency zero. -/
theorem integral_positiveDressingKernel (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    (∫ u : ℝ,positiveDressingKernel lam u)=(Real.pi-2*lam)/(Real.pi-lam) := by
  obtain ⟨hc,ha,ha'⟩ := positive_dressing_parameters lam h0 hh
  have he : positiveDressingKernel lam=(fun u => (Real.pi/(Real.pi-lam))*
      kernelK (Real.pi*lam/(2*(Real.pi-lam))) ((Real.pi/(Real.pi-lam))*u)) :=
    funext (positiveDressingKernel_rescaling lam (by linarith [Real.pi_pos]))
  rw [he,integral_const_mul,Measure.integral_comp_mul_left,
    abs_of_pos (inv_pos.mpr hc)]
  change (Real.pi/(Real.pi-lam))*((Real.pi/(Real.pi-lam))⁻¹*
    (∫ u : ℝ,kernelK (Real.pi*lam/(2*(Real.pi-lam))) u))=_
  rw [← mul_assoc,mul_inv_cancel₀ hc.ne',one_mul,
    integral_kernelK _ ha (by linarith [Real.pi_pos])]
  field_simp [Real.pi_ne_zero,show Real.pi-lam ≠ 0 by linarith [Real.pi_pos]]
  <;> ring

/-- The auxiliary positive kernel has the exact real-frequency transform
used by the paper's dressed-resolvent factorization. -/
theorem positiveDressingKernel_fourier_nonzero (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (p : ℝ) (hp : p ≠ 0) :
    paperFourier (fun u => (positiveDressingKernel lam u : ℂ)) p=
      ((Real.sinh ((Real.pi-2*lam)*p/2)/Real.sinh ((Real.pi-lam)*p/2) : ℝ) : ℂ) := by
  obtain ⟨hc,ha,ha'⟩ := positive_dressing_parameters lam h0 hh
  have he : (fun u => (positiveDressingKernel lam u : ℂ))=
      (fun u => ((Real.pi/(Real.pi-lam) : ℝ) : ℂ)*
        (kernelK (Real.pi*lam/(2*(Real.pi-lam))) ((Real.pi/(Real.pi-lam))*u) : ℂ)) := by
    funext u
    rw [positiveDressingKernel_rescaling lam (by linarith [Real.pi_pos]) u,Complex.ofReal_mul]
  rw [he,angular_scaled_transform (fun u : ℝ => (kernelK (Real.pi*lam/(2*(Real.pi-lam))) u : ℂ)) _ hc p]
  change (∫ u : ℝ,Complex.exp (-Complex.I*((p/(Real.pi/(Real.pi-lam)) : ℝ) : ℂ)*(u : ℂ))*
    (kernelK (Real.pi*lam/(2*(Real.pi-lam))) u : ℂ))=_
  rw [kernelK_fourier_nonzero _ ha (by linarith [Real.pi_pos]) _ (div_ne_zero hp hc.ne')]
  have h1 : (Real.pi-2*(Real.pi*lam/(2*(Real.pi-lam))))*(p/(Real.pi/(Real.pi-lam)))/2=
      (Real.pi-2*lam)*p/2 := by
    field_simp [Real.pi_ne_zero,show Real.pi-lam ≠ 0 by linarith [Real.pi_pos]]
    <;> ring
  have h2 : Real.pi*(p/(Real.pi/(Real.pi-lam)))/2=(Real.pi-lam)*p/2 := by
    field_simp [Real.pi_ne_zero,show Real.pi-lam ≠ 0 by linarith [Real.pi_pos]]
  rw [h1,h2]

end
end SixVertex
