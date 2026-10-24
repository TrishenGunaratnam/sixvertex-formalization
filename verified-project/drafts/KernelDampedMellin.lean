import SixVertex.UnitQuadraticMellin
import SixVertex.DampedFourierContinuity

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- The actual exponential Jacobian relates the physical kernel to the
quadratic Mellin integrand,with the exact damping and Fourier factors. -/
theorem kernelK_mellin_exponential_jacobian (lam eps p v : ℝ) :
    (Real.exp v : ℝ) • ((-(Real.sin (2*lam-Real.pi) : ℂ)/(Real.pi : ℂ))*
      (((Real.exp v : ℝ) : ℂ)^((1-(eps : ℂ)-Complex.I*(p : ℂ)/2)-1)/
        (((Real.exp v : ℝ) : ℂ)^2+2*(Real.cos (2*lam-Real.pi) : ℂ)*((Real.exp v : ℝ) : ℂ)+1)))=
    (1/2 : ℂ)*(Complex.exp (-Complex.I*(p : ℂ)*(v/2 : ℝ))*
      ((Real.exp (-eps*v)*kernelK lam (v/2) : ℝ) : ℂ)) := by
  let alpha : ℝ := 2*lam-Real.pi
  let E : ℂ := ((Real.exp v : ℝ) : ℂ)
  have hE : E ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos v).ne'
  have hcosh : (Real.cosh v : ℂ)=(E+E⁻¹)/2 := by
    change (Real.cosh v : ℂ)=(((Real.exp v : ℝ) : ℂ)+(((Real.exp v : ℝ) : ℂ))⁻¹)/2
    rw [Real.cosh_eq,Real.exp_neg]
    push_cast
    rfl
  have hQ : E^2+2*(Real.cos alpha : ℂ)*E+1=
      2*E*((Real.cosh v : ℂ)+(Real.cos alpha : ℂ)) := by
    rw [hcosh]
    field_simp [hE]
    ring
  have hlog : Complex.log E=(v : ℂ) := by
    dsimp [E]
    rw [← Complex.ofReal_log (Real.exp_pos v).le,Real.log_exp]
  have hpow : E^((1-(eps : ℂ)-Complex.I*(p : ℂ)/2)-1)=
      Complex.exp (-Complex.I*(p : ℂ)*(v/2 : ℝ))*((Real.exp (-eps*v) : ℝ) : ℂ) := by
    rw [Complex.cpow_def_of_ne_zero hE,hlog,Complex.ofReal_exp,← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hs : Real.sin alpha= -Real.sin (2*lam) := by dsimp [alpha]; rw [Real.sin_sub]; simp
  have hc : Real.cos alpha= -Real.cos (2*lam) := by dsimp [alpha]; rw [Real.cos_sub]; simp
  have hk : (kernelK lam (v/2) : ℂ)=
      -(Real.sin alpha : ℂ)/((Real.pi : ℂ)*((Real.cosh v : ℂ)+(Real.cos alpha : ℂ))) := by
    unfold kernelK phaseDensity
    rw [hs,hc,show 2*(v/2)=v by ring]
    push_cast
    simp only [neg_neg,sub_eq_add_neg]
  change E*((-(Real.sin alpha : ℂ)/(Real.pi : ℂ))*
      (E^((1-(eps : ℂ)-Complex.I*(p : ℂ)/2)-1)/(E^2+2*(Real.cos alpha : ℂ)*E+1)))=_
  simp only [Complex.ofReal_mul]
  rw [hpow,hQ,hk]
  by_cases hd : (Real.cosh v : ℂ)+(Real.cos alpha : ℂ)=0
  · simp only [hd,mul_zero,div_zero,zero_mul]
  · field_simp [hE,Complex.ofReal_ne_zero.mpr Real.pi_ne_zero,hd] <;> ring

/-- The actual physical kernel Fourier integral with damping is evaluated
by the proved quadratic Mellin formula in its genuine convergence strip. -/
theorem integral_damped_kernelK_mellin (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (eps : ℝ) (he0 : 0 < eps) (he1 : eps < 1) (p : ℝ) :
    (∫ u : ℝ, Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*
      ((Real.exp (-2*eps*u)*kernelK lam u : ℝ) : ℂ))=
      Complex.sin (((2*lam-Real.pi : ℝ) : ℂ)*(- (eps : ℂ)-Complex.I*(p : ℂ)/2))/
        Complex.sin ((Real.pi : ℂ)*(1-(eps : ℂ)-Complex.I*(p : ℂ)/2)) := by
  let alpha : ℝ := 2*lam-Real.pi
  let z : ℂ := 1-(eps : ℂ)-Complex.I*(p : ℂ)/2
  let f : ℝ → ℂ := fun u => Complex.exp (-Complex.I*(p : ℂ)*(u : ℂ))*
    ((Real.exp (-2*eps*u)*kernelK lam u : ℝ) : ℂ)
  have hz : z.re=1-eps := by norm_num [z,Complex.mul_re,Complex.mul_im,Complex.div_re]
  have hm := unit_quadratic_mellin_integral alpha (by dsimp [alpha]; linarith)
    (by dsimp [alpha]; linarith) z (by rw [hz]; linarith) (by rw [hz]; linarith)
  have he : z-1= -(eps : ℂ)-Complex.I*(p : ℂ)/2 := by dsimp [z]; ring
  change (∫ u : ℝ, f u)=_
  calc
    _ = (1/2 : ℂ)*(∫ v : ℝ, f (v/2)) := by
      rw [Measure.integral_comp_div f (2 : ℝ),abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      change (∫ u : ℝ, f u)=(1/2 : ℂ)*((2 : ℂ)*(∫ u : ℝ, f u))
      ring
    _ = ∫ v : ℝ, (Real.exp v : ℝ) • ((-(Real.sin alpha : ℂ)/(Real.pi : ℂ))*
        (((Real.exp v : ℝ) : ℂ)^(z-1)/
          (((Real.exp v : ℝ) : ℂ)^2+2*(Real.cos alpha : ℂ)*((Real.exp v : ℝ) : ℂ)+1))) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => by
        have hj := kernelK_mellin_exponential_jacobian lam eps p v
        change (1/2 : ℂ)*f (v/2)=_
        have hf : f (v/2)=Complex.exp (-Complex.I*(p : ℂ)*(v/2 : ℝ))*((Real.exp (-eps*v)*kernelK lam (v/2) : ℝ) : ℂ) := by
          dsimp [f]
          rw [show -2*eps*(v/2)= -eps*v by ring]
        rw [hf]
        exact hj.symm)
    _ = _ := by
      rw [integral_comp_exp (fun t : ℝ => (-(Real.sin alpha : ℂ)/(Real.pi : ℂ))*((t : ℂ)^(z-1)/((t : ℂ)^2+2*(Real.cos alpha : ℂ)*(t : ℂ)+1))),hm,he]


end
end SixVertex
