import SixVertex.FiniteBetheKernels
import SixVertex.BetheVacuum

namespace SixVertex

/-- A real hyperbolic sine with an imaginary shift, in Cartesian coordinates. -/
theorem sinh_real_shift (u θ : ℝ) :
    Complex.sinh ((u : ℂ) + Complex.I*(θ : ℂ)) =
      ((Real.sinh u * Real.cos θ : ℝ) : ℂ) +
        ((Real.cosh u * Real.sin θ : ℝ) : ℂ) * Complex.I := by
  rw [mul_comm Complex.I, Complex.sinh_add, Complex.cosh_mul_I, Complex.sinh_mul_I]
  simp only [← Complex.ofReal_sinh, ← Complex.ofReal_cosh, ← Complex.ofReal_cos,
    ← Complex.ofReal_sin, Complex.ofReal_mul]
  ring

theorem sinh_real_shift_ne_zero (u θ : ℝ) (hθ : Real.sin θ ≠ 0) :
    Complex.sinh ((u : ℂ) + Complex.I*(θ : ℂ)) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  rw [sinh_real_shift] at hi
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    Complex.I_im, Complex.I_re, mul_one, mul_zero, zero_add, add_zero, Complex.zero_im] at hi
  exact (mul_ne_zero (Real.cosh_pos u).ne' hθ) hi

/-- Cayley's parametrization of a phase, with the arctan branch fixed on the real line. -/
theorem exp_arctan_cayley (r : ℝ) :
    Complex.exp (2 * (Real.arctan r : ℂ) * Complex.I) * (1-(r : ℂ)*Complex.I) =
      1+(r : ℂ)*Complex.I := by
  have hs : Real.sin (Real.arctan r) = r * Real.cos (Real.arctan r) := by
    have h := Real.tan_arctan r
    rw [Real.tan_eq_sin_div_cos] at h
    exact (div_eq_iff (Real.cos_arctan_pos r).ne').mp h
  have ht := Real.cos_sq_add_sin_sq (Real.arctan r)
  rw [Complex.exp_mul_I]
  rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  apply Complex.ext
  · simp only [Complex.mul_re, Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, Complex.sub_im, mul_zero, mul_one, zero_mul, add_zero, sub_zero, zero_sub,
      Real.cos_two_mul', Real.sin_two_mul]
    linear_combination ht - 2 * Real.sin (Real.arctan r) * hs
  · simp only [Complex.mul_im, Complex.add_re, Complex.sub_re, Complex.one_re,
      Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.sub_im, Complex.mul_re, mul_zero, mul_one, zero_mul,
      add_zero, sub_zero, zero_sub, Real.cos_two_mul', Real.sin_two_mul]
    linear_combination r * ht + 2 * Real.cos (Real.arctan r) * hs

/-- Exact phase of the shifted-sinh ratio, including its minus sign. -/
theorem exp_barePhase (θ u : ℝ) (hθ : Real.sin θ ≠ 0) :
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (barePhase θ u : ℂ)) =
      -Complex.sinh ((u : ℂ)-Complex.I*θ) / Complex.sinh ((u : ℂ)+Complex.I*θ) := by
  let r := (Real.cos θ / Real.sin θ) * (Real.sinh u / Real.cosh u)
  have h := exp_arctan_cayley r
  have hr : (r : ℂ) * (Real.cosh u : ℂ) * (Real.sin θ : ℂ) =
      (Real.sinh u : ℂ) * (Real.cos θ : ℂ) := by
    have hrR : r * Real.cosh u * Real.sin θ = Real.sinh u * Real.cos θ := by
      dsimp [r]
      field_simp [(Real.cosh_pos u).ne', hθ]
    simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal hrR
  have he : 2 * (Real.pi : ℂ) * Complex.I * (barePhase θ u : ℂ) =
      2 * (Real.arctan r : ℂ) * Complex.I := by
    unfold barePhase
    push_cast
    dsimp [r]
    field_simp
  rw [he]
  apply (eq_div_iff (sinh_real_shift_ne_zero u θ hθ)).2
  have hm : (u : ℂ) - Complex.I*θ = (u : ℂ) + Complex.I*(-θ : ℝ) := by push_cast; ring
  rw [hm, sinh_real_shift, sinh_real_shift]
  simp only [Real.cos_neg, Real.sin_neg, mul_neg, Complex.ofReal_neg, Complex.ofReal_mul]
  have hI := congrArg (fun z : ℂ => (Complex.I * (Real.cosh u : ℂ) * (Real.sin θ : ℂ)) * z) h
  ring_nf at hI
  simp only [Complex.I_sq] at hI
  rw [show Complex.I * (Real.arctan r : ℂ) * 2 = 2 * (Real.arctan r : ℂ) * Complex.I by ring] at hI
  linear_combination hI - (Complex.exp (2 * (Real.arctan r : ℂ) * Complex.I) + 1) * hr

end SixVertex
