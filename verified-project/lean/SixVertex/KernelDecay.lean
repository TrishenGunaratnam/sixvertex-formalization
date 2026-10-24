import SixVertex.GlobalRootFamily

namespace SixVertex

theorem exp_abs_le_two_cosh (u : ℝ) : Real.exp |u| ≤ 2*Real.cosh u := by
  calc
    _ ≤ Real.exp |u|+Real.exp (-|u|) := by linarith [Real.exp_pos (-|u|)]
    _ = 2*Real.cosh |u| := by rw [Real.cosh_eq]; ring
    _ = _ := by rw [Real.cosh_abs]

/-- A positive quadratic lower bound on the hyperbolic kernel denominator. -/
theorem phase_denominator_cosh_bound (lam u : ℝ) :
    2*(Real.sin lam)^2*(Real.cosh u)^2 ≤ Real.cosh (2*u)-Real.cos (2*lam) := by
  rw [Real.cosh_two_mul,Real.cos_two_mul_eq_one_sub,Real.cosh_sq]
  have htrig := Real.sin_sq_add_cos_sq lam
  have hnonneg := mul_nonneg (sq_nonneg (Real.cos lam)) (sq_nonneg (Real.sinh u))
  nlinarith

/-- Explicit exponential decay for the full physical kernel, including the
zero kernel at the free point. The constant depends only on lambda. -/
theorem kernelK_exponential_bound (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    |kernelK lam u| ≤ (2/(Real.pi*(Real.sin lam)^2))*Real.exp (-2*|u|) := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hs2 : 0 < (Real.sin lam)^2 := sq_pos_of_ne_zero hs
  have hd := phase_denominator_pos lam u hs
  have hc := exp_abs_le_two_cosh u
  have hcp := Real.cosh_pos u
  have he := Real.exp_pos |u|
  have hcsq : (Real.exp |u|)^2 ≤ 4*(Real.cosh u)^2 := by nlinarith
  have hdc := phase_denominator_cosh_bound lam u
  have hmul := mul_nonneg hs2.le (sub_nonneg.mpr hcsq)
  have hde : (Real.sin lam)^2*Real.exp (2*|u|) ≤
      2*(Real.cosh (2*u)-Real.cos (2*lam)) := by
    rw [show 2*|u| = |u|+|u| by ring,Real.exp_add]
    nlinarith
  have hinv : Real.exp (2*|u|)*Real.exp (-2*|u|) = 1 := by
    rw [← Real.exp_add,show 2*|u|+(-2*|u|) = 0 by ring,Real.exp_zero]
  have hmult := mul_le_mul_of_nonneg_right hde (Real.exp_pos (-2*|u|)).le
  have hbound : (Real.sin lam)^2 ≤
      2*(Real.cosh (2*u)-Real.cos (2*lam))*Real.exp (-2*|u|) := by
    calc
      _ = ((Real.sin lam)^2*Real.exp (2*|u|))*Real.exp (-2*|u|) := by rw [mul_assoc,hinv,mul_one]
      _ ≤ _ := hmult
  unfold kernelK phaseDensity
  rw [abs_div,abs_of_pos (mul_pos Real.pi_pos hd)]
  apply (div_le_iff₀ (mul_pos Real.pi_pos hd)).mpr
  calc
    |Real.sin (2*lam)| ≤ 1 := Real.abs_sin_le_one _
    _ ≤ (2/(Real.pi*(Real.sin lam)^2))*Real.exp (-2*|u|) *
        (Real.pi*(Real.cosh (2*u)-Real.cos (2*lam))) := by
      have heq : (2/(Real.pi*(Real.sin lam)^2))*Real.exp (-2*|u|) *
          (Real.pi*(Real.cosh (2*u)-Real.cos (2*lam))) =
          (2*(Real.cosh (2*u)-Real.cos (2*lam))*Real.exp (-2*|u|))/(Real.sin lam)^2 := by
        field_simp [Real.pi_ne_zero,hs2.ne']
      rw [heq]
      apply (le_div_iff₀ hs2).mpr
      simpa only [one_mul] using hbound

end SixVertex
