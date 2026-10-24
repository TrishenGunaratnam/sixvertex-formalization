import SixVertex.WeightedKernel

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem cosh_le_exp_abs_real (u : ℝ) : Real.cosh u ≤ Real.exp |u| := by
  rw [Real.cosh_eq]
  have hp := Real.exp_le_exp.mpr (le_abs_self u)
  have hm := Real.exp_le_exp.mpr (neg_le_abs u)
  linarith

theorem phase_denominator_exp_upper (theta u : ℝ) :
    Real.cosh (2*u)-Real.cos (2*theta) ≤ 2*Real.exp (2*|u|) := by
  have hc := cosh_le_exp_abs_real (2*u)
  have he : |2*u|=2*|u| := by rw [abs_mul,abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  rw [he] at hc
  have hp : 1 ≤ Real.exp (2*|u|) := Real.one_le_exp_iff.mpr (by positivity)
  linarith [Real.neg_one_le_cos (2*theta)]

/-- A lower exponential envelope for the absolute physical kernel.
It is nontrivial away from the free-fermion zero kernel. -/
theorem kernelK_exponential_lower_bound (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    (|Real.sin (2*lam)|/(2*Real.pi))*Real.exp (-2*|u|) ≤ |kernelK lam u| := by
  have hd := phase_denominator_pos lam u (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hup := phase_denominator_exp_upper lam u
  have h := div_le_div_of_nonneg_left (abs_nonneg (Real.sin (2*lam)))
    (mul_pos Real.pi_pos hd) (mul_le_mul_of_nonneg_left hup Real.pi_pos.le)
  have he : |Real.sin (2*lam)|/(Real.pi*(2*Real.exp (2*|u|)))=
      (|Real.sin (2*lam)|/(2*Real.pi))*Real.exp (-2*|u|) := by
    rw [show -2*|u|= -(2*|u|) by ring,Real.exp_neg]
    field_simp
  rw [he] at h
  change _ ≤ |Real.sin (2*lam)/(Real.pi*(Real.cosh (2*u)-Real.cos (2*lam)))|
  rw [abs_div,abs_of_pos (mul_pos Real.pi_pos hd)]
  exact h

def kernelTail (q : ℝ → ℝ) (u : ℝ) : ℝ := ∫ v in Ioi u, q v

theorem kernelTail_nonneg (q : ℝ → ℝ) (hq : ∀ v, 0 ≤ q v) (u : ℝ) : 0 ≤ kernelTail q u :=
  integral_nonneg (fun v => hq v)

end
end SixVertex
