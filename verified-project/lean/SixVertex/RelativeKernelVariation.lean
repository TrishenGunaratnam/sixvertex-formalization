import SixVertex.FiniteIntervalRegularity
import SixVertex.FreeFermionRoots

namespace SixVertex
noncomputable section
open Set

/-- A positive differentiable function with bounded relative derivative
has a two-sided multiplicative comparison, without a global lower bound. -/
theorem positive_function_exponential_comparison (f f' : ℝ → ℝ) (C : ℝ)
    (hp : ∀ x, 0 < f x) (hd : ∀ x, HasDerivAt f (f' x) x)
    (hb : ∀ x, |f' x| ≤ C*f x) (u v : ℝ) :
    Real.exp (-(C*|v-u|))*f u ≤ f v ∧ f v ≤ Real.exp (C*|v-u|)*f u := by
  have hl (x : ℝ) : HasDerivAt (fun y => Real.log (f y)) (f' x/f x) x :=
    (hd x).log (hp x).ne'
  have hbn (x : ℝ) : ‖f' x/f x‖ ≤ C := by
    rw [Real.norm_eq_abs,abs_div,abs_of_pos (hp x)]
    exact (div_le_iff₀ (hp x)).mpr (hb x)
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (univ : Set ℝ)) => (hl x).hasDerivWithinAt)
    (fun x (_ : x ∈ (univ : Set ℝ)) => hbn x)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ u) (mem_univ v)
  have hh := abs_le.mp (by simpa only [Real.norm_eq_abs] using h :
    |Real.log (f v)-Real.log (f u)| ≤ C*|v-u|)
  have hlo := Real.exp_le_exp.mpr hh.1
  have hhi := Real.exp_le_exp.mpr hh.2
  rw [Real.exp_sub,Real.exp_log (hp v),Real.exp_log (hp u)] at hlo hhi
  exact ⟨(le_div_iff₀ (hp u)).mp hlo,(div_le_iff₀ (hp u)).mp hhi⟩

theorem kernelS_exponential_comparison (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u v : ℝ) :
    Real.exp (-(kernelLogConstant lam*|v-u|))*kernelS lam u ≤ kernelS lam v ∧
    kernelS lam v ≤ Real.exp (kernelLogConstant lam*|v-u|)*kernelS lam u := by
  apply positive_function_exponential_comparison (kernelS lam) (kernelSPrime lam) (kernelLogConstant lam)
    (fun x => kernelS_pos lam x h0 hpi) (fun x => hasDerivAt_kernelS lam x h0 hpi)
  intro x
  apply (kernelSPrime_relative_bound lam x h0 hpi).trans
  apply mul_le_mul_of_nonneg_right _ (kernelS_pos lam x h0 hpi).le
  unfold kernelLogConstant
  have hh : 0 ≤ 2/(Real.sin lam)^2 := by positivity
  linarith

/-- The zero kernel at the free point is included in this comparison. -/
theorem negative_kernelK_exponential_comparison (lam : ℝ) (hhalf : Real.pi/2 ≤ lam)
    (hpi : lam < Real.pi) (u v : ℝ) :
    Real.exp (-(kernelLogConstant lam*|v-u|))*(-kernelK lam u) ≤ -kernelK lam v ∧
    -kernelK lam v ≤ Real.exp (kernelLogConstant lam*|v-u|)*(-kernelK lam u) := by
  rcases hhalf.eq_or_lt with heq | hstrict
  · rw [← heq]
    simp only [kernelK_freeFermion,neg_zero,mul_zero,le_refl,and_self]
  · have h0 : 0 < lam := by linarith [Real.pi_pos]
    apply positive_function_exponential_comparison (fun x => -kernelK lam x) (fun x => -kernelKPrime lam x)
      (kernelLogConstant lam) (fun x => neg_pos.mpr (kernelK_strict_neg lam x hstrict hpi))
      (fun x => (hasDerivAt_kernelK lam x h0 hpi).neg)
    intro x
    rw [abs_neg]
    have hh := kernelKPrime_relative_bound lam x h0 hpi
    rw [abs_of_neg (kernelK_strict_neg lam x hstrict hpi)] at hh
    apply hh.trans
    apply mul_le_mul_of_nonneg_right _ (neg_pos.mpr (kernelK_strict_neg lam x hstrict hpi)).le
    unfold kernelLogConstant
    have hs : 0 ≤ 2/(Real.sin (lam/2))^2 := by positivity
    linarith

/-- Enlarge a known multiplicative comparison to a specified radius. -/
theorem exponential_comparison_of_distance_le (f : ℝ → ℝ) (C eps u v : ℝ)
    (hC : 0 ≤ C) (hf : 0 ≤ f u) (hd : |v-u| ≤ eps)
    (hcomp : Real.exp (-(C*|v-u|))*f u ≤ f v ∧ f v ≤ Real.exp (C*|v-u|)*f u) :
    Real.exp (-(C*eps))*f u ≤ f v ∧ f v ≤ Real.exp (C*eps)*f u := by
  constructor
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by nlinarith)) hf).trans hcomp.1
  · exact hcomp.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hd hC)) hf)

end
end SixVertex
