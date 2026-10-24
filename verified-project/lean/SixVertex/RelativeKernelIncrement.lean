import SixVertex.RelativeKernelVariation

namespace SixVertex
noncomputable section
open Set

/-- Relative variation of the actual kernel, with the free point included. -/
theorem kernelK_relative_increment_bound (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (eps u v : ℝ) (hd : |v-u| ≤ eps) :
    |kernelK lam v-kernelK lam u| ≤
      kernelLogConstant lam*Real.exp (kernelLogConstant lam*eps)*|kernelK lam u| *|v-u| := by
  let C := kernelLogConstant lam
  have hC : 0 ≤ C := kernelLogConstant_nonneg lam
  have hkC : 2/(Real.sin lam)^2 ≤ C := by
    dsimp [C,kernelLogConstant]
    have hh : 0 ≤ 2/(Real.sin (lam/2))^2 := by positivity
    linarith
  have hprime (x : ℝ) (hx : x ∈ uIcc u v) :
      ‖kernelKPrime lam x‖ ≤ C*Real.exp (C*eps)*|kernelK lam u| := by
    have hdist : |x-u| ≤ eps := (abs_sub_left_of_mem_uIcc hx).trans hd
    have hcomp := (exponential_comparison_of_distance_le (fun x => -kernelK lam x) C eps u x hC
      (neg_nonneg.mpr (kernelK_nonpos lam _ hhalf hpi)) hdist
      (negative_kernelK_exponential_comparison lam hhalf hpi u x)).2
    rw [Real.norm_eq_abs]
    calc
      _ ≤ C*|kernelK lam x| := (kernelKPrime_relative_bound lam x h0 hpi).trans
        (mul_le_mul_of_nonneg_right hkC (abs_nonneg _))
      _ ≤ C*(Real.exp (C*eps)*|kernelK lam u|) := by
        apply mul_le_mul_of_nonneg_left _ hC
        simpa only [abs_of_nonpos (kernelK_nonpos lam _ hhalf hpi)] using hcomp
      _ = _ := by ring
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ uIcc u v) => (hasDerivAt_kernelK lam x h0 hpi).hasDerivWithinAt)
    hprime (convex_uIcc u v) (left_mem_uIcc) (right_mem_uIcc)
  simpa only [Real.norm_eq_abs] using hh

end
end SixVertex
