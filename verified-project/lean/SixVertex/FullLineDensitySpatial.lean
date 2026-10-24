import SixVertex.ExplicitDensityIdentification

namespace SixVertex
noncomputable section

private theorem cosh_spatial_upper (x y : ℝ) :
    Real.cosh x ≤ Real.exp |y-x| *Real.cosh y := by
  have hp : Real.exp x ≤ Real.exp |y-x| *Real.exp y := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [neg_abs_le (y-x)]
  have hn : Real.exp (-x) ≤ Real.exp |y-x| *Real.exp (-y) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    linarith [le_abs_self (y-x)]
  rw [Real.cosh_eq,Real.cosh_eq]
  nlinarith only [hp,hn]

/-- The actual identified density has a uniform spatial exponential
comparison with the exact inverse length scale pi/lambda. -/
theorem fullLineDensityFunction_spatial_comparison_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (u v : ℝ) :
    Real.exp (-((Real.pi/lam)*|v-u|))*fullLineDensityFunction lam h0 hpi u ≤
        fullLineDensityFunction lam h0 hpi v ∧
      fullLineDensityFunction lam h0 hpi v ≤
        Real.exp ((Real.pi/lam)*|v-u|)*fullLineDensityFunction lam h0 hpi u := by
  let eta : ℝ := lam/Real.pi
  have heta : 0 < eta := div_pos h0 Real.pi_pos
  have hupper (x y : ℝ) : fullLineDensityFunction lam h0 hpi y ≤
      Real.exp ((Real.pi/lam)*|y-x|)*fullLineDensityFunction lam h0 hpi x := by
    rw [fullLineDensityFunction_eq_explicitDensityProfile,fullLineDensityFunction_eq_explicitDensityProfile]
    unfold explicitDensityProfile
    change 1/(2*lam*Real.cosh (y/eta)) ≤ Real.exp ((Real.pi/lam)*|y-x|)*(1/(2*lam*Real.cosh (x/eta)))
    rw [mul_one_div]
    apply (div_le_div_iff₀ (mul_pos (mul_pos (by norm_num) h0) (Real.cosh_pos _))
      (mul_pos (mul_pos (by norm_num) h0) (Real.cosh_pos _))).mpr
    have hd : |y/eta-x/eta|=(Real.pi/lam)*|y-x| := by
      rw [← sub_div,abs_div,abs_of_pos heta]
      dsimp [eta]
      field_simp [h0.ne',Real.pi_ne_zero]
    have hc := cosh_spatial_upper (x/eta) (y/eta)
    rw [hd] at hc
    have hm := mul_le_mul_of_nonneg_left hc (show 0 ≤ 2*lam by positivity)
    nlinarith only [hm]
  refine ⟨?_,hupper u v⟩
  have hu := hupper v u
  rw [abs_sub_comm u v] at hu
  have hm := mul_le_mul_of_nonneg_left hu (Real.exp_pos (-((Real.pi/lam)*|v-u|))).le
  have he : Real.exp (-((Real.pi/lam)*|v-u|))*Real.exp ((Real.pi/lam)*|v-u|)=1 := by
    rw [← Real.exp_add]
    simp
  rw [← mul_assoc,he,one_mul] at hm
  exact hm

end
end SixVertex
