import SixVertex.PositiveWindowComparison
import SixVertex.ExitKernelComparison

namespace SixVertex
noncomputable section
open MeasureTheory Set

/-- The full density/H_Q comparison clause of Lemma 3.1, for every
physical parameter and with constants chosen before all cutoffs and points. -/
theorem exists_uniform_finiteInterval_comparison (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ Q : ℝ,0 ≤ Q → ∀ u : ℝ,|u| ≤ Q →
      c*fullLineDensityFunction lam h0 hpi u ≤ finiteIntervalDensity lam h0 hpi Q u ∧
      finiteIntervalDensity lam h0 hpi Q u ≤ C*fullLineDensityFunction lam h0 hpi u ∧
      c ≤ finiteIntervalOne lam h0 hpi Q u ∧ finiteIntervalOne lam h0 hpi Q u ≤ C := by
  let h : ℝ := kernelL1Mass (kernelK lam)
  have hh0 : 0 ≤ h := kernelL1Mass_nonneg _
  have hh1 : h < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  have hm : h=|1-2*lam/Real.pi| := integral_abs_kernelK lam h0 hpi
  by_cases hhalf : Real.pi/2 ≤ lam
  · have hd : 0 < 1-h := sub_pos.mpr hh1
    have hC : 1 ≤ (1-h)⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hd).mpr
      linarith
    refine ⟨1-h,(1-h)⁻¹,hd,inv_pos.mpr hd,?_⟩
    intro Q hQ u hu
    have hr : 0 ≤ fullLineDensityFunction lam h0 hpi u := (fullLineDensityFunction_pos_all lam h0 hpi u).le
    have hH := finiteIntervalOne_bounds lam h0 hhalf hpi Q u
    rw [← hm] at hH
    refine ⟨finiteIntervalDensity_lower_comparison lam h0 hhalf hpi Q hQ u (abs_le.mp hu),?_,?_,hH.2⟩
    · exact (finiteIntervalDensity_le_fullLineDensity lam h0 hhalf hpi Q u).trans
        (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hC hr)
    · exact (show 1-h ≤ 1 by linarith).trans hH.1
  · have hp : lam < Real.pi/2 := lt_of_not_ge hhalf
    let tau := kernelL1Mass (fun v => physicalResolventKernel lam h0 hpi v)
    have ht0 : 0 ≤ tau := kernelL1Mass_nonneg _
    have ht1 : tau < 1 := (physicalResolventKernel_L1_mass_lt_half_positiveK lam h0 hp).trans (by norm_num)
    have hd : 0 < 1-tau := sub_pos.mpr ht1
    have hC : 1 ≤ (1-tau)⁻¹ := by
      rw [← one_div]
      apply (le_div_iff₀ hd).mpr
      linarith
    have hc : 0 < 1/(1+h) := one_div_pos.mpr (by linarith)
    have hc1 : 1/(1+h) ≤ 1 := (div_le_one (by linarith : 0 < 1+h)).mpr (by linarith)
    refine ⟨1/(1+h),(1-tau)⁻¹,hc,inv_pos.mpr hd,?_⟩
    intro Q hQ u hu
    have hr : 0 ≤ fullLineDensityFunction lam h0 hpi u := (fullLineDensityFunction_pos_all lam h0 hpi u).le
    have hR := finiteIntervalDensity_comparison_positiveK lam h0 hp Q hQ u hu
    have hH := finiteIntervalOne_bounds_positiveK lam h0 hp Q u
    refine ⟨?_,?_,hH.1,hH.2.trans hC⟩
    · have hlow : (1/(1+h))*fullLineDensityFunction lam h0 hpi u ≤ fullLineDensityFunction lam h0 hpi u := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 hr
      exact hlow.trans hR.1
    · exact hR.2.trans_eq (by dsimp [tau]; rw [div_eq_inv_mul])

end
end SixVertex
