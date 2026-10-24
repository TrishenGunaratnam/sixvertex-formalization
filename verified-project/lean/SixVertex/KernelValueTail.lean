import SixVertex.KernelTailProfile

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- The whole-line value-to-tail bound used at every finite source
and interaction center in the sparse-edge argument. -/
theorem PositiveKernelTailData.value_le_tail {q : ℝ → ℝ} {c C : ℝ}
    (h : PositiveKernelTailData q c C) (u : ℝ) : q u ≤ (2*C/c)*kernelTail q u := by
  have hD : 0 ≤ 2*C/c := div_nonneg (mul_nonneg (by norm_num) h.upper_pos.le) h.lower_pos.le
  have he : (2*C/c)*(c/2)=C := by field_simp [h.lower_pos.ne']
  by_cases hu : 0 ≤ u
  · have hlo := (h.tail_bounds u hu).1
    have hhi : q u ≤ C*Real.exp (-2*u) := by simpa only [abs_of_nonneg hu] using h.upper u
    calc
      _ ≤ C*Real.exp (-2*u) := hhi
      _ = (2*C/c)*((c/2)*Real.exp (-2*u)) := by rw [← mul_assoc,he]
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo hD
  · have htail0 : c/2 ≤ kernelTail q 0 := by
      simpa only [mul_zero,Real.exp_zero,mul_one] using (h.tail_bounds 0 le_rfl).1
    have htail : c/2 ≤ kernelTail q u := htail0.trans
      (kernelTail_antitone q h.integrable h.nonnegative (le_of_not_ge hu))
    have hhi : q u ≤ C := (h.upper u).trans
      (mul_le_of_le_one_right h.upper_pos.le (Real.exp_le_one_iff.mpr (by linarith [abs_nonneg u])))
    calc
      _ ≤ C := hhi
      _ = (2*C/c)*(c/2) := he.symm
      _ ≤ _ := mul_le_mul_of_nonneg_left htail hD

/-- On the outward half-line, the kernel also controls its tail from
below. Together these are the paper's kernel-tail comparison. -/
theorem PositiveKernelTailData.tail_le_value {q : ℝ → ℝ} {c C : ℝ}
    (h : PositiveKernelTailData q c C) (u : ℝ) (hu : 0 ≤ u) :
    (2*c/C)*kernelTail q u ≤ q u := by
  have hD : 0 ≤ 2*c/C := div_nonneg (mul_nonneg (by norm_num) h.lower_pos.le) h.upper_pos.le
  have he : (2*c/C)*(C/2)=c := by field_simp [h.upper_pos.ne']
  calc
    _ ≤ (2*c/C)*((C/2)*Real.exp (-2*u)) := mul_le_mul_of_nonneg_left (h.tail_bounds u hu).2 hD
    _ = c*Real.exp (-2*u) := by rw [← mul_assoc,he]
    _ ≤ _ := by simpa only [abs_of_nonneg hu] using h.lower u

end
end SixVertex
