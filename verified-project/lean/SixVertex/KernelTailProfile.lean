import SixVertex.KernelTailComparison
import SixVertex.DensityRegularity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Analytic data for a positive physical kernel, with explicit
whole-line upper and positive-half-line lower exponential envelopes. -/
structure PositiveKernelTailData (q : ℝ → ℝ) (c C : ℝ) : Prop where
  integrable : Integrable q
  nonnegative : ∀ u, 0 ≤ q u
  lower_pos : 0 < c
  upper_pos : 0 < C
  lower : ∀ u, c*Real.exp (-2*|u|) ≤ q u
  upper : ∀ u, q u ≤ C*Real.exp (-2*|u|)

theorem PositiveKernelTailData.tail_bounds {q : ℝ → ℝ} {c C : ℝ}
    (h : PositiveKernelTailData q c C) (u : ℝ) (hu : 0 ≤ u) :
    (c/2)*Real.exp (-2*u) ≤ kernelTail q u ∧ kernelTail q u ≤ (C/2)*Real.exp (-2*u) := by
  apply kernelTail_exponential_bounds q h.integrable c C
  · intro v hv
    simpa only [abs_of_nonneg hv] using h.lower v
  · intro v hv
    simpa only [abs_of_nonneg hv] using h.upper v
  · exact hu

theorem PositiveKernelTailData.shift_bound {q : ℝ → ℝ} {c C : ℝ}
    (h : PositiveKernelTailData q c C) (u t : ℝ) (hu : 0 ≤ u) (ht : 0 ≤ t) :
    kernelTail q (u+t) ≤ (C/c)*Real.exp (-2*t)*kernelTail q u := by
  apply kernelTail_shift_exponential q h.integrable c C h.lower_pos h.upper_pos.le
  · intro v hv
    simpa only [abs_of_nonneg hv] using h.lower v
  · intro v hv
    simpa only [abs_of_nonneg hv] using h.upper v
  · exact hu
  · exact ht

/-- The source kernel s has positive two-sided exponential envelopes
for every physical parameter. -/
theorem kernelS_positive_tail_data (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    PositiveKernelTailData (kernelS lam) (Real.sin lam/(2*Real.pi))
      (2/(Real.pi*(Real.sin (lam/2))^2)) := by
  have hh0 : 0 < lam/2 := by linarith
  have hhpi : lam/2 < Real.pi := by linarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  have hs2 := Real.sin_pos_of_pos_of_lt_pi hh0 hhpi
  have he : (kernelS lam)=(kernelK (lam/2)) := funext (kernelS_eq_phaseDensity lam)
  refine ⟨kernelS_integrable lam h0 hpi,(fun u => (kernelS_pos lam u h0 hpi).le),
    div_pos hs (mul_pos (by norm_num) Real.pi_pos),by positivity,?_,?_⟩
  · intro u
    have h := kernelK_exponential_lower_bound (lam/2) u hh0 hhpi
    rw [show 2*(lam/2)=lam by ring,abs_of_pos hs,← he,abs_of_pos (kernelS_pos lam u h0 hpi)] at h
    exact h
  · intro u
    have h := kernelK_exponential_bound (lam/2) u hh0 hhpi
    rw [← he,abs_of_pos (kernelS_pos lam u h0 hpi)] at h
    exact h

/-- In the strict negative-kernel regime k=-K is a positive L1 kernel
with positive explicit envelope constants. -/
theorem negative_kernel_positive_tail_data (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    PositiveKernelTailData (fun u => -kernelK lam u) (|Real.sin (2*lam)|/(2*Real.pi))
      (2/(Real.pi*(Real.sin lam)^2)) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  have hsin : Real.sin (2*lam) ≠ 0 := by
    have hk := kernelK_strict_neg lam 0 hhalf hpi
    intro hn
    have hz : kernelK lam 0=0 := by unfold kernelK phaseDensity; rw [hn]; simp
    linarith
  refine ⟨(kernelK_integrable lam h0 hpi).neg,(fun u => (neg_pos.mpr (kernelK_strict_neg lam u hhalf hpi)).le),
    div_pos (abs_pos.mpr hsin) (mul_pos (by norm_num) Real.pi_pos),by positivity,?_,?_⟩
  · intro u
    simpa only [abs_of_neg (kernelK_strict_neg lam u hhalf hpi)] using
      kernelK_exponential_lower_bound lam u h0 hpi
  · intro u
    simpa only [abs_of_neg (kernelK_strict_neg lam u hhalf hpi)] using
      kernelK_exponential_bound lam u h0 hpi

end
end SixVertex
