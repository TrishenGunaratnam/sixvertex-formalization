import SixVertex.LocalCountingWindow
import SixVertex.DensityRegularity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem continuous_integrable_supported_Icc (f : ℝ → ℝ) (hf : Continuous f)
    (a z : ℝ) (hs : ∀ x, x ∉ Icc a z → f x=0) : Integrable f := by
  have hi := (hf.integrableOn_Icc (μ := volume) (a := a) (b := z)).integrable_indicator measurableSet_Icc
  have he : (Icc a z).indicator f=f := by
    funext x
    by_cases hx : x ∈ Icc a z
    · exact Set.indicator_of_mem hx f
    · rw [Set.indicator_of_notMem hx,hs x hx]
  rwa [he] at hi

/-- Compactly supported discrete/smooth integration by parts. The error
bound uses the counting window only where the derivative is supported. -/
theorem counting_discrete_smooth_error {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0)
    (f f' : BoundedRealFunction) (a z : ℝ) (haz : a ≤ z)
    (hdf : ∀ x, HasDerivAt (fun v => f v) (f' x) x)
    (hs : ∀ x, x ∉ Icc a z → f x=0) (hs' : ∀ x, x ∉ Icc a z → f' x=0)
    (hwindow : ∀ x ∈ Icc a z, -(n : ℝ)/2 ≤ countingXi lam b L Y x ∧
      countingXi lam b L Y x ≤ (n : ℝ)/2)
    (D : ℝ) (hD : ∀ x ∈ Icc a z, |f' x| ≤ D) :
    |(∑ j : Fin n, f (Y j))-(∫ x : ℝ, f x*countingSlope lam b L Y x)| ≤ (z-a)*D/2 := by
  let negMap : ContinuousMap ℝ ℝ := ⟨fun x => -x,continuous_neg⟩
  let q := f.compContinuous negMap
  let q' := -(f'.compContinuous negMap)
  have hi := continuous_integrable_supported_Icc (fun x => f x) f.continuous a z hs
  have hi' := continuous_integrable_supported_Icc (fun x => f' x) f'.continuous a z hs'
  have hq : Integrable (fun x => q x) := by
    exact hi.comp_neg
  have hq' : Integrable (fun x => q' x) := by
    exact hi'.comp_neg.neg
  have hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x := by
    intro x
    simpa only [Function.comp_def,mul_neg_one] using!
      (hdf (-x)).comp x (hasDerivAt_neg x)
  have he := countingDiscrepancy_kernel_identity_general lam b L hL Y hhalf hpi q q' hq hq' hdq 0
  have hqa (x : ℝ) : q (0-x)=f x := by change f (-(0-x))=f x; rw [zero_sub,neg_neg]
  have hqpa (x : ℝ) : q' (0-x)= -f' x := by change -f' (-(0-x))= -f' x; rw [zero_sub,neg_neg]
  simp_rw [hqa,hqpa] at he
  rw [← he]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Icc a z) (fun x hx => by rw [hs' x hx]; simp)]
  have hb := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc a z)
    (f := fun x : ℝ => (-f' x)*countingDiscrepancy lam b L Y x)
    (C := D/2) (isCompact_Icc.measure_lt_top) (by
      intro x hx
      rw [Real.norm_eq_abs,abs_mul,abs_neg]
      have hw := hwindow x hx
      have hF := countingDiscrepancy_bound_in_window lam b L hL Y hhalf hpi hroots x hw.1 hw.2
      calc
        _ ≤ |f' x| *(1/2) := mul_le_mul_of_nonneg_left hF (abs_nonneg _)
        _ ≤ D*(1/2) := mul_le_mul_of_nonneg_right (hD x hx) (by norm_num)
        _ = D/2 := by ring)
  rw [Real.norm_eq_abs] at hb
  convert hb using 1
  rw [Real.volume_real_Icc_of_le haz]
  ring

end
end SixVertex
