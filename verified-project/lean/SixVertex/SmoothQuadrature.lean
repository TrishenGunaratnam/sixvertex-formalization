import SixVertex.CompactCountingError
import SixVertex.NormalizedTest
import SixVertex.QuadratureMeasure
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Integration against the manuscript's actual weighted atomic measure.
All inverse-density weights are positive; no independently defined
quadrature functional is substituted for this measure. -/
theorem integral_rootQuadratureMeasure {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (phi : ℝ → ℝ) :
    (∫ x, phi x ∂rootQuadratureMeasure lam b L Y)=
      ∑ j : Fin n, phi (Y j)/countingSlope lam b L Y (Y j) := by
  unfold rootQuadratureMeasure
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top),tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (countingSlope_pos_nonpositiveK lam b L hL Y _ hhalf hpi).le)]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- Quantitative quadrature on an occupied window for compact C1 tests.
The constant is uniform in the chain, filling, array and root list. -/
theorem smooth_quadrature_error {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0)
    (phi phi' : BoundedRealFunction) (a z M : ℝ) (haz : a ≤ z) (hM : 0 < M)
    (hdphi : ∀ x, HasDerivAt (fun v => phi v) (phi' x) x)
    (hs : ∀ x, x ∉ Icc a z → phi x=0) (hs' : ∀ x, x ∉ Icc a z → phi' x=0)
    (hlower : ∀ x ∈ Icc a z, M ≤ countingSlope lam b L Y x)
    (hwindow : ∀ x ∈ Icc a z, -(n : ℝ)/2 ≤ countingXi lam b L Y x ∧
      countingXi lam b L Y x ≤ (n : ℝ)/2) :
    |(∫ x, phi x ∂rootQuadratureMeasure lam b L Y)-(∫ x : ℝ, phi x)| ≤
      (z-a)*(‖phi'‖+kernelLogConstant lam*‖phi‖)/(2*M) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hrho : Continuous (countingSlope lam b L Y) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_countingSlope lam b L Y x h0 hpi).continuousAt)
  obtain ⟨f,f',hf,hdf,hfs,hfs',hfbd⟩ := exists_normalized_compact_test phi phi'
    (countingSlope lam b L Y) (countingCurvature lam b L Y) hrho
    (continuous_countingCurvature lam b L Y h0 hpi)
    (fun x => countingSlope_pos_nonpositiveK lam b L hL Y x hhalf hpi)
    hdphi (fun x => hasDerivAt_countingSlope lam b L Y x h0 hpi)
    a z M (kernelLogConstant lam) hM (kernelLogConstant_nonneg lam) hs hs' hlower
    (fun x => countingCurvature_relative_bound lam b L Y hhalf hpi x)
  have he := counting_discrete_smooth_error lam b L hL Y hhalf hpi hroots f f' a z haz hdf hfs hfs'
    hwindow ((‖phi'‖+kernelLogConstant lam*‖phi‖)/M) (fun x _ => hfbd x)
  have hm (x : ℝ) : f x*countingSlope lam b L Y x=phi x := by
    rw [hf x,div_mul_cancel₀ _ (countingSlope_pos_nonpositiveK lam b L hL Y x hhalf hpi).ne']
  simp_rw [hm] at he
  simp_rw [hf] at he
  rw [integral_rootQuadratureMeasure lam b L hL Y hhalf hpi]
  convert he using 1 <;> ring

/-- At exact half filling the occupied counting-window condition holds
on every compact interval, so only the local density lower bound remains. -/
theorem half_filled_smooth_quadrature_error {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0)
    (phi phi' : BoundedRealFunction) (a z M : ℝ) (haz : a ≤ z) (hM : 0 < M)
    (hdphi : ∀ x, HasDerivAt (fun v => phi v) (phi' x) x)
    (hs : ∀ x, x ∉ Icc a z → phi x=0) (hs' : ∀ x, x ∉ Icc a z → phi' x=0)
    (hlower : ∀ x ∈ Icc a z, M ≤ countingSlope lam b L Y x) :
    |(∫ x, phi x ∂rootQuadratureMeasure lam b L Y)-(∫ x : ℝ, phi x)| ≤
      (z-a)*(‖phi'‖+kernelLogConstant lam*‖phi‖)/(2*M) :=
  smooth_quadrature_error lam b L hL Y hhalf hpi hroots phi phi' a z M haz hM hdphi hs hs' hlower
    (fun x _ => countingXi_half_bounds lam b L hL hfill Y hhalf hpi x)

end
end SixVertex
