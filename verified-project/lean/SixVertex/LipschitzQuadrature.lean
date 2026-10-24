import SixVertex.LipschitzCountingError
import SixVertex.NormalizedLipschitz
import SixVertex.SmoothQuadrature

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal

/-- The paper's bounded-Lipschitz quadrature error, on an occupied window.
The only local scale is an explicit lower bound M for the actual density. -/
theorem bounded_lipschitz_quadrature_error {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0)
    (phi : BoundedRealFunction) (K : ℝ≥0) (hLip : LipschitzWith K (fun x => phi x))
    (a z M : ℝ) (haz : a ≤ z) (hM : 0 < M)
    (hs : ∀ x, x ∉ Icc a z → phi x=0)
    (hlower : ∀ x ∈ Icc a z, M ≤ countingSlope lam b L Y x)
    (hwindow : ∀ x ∈ Icc a z, -(n : ℝ)/2 ≤ countingXi lam b L Y x ∧
      countingXi lam b L Y x ≤ (n : ℝ)/2) :
    |(∫ x, phi x ∂rootQuadratureMeasure lam b L Y)-(∫ x : ℝ, phi x)| ≤
      (z-a)*((K : ℝ)+kernelLogConstant lam*‖phi‖)/(2*M) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hrho : Continuous (countingSlope lam b L Y) := continuous_iff_continuousAt.mpr
    (fun x => (hasDerivAt_countingSlope lam b L Y x h0 hpi).continuousAt)
  obtain ⟨f,hf,hfs,hfLip⟩ := exists_normalized_lipschitz_test phi K hLip
    (countingSlope lam b L Y) (countingCurvature lam b L Y) hrho
    (fun x => countingSlope_pos_nonpositiveK lam b L hL Y x hhalf hpi)
    (fun x => hasDerivAt_countingSlope lam b L Y x h0 hpi)
    a z M (kernelLogConstant lam) haz hM (kernelLogConstant_nonneg lam) hs hlower
    (fun x => countingCurvature_relative_bound lam b L Y hhalf hpi x)
  have he := counting_lipschitz_discrete_smooth_error lam b L hL Y hhalf hpi hroots f _ hfLip a z haz hfs hwindow
  have hm (x : ℝ) : f x*countingSlope lam b L Y x=phi x := by
    rw [hf x,div_mul_cancel₀ _ (countingSlope_pos_nonpositiveK lam b L hL Y x hhalf hpi).ne']
  simp_rw [hm] at he
  simp_rw [hf] at he
  rw [integral_rootQuadratureMeasure lam b L hL Y hhalf hpi]
  change |(∑ j : Fin n, phi (Y j)/countingSlope lam b L Y (Y j))-(∫ x : ℝ, phi x)| ≤
    (z-a)*(((K : ℝ)+kernelLogConstant lam*‖phi‖)/M)/2 at he
  convert he using 1 <;> ring

/-- At half filling every compact interval is an occupied counting window. -/
theorem half_filled_lipschitz_quadrature_error {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0)
    (phi : BoundedRealFunction) (K : ℝ≥0) (hLip : LipschitzWith K (fun x => phi x))
    (a z M : ℝ) (haz : a ≤ z) (hM : 0 < M)
    (hs : ∀ x, x ∉ Icc a z → phi x=0)
    (hlower : ∀ x ∈ Icc a z, M ≤ countingSlope lam b L Y x) :
    |(∫ x, phi x ∂rootQuadratureMeasure lam b L Y)-(∫ x : ℝ, phi x)| ≤
      (z-a)*((K : ℝ)+kernelLogConstant lam*‖phi‖)/(2*M) :=
  bounded_lipschitz_quadrature_error lam b L hL Y hhalf hpi hroots phi K hLip a z M haz hM hs hlower
    (fun x _ => countingXi_half_bounds lam b L hL hfill Y hhalf hpi x)

/-- One constant for all unit bounded-Lipschitz tests on the same occupied
interval, matching the uniform O(1/M) test-function clause. -/
theorem unit_bounded_lipschitz_quadrature_error {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0)
    (phi : BoundedRealFunction) (hLip : LipschitzWith 1 (fun x => phi x)) (hnorm : ‖phi‖ ≤ 1)
    (a z M : ℝ) (haz : a ≤ z) (hM : 0 < M)
    (hs : ∀ x, x ∉ Icc a z → phi x=0)
    (hlower : ∀ x ∈ Icc a z, M ≤ countingSlope lam b L Y x)
    (hwindow : ∀ x ∈ Icc a z, -(n : ℝ)/2 ≤ countingXi lam b L Y x ∧
      countingXi lam b L Y x ≤ (n : ℝ)/2) :
    |(∫ x, phi x ∂rootQuadratureMeasure lam b L Y)-(∫ x : ℝ, phi x)| ≤
      (z-a)*(1+kernelLogConstant lam)/(2*M) := by
  apply (bounded_lipschitz_quadrature_error lam b L hL Y hhalf hpi hroots phi 1 hLip a z M haz hM hs hlower hwindow).trans
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr haz)
  simp only [NNReal.coe_one]
  have hc := mul_le_mul_of_nonneg_left hnorm (kernelLogConstant_nonneg lam)
  linarith

end
end SixVertex
