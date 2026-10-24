import SixVertex.ArrayCountingDensity
import SixVertex.HalfFilledQuadrature

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal

/-- The actual array quadrature error is O(d), uniformly in chain length
and every test window contained in the bare array's bulk. -/
theorem exists_array_window_quadrature_rate (lam : ℝ) (hhalf : Real.pi/2 ≤ lam)
    (hpi : lam < Real.pi) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n L : ℕ) (d : ℝ), 0 < L → L=2*n → 0 < d → d ≤ 1 →
      ∀ (Z : Fin n → ℝ), ConsecutiveRoots lam (arraySite L d) L Z 0 →
      ∀ a : ℝ, |a|+A+1 ≤ (L : ℝ)*d/4 →
      ∀ phi : BoundedRealFunction, LipschitzWith 1 (fun x => phi x) → ‖phi‖ ≤ 1 →
      (∀ x, x ∉ Icc (a-A) (a+A) → phi x=0) →
      |(∫ x, phi x ∂rootQuadratureMeasure lam (arraySite L d) L Z)-(∫ x : ℝ, phi x)| ≤ C*d := by
  obtain ⟨c,hc,hgrowth⟩ := exists_array_counting_density_lower lam hhalf hpi
  let C : ℝ := A*(1+kernelLogConstant lam)/c
  have hC : 0 < C := div_pos (mul_pos hA (by linarith [kernelLogConstant_nonneg lam])) hc
  refine ⟨C,hC,?_⟩
  intro n L d hL hfill hd hd1 Z hZ a hspan phi hLip hnorm hs
  have he := unit_bounded_lipschitz_quadrature_error lam (arraySite L d) L hL Z hhalf hpi hZ phi hLip hnorm
    (a-A) (a+A) (c/d) (by linarith) (div_pos hc hd) hs
    (fun u hu => hgrowth n L d hd hd1 Z u (by
      have huA : |u-a| ≤ A := abs_le.mpr ⟨by linarith [hu.1],by linarith [hu.2]⟩
      have htri : |u| ≤ |u-a|+|a| := by simpa only [sub_zero] using abs_sub_le u a 0
      linarith))
    (fun u _ => countingXi_half_bounds lam (arraySite L d) L hL hfill Z hhalf hpi u)
  apply he.trans_eq
  dsimp [C]
  field_simp [hc.ne',hd.ne']
  ring

/-- Translating the test follows the moving array center, while its
Lebesgue integral is unchanged. -/
theorem exists_translated_array_quadrature_rate (lam : ℝ) (hhalf : Real.pi/2 ≤ lam)
    (hpi : lam < Real.pi) (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n L : ℕ) (d : ℝ), 0 < L → L=2*n → 0 < d → d ≤ 1 →
      ∀ (Z : Fin n → ℝ), ConsecutiveRoots lam (arraySite L d) L Z 0 →
      ∀ a : ℝ, |a|+A+1 ≤ (L : ℝ)*d/4 →
      ∀ phi : BoundedRealFunction, LipschitzWith 1 (fun x => phi x) → ‖phi‖ ≤ 1 →
      (∀ x, x ∉ Icc (-A) A → phi x=0) →
      |(∫ x, phi (x-a) ∂rootQuadratureMeasure lam (arraySite L d) L Z)-(∫ x : ℝ, phi x)| ≤ C*d := by
  obtain ⟨C,hC,hbound⟩ := exists_array_window_quadrature_rate lam hhalf hpi A hA
  refine ⟨C,hC,?_⟩
  intro n L d hL hfill hd hd1 Z hZ a hspan phi hLip hnorm hs
  let psi := translateBoundedFunction phi a
  have hpLip : LipschitzWith 1 (fun x => psi x) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |phi (x-a)-phi (y-a)| ≤ ((1 : ℝ≥0) : ℝ)*|x-y|
    have hh := hLip.dist_le_mul (x-a) (y-a)
    have heq : (x-a)-(y-a)=x-y := by ring
    simpa only [Real.dist_eq,heq] using hh
  have hpNorm : ‖psi‖ ≤ 1 := by
    apply le_trans _ hnorm
    apply (BoundedContinuousFunction.norm_le (norm_nonneg phi)).mpr
    intro x
    exact phi.norm_coe_le_norm (x-a)
  have hpSupport : ∀ x, x ∉ Icc (a-A) (a+A) → psi x=0 := by
    intro x hx
    change phi (x-a)=0
    apply hs
    intro hh
    apply hx
    exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have he := hbound n L d hL hfill hd hd1 Z hZ a hspan psi hpLip hpNorm hpSupport
  have hInt : (∫ x : ℝ, psi x)=∫ x : ℝ, phi x := by
    change (∫ x : ℝ, phi (x-a))=∫ x : ℝ, phi x
    exact integral_sub_right_eq_self (fun x => phi x) a
  rw [hInt] at he
  exact he

/-- Uniform two-stage array convergence in the manuscript convention:
first the width is large, then the spacing is small, with moving centers
anywhere in a fixed bulk fraction. -/
theorem array_bulk_quadrature_limit (lam : ℝ) (hhalf : Real.pi/2 ≤ lam)
    (hpi : lam < Real.pi) (A : ℝ) (hA : 0 < A) (gamma : ℝ) (hg : 0 < gamma) (hg1 : gamma < 1) :
    ∀ eps : ℝ, 0 < eps → ∃ d₀ B₀ : ℝ, 0 < d₀ ∧ 0 < B₀ ∧
      ∀ d : ℝ, 0 < d → d < d₀ → ∀ n L : ℕ, 0 < L → L=2*n →
      B₀ ≤ (L : ℝ)*d/2 → ∀ (Z : Fin n → ℝ), ConsecutiveRoots lam (arraySite L d) L Z 0 →
      ∀ a : ℝ, |a| ≤ (1-gamma)*((L : ℝ)*d/2)/2 →
      ∀ phi : BoundedRealFunction, LipschitzWith 1 (fun x => phi x) → ‖phi‖ ≤ 1 →
      (∀ x, x ∉ Icc (-A) A → phi x=0) →
      |(∫ x, phi (x-a) ∂rootQuadratureMeasure lam (arraySite L d) L Z)-(∫ x : ℝ, phi x)| ≤ eps := by
  obtain ⟨C,hC,hbound⟩ := exists_translated_array_quadrature_rate lam hhalf hpi A hA
  intro eps heps
  let d₀ : ℝ := min 1 (eps/C)
  let B₀ : ℝ := 2*(A+1)/gamma
  have hd₀ : 0 < d₀ := lt_min (by norm_num) (div_pos heps hC)
  have hB₀ : 0 < B₀ := div_pos (by linarith) hg
  refine ⟨d₀,B₀,hd₀,hB₀,?_⟩
  intro d hd hdd n L hL hfill hB Z hZ a ha phi hLip hnorm hs
  have hd1 : d ≤ 1 := hdd.le.trans (min_le_left _ _)
  have hdeps : d ≤ eps/C := hdd.le.trans (min_le_right _ _)
  have hBmul : 2*(A+1) ≤ ((L : ℝ)*d/2)*gamma := (div_le_iff₀ hg).mp hB
  have hspan : |a|+A+1 ≤ (L : ℝ)*d/4 := by nlinarith only [hBmul,ha]
  exact (hbound n L d hL hfill hd hd1 Z hZ a hspan phi hLip hnorm hs).trans
    (by have hh := (le_div_iff₀ hC).mp hdeps; nlinarith only [hh])

end
end SixVertex
