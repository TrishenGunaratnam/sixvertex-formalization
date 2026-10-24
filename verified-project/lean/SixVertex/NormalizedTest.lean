import SixVertex.DensityRegularity
import SixVertex.BoundedConvolution

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem normalized_derivative_scalar_bound (p p' r r' M C : ℝ)
    (hM : 0 < M) (hMr : M ≤ r) (hC : 0 ≤ C) (hd : |r'| ≤ C*r) :
    |(p'*r-p*r')/r^2| ≤ (|p'|+C*|p|)/M := by
  have hr : 0 < r := hM.trans_le hMr
  have hn : |p'*r-p*r'| ≤ (|p'|+C*|p|)*r := by
    calc
      _ ≤ |p'*r|+|p*r'| := abs_sub _ _
      _ = |p'| *r+|p| *|r'| := by rw [abs_mul,abs_mul,abs_of_pos hr]
      _ ≤ |p'| *r+|p| *(C*r) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hd (abs_nonneg _))
      _ = _ := by ring
  rw [abs_div,abs_of_nonneg (sq_nonneg r)]
  calc
    _ ≤ ((|p'|+C*|p|)*r)/r^2 := div_le_div_of_nonneg_right hn (sq_nonneg _)
    _ = (|p'|+C*|p|)/r := by field_simp
    _ ≤ (|p'|+C*|p|)/M := div_le_div_of_nonneg_left (by positivity) hM hMr

/-- The derivative bound for the actual quotient by a positive density.
No quotient derivative or density regularity is postulated. -/
theorem exists_normalized_compact_test (phi phi' : BoundedRealFunction)
    (rho rho' : ℝ → ℝ) (hrho : Continuous rho) (hrho' : Continuous rho')
    (hpos : ∀ x, 0 < rho x)
    (hdphi : ∀ x, HasDerivAt (fun v => phi v) (phi' x) x)
    (hdrho : ∀ x, HasDerivAt rho (rho' x) x)
    (a z M C : ℝ) (hM : 0 < M) (hC : 0 ≤ C)
    (hs : ∀ x, x ∉ Icc a z → phi x=0)
    (hs' : ∀ x, x ∉ Icc a z → phi' x=0)
    (hlower : ∀ x ∈ Icc a z, M ≤ rho x)
    (hrelative : ∀ x, |rho' x| ≤ C*rho x) :
    ∃ f f' : BoundedRealFunction,
      (∀ x, f x=phi x/rho x) ∧
      (∀ x, HasDerivAt (fun v => f v) (f' x) x) ∧
      (∀ x, x ∉ Icc a z → f x=0) ∧
      (∀ x, x ∉ Icc a z → f' x=0) ∧
      (∀ x, |f' x| ≤ (‖phi'‖+C*‖phi‖)/M) := by
  let v : ℝ → ℝ := fun x => phi x/rho x
  let d : ℝ → ℝ := fun x => (phi' x*rho x-phi x*rho' x)/(rho x)^2
  have hv : Continuous v := phi.continuous.div hrho (fun x => (hpos x).ne')
  have hd : Continuous d := ((phi'.continuous.mul hrho).sub (phi.continuous.mul hrho')).div
    (hrho.pow 2) (fun x => pow_ne_zero 2 (hpos x).ne')
  have hzv : ∀ x, x ∉ Icc a z → v x=0 := by intro x hx; dsimp [v]; rw [hs x hx,zero_div]
  have hzd : ∀ x, x ∉ Icc a z → d x=0 := by intro x hx; dsimp [d]; rw [hs x hx,hs' x hx]; simp
  have hbv : ∀ x, |v x| ≤ ‖phi‖/M := by
    intro x
    by_cases hx : x ∈ Icc a z
    · dsimp [v]
      rw [abs_div,abs_of_pos (hpos x)]
      apply le_trans (div_le_div_of_nonneg_right (by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm x) (hpos x).le)
      exact div_le_div_of_nonneg_left (norm_nonneg _) hM (hlower x hx)
    · rw [hzv x hx]
      simp only [abs_zero]
      positivity
  have hbd : ∀ x, |d x| ≤ (‖phi'‖+C*‖phi‖)/M := by
    intro x
    by_cases hx : x ∈ Icc a z
    · apply (normalized_derivative_scalar_bound (phi x) (phi' x) (rho x) (rho' x) M C
        hM (hlower x hx) hC (hrelative x)).trans
      apply div_le_div_of_nonneg_right _ hM.le
      apply add_le_add
      · simpa only [Real.norm_eq_abs] using phi'.norm_coe_le_norm x
      · exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using phi.norm_coe_le_norm x) hC
    · rw [hzd x hx]
      simp only [abs_zero]
      positivity
  let f := BoundedContinuousFunction.ofNormedAddCommGroup v hv (‖phi‖/M) hbv
  let f' := BoundedContinuousFunction.ofNormedAddCommGroup d hd ((‖phi'‖+C*‖phi‖)/M) hbd
  refine ⟨f,f',fun _ => rfl,?_,hzv,hzd,hbd⟩
  intro x
  exact (hdphi x).div (hdrho x) (hpos x).ne'

end
end SixVertex
