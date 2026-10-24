import SixVertex.PhysicalJacobianVariation
import SixVertex.FiniteQuantitativeNewton

namespace SixVertex
noncomputable section
open Set Metric

/-- Actual finite Bethe equations have a solution in a uniformly weighted
neighborhood of the actual continuum reference quantiles throughout the
physical range. Ordering is a subsequent obligation. -/
theorem exists_weighted_reference_counting_solution_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ M₀ radius : ℝ, 0 < M₀ ∧ 0 < radius ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      ∃ X : Fin n → ℝ,countingSystem lam (fun _ => 0) L X=countingTarget n 0 ∧
        ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) := by
  obtain ⟨m,C,hm,hC,hinv⟩ := exists_uniform_referenceGaudin_inverse_all lam h0 hpi
  let radius := C*|1-2*lam/Real.pi|+1
  have hrad : 0 < radius := by dsimp [radius]; positivity
  have heps : 0 < 1/(2*C) := by positivity
  obtain ⟨m',hm',hsmall⟩ := exists_physicalJacobianVariation_threshold lam radius (1/(2*C)) heps
  let M₀ := max m m'
  have hM : 0 < M₀ := hm.trans_le (le_max_left _ _)
  refine ⟨M₀,radius,hM,hrad,?_⟩
  intro n Q L Y R hlower
  have hlower' : ∀ u ∈ Icc (-Q) Q,m ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u :=
    fun u hu => (le_max_left _ _).trans (hlower u hu)
  obtain ⟨hleft,hright,hB⟩ := hinv n Q L Y R hlower'
  let D := referenceInverseDensityOperator lam h0 hpi Q L Y
  let z : (Fin n → ℝ) → (Fin n → ℝ) := fun v => Y+D v
  let f : (Fin n → ℝ) → (Fin n → ℝ) := fun v => countingSystem lam (fun _ => 0) L (z v)-countingTarget n 0
  let df : (Fin n → ℝ) → ((Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :=
    fun v => (gaudinCLM lam (fun _ => 0) L (z v)).comp D
  let J := referenceScaledGaudin lam h0 hpi Q L Y
  let B := referenceGaudinInverse lam h0 hpi Q L Y
  have hclose (v : Fin n → ℝ) (hv : ‖v‖ ≤ radius) (j : Fin n) :
      |z v j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) := by
    let w := (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)
    have hw : 0 < w := hM.trans_le (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩)
    change |(Y+D v) j-Y j| ≤ radius/w
    simp only [Pi.add_apply,add_sub_cancel_left,D,referenceInverseDensityOperator,finiteDiagonalOperator_apply]
    change |w⁻¹*v j| ≤ radius/w
    rw [abs_mul,abs_inv,abs_of_pos hw]
    have hvj0 : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
    have hvj : |v j| ≤ radius := hvj0.trans hv
    have ht := div_le_div_of_nonneg_right hvj hw.le
    simpa only [div_eq_mul_inv,mul_comm] using ht
  have hderiv (v : Fin n → ℝ) (_hv : v ∈ closedBall (0 : Fin n → ℝ) radius) : HasFDerivAt f (df v) v := by
    have hz : HasFDerivAt z D v := by
      convert ((hasFDerivAt_const Y v).add D.hasFDerivAt) using 1 <;> simp [z]
    exact ((hasFDerivAt_countingSystem lam (fun _ => 0) L (z v) h0 hpi).comp v hz).sub_const (countingTarget n 0)
  have herror (v : Fin n → ℝ) (hv : v ∈ closedBall (0 : Fin n → ℝ) radius) : ‖df v-J‖ ≤ 1/(2*C) := by
    have hv' : ‖v‖ ≤ radius := by simpa only [mem_closedBall,dist_zero_right] using hv
    exact (weighted_configuration_gaudin_norm_difference_all lam h0 hpi Q L Y (z v) R M₀ hM hlower radius hrad.le (hclose v hv')).trans
      (hsmall M₀ (le_max_right _ _)).le
  have hres : ‖f 0‖ ≤ radius/(2*C) := by
    have hf : f 0=countingSystem lam (fun _ => 0) L Y-countingTarget n 0 := by simp only [f,z,map_zero,add_zero]
    rw [hf]
    apply (reference_bethe_residual_norm_all lam h0 hpi Q L Y R).trans
    apply (le_div_iff₀ (by positivity : 0 < 2*C)).mpr
    dsimp [radius]
    nlinarith
  obtain ⟨v,hv,hzero⟩ := finite_quantitative_newton_exists_zero f df J B C radius hC hrad.le hright hB hderiv herror hres
  refine ⟨z v,sub_eq_zero.mp hzero,hclose v hv⟩

end
end SixVertex
