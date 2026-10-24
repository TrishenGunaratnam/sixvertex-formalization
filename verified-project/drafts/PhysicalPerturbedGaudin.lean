import SixVertex.PhysicalOrderedNewtonRoots

namespace SixVertex
noncomputable section
open Set

/-- A sufficiently small perturbation of an operator with a bounded
right inverse still has a right inverse, constructed by a convergent
Neumann series. -/
theorem finite_operator_small_perturbation_right_inverse {n : ℕ}
    (J Inv G : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hJ : J*Inv=1) (hsmall : ‖G-J‖*‖Inv‖ < 1) :
    ∃ B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ),G*B=1 := by
  let A := (G-J)*Inv
  have hA : ‖A‖ < 1 := (norm_mul_le _ _).trans_lt hsmall
  have heq : G*Inv=1+A := by
    dsimp [A]
    rw [sub_mul,hJ]
    abel
  refine ⟨Inv*(∑' m : ℕ,(-A)^m),?_⟩
  rw [← mul_assoc,heq]
  exact finite_operator_neumann_right A hA

/-- Surjectivity of any right-scaled actual Gaudin operator implies
nonsingularity of the original actual matrix. -/
theorem gaudin_det_ne_zero_of_scaled_right_inverse {n : ℕ} (lam : ℝ) (b : ℕ → ℝ)
    (L : ℕ) (X : Fin n → ℝ) (D B : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ))
    (hInv : ((gaudinCLM lam b L X).comp D)*B=1) :
    (gaudinMatrix lam b L X).det ≠ 0 := by
  have hs : Function.Surjective ((gaudinCLM lam b L X).comp D) := by
    intro y
    refine ⟨B y,?_⟩
    exact congrArg (fun T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => T y) hInv
  have hg : Function.Surjective (gaudinCLM lam b L X) := by
    intro y
    obtain ⟨v,hv⟩ := hs y
    exact ⟨D v,hv⟩
  have hu : IsUnit (gaudinMatrix lam b L X) := Matrix.mulVec_surjective_iff_isUnit.mp hg
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

/-- The actual Gaudin matrix is nonsingular throughout a weighted
neighborhood of the actual reference quantiles, for every physical
lambda. The threshold is chosen before every finite datum. -/
theorem exists_weighted_gaudin_nonsingularity_threshold_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius : ℝ) (hrad : 0 ≤ radius) :
    ∃ M₀ : ℝ,0 < M₀ ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) →
      (gaudinMatrix lam (fun _ => 0) L X).det ≠ 0 := by
  obtain ⟨m,C,hm,hC,hinv⟩ := exists_uniform_referenceGaudin_inverse_all lam h0 hpi
  obtain ⟨m',hm',hsmall⟩ := exists_physicalJacobianVariation_threshold lam radius (1/(2*C)) (by positivity)
  let M₀ := max m m'
  have hM : 0 < M₀ := hm.trans_le (le_max_left _ _)
  refine ⟨M₀,hM,?_⟩
  intro n Q L Y X R hlower hclose
  obtain ⟨hleft,hright,hInv⟩ := hinv n Q L Y R
    (fun u hu => (le_max_left _ _).trans (hlower u hu))
  let D := referenceInverseDensityOperator lam h0 hpi Q L Y
  let J := referenceScaledGaudin lam h0 hpi Q L Y
  let Inv := referenceGaudinInverse lam h0 hpi Q L Y
  let G := (gaudinCLM lam (fun _ => 0) L X).comp D
  have he : ‖G-J‖ ≤ physicalJacobianVariationBound lam radius M₀ :=
    weighted_configuration_gaudin_norm_difference_all lam h0 hpi Q L Y X R M₀ hM hlower radius hrad hclose
  have he' : ‖G-J‖ < 1/(2*C) := he.trans_lt (hsmall M₀ (le_max_right _ _))
  have hs : ‖G-J‖*‖Inv‖ < 1 := by
    have h := mul_lt_mul_of_pos_right he' hC
    have hid : (1/(2*C))*C=(1 : ℝ)/2 := by field_simp
    rw [hid] at h
    exact (mul_le_mul_of_nonneg_left hInv (norm_nonneg (G-J))).trans_lt (by linarith)
  obtain ⟨B,hB⟩ := finite_operator_small_perturbation_right_inverse J Inv G hright hs
  exact gaudin_det_ne_zero_of_scaled_right_inverse lam (fun _ => 0) L X D B hB

end
end SixVertex
