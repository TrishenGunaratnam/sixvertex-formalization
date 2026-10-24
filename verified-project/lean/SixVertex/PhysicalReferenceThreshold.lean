import SixVertex.PhysicalReferenceGaudin
import SixVertex.UniformWindowComparison

namespace SixVertex
noncomputable section
open Set

/-- The actual finite-window density has a positive lower bound on all
bounded windows for every physical lambda, chosen before the window. -/
theorem exists_bounded_window_density_lower_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (B : ℝ) :
    ∃ d : ℝ,0 < d ∧ ∀ Q : ℝ,Q ≤ B → ∀ u ∈ Icc (-Q) Q,
      d ≤ finiteIntervalDensity lam h0 hpi Q u := by
  obtain ⟨c,C,hc,hC,hbound⟩ := exists_uniform_finiteInterval_comparison lam h0 hpi
  let d : ℝ := c*fullLineDensityFunction lam h0 hpi B
  refine ⟨d,mul_pos hc (fullLineDensityFunction_pos_all lam h0 hpi B),?_⟩
  intro Q hQB u hu
  have hQ : 0 ≤ Q := by linarith [hu.1,hu.2]
  have hab : |u| ≤ B := (abs_le.mpr hu).trans hQB
  have hr := fullLineDensityFunction_radiallyAntitone_all lam h0 hpi u B (hab.trans (le_abs_self B))
  exact (mul_le_mul_of_nonneg_left hr hc.le).trans (hbound Q hQ u (abs_le.mpr hu)).1

/-- Every fixed scaled-density threshold is reached uniformly over
bounded cutoffs as chain length increases, throughout the physical range. -/
theorem exists_bounded_window_scaled_density_threshold_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (B M : ℝ) :
    ∃ N : ℕ,∀ L : ℕ,N ≤ L → ∀ Q : ℝ,Q ≤ B → ∀ u ∈ Icc (-Q) Q,
      M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u := by
  obtain ⟨d,hd,hlo⟩ := exists_bounded_window_density_lower_all lam h0 hpi B
  obtain ⟨N,hN⟩ := exists_nat_gt (M/d)
  refine ⟨N,?_⟩
  intro L hL Q hQ u hu
  have hNL : (N : ℝ) ≤ L := Nat.cast_le.mpr hL
  have hML : M ≤ (L : ℝ)*d := ((div_lt_iff₀ hd).mp (hN.trans_le hNL)).le
  exact hML.trans (mul_le_mul_of_nonneg_left (hlo Q hQ u hu) (Nat.cast_nonneg L))

/-- Uniform actual reference-Gaudin inverses at bounded cutoffs for all
physical lambda; no inverse or density estimate is assumed as input. -/
theorem bounded_cutoff_referenceGaudin_inverse_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (B : ℝ) :
    ∃ N : ℕ,∃ C : ℝ,0 < C ∧ ∀ (n L : ℕ),N ≤ L → ∀ Q : ℝ,Q ≤ B →
      ∀ (Y : Fin n → ℝ) (R : ReferenceQuantileData lam h0 hpi Q L Y),
      referenceGaudinInverse lam h0 hpi Q L Y*referenceScaledGaudin lam h0 hpi Q L Y=1 ∧
      referenceScaledGaudin lam h0 hpi Q L Y*referenceGaudinInverse lam h0 hpi Q L Y=1 ∧
      ‖referenceGaudinInverse lam h0 hpi Q L Y‖ ≤ C := by
  obtain ⟨M,C,hM,hC,hInv⟩ := exists_uniform_referenceGaudin_inverse_all lam h0 hpi
  obtain ⟨N,hN⟩ := exists_bounded_window_scaled_density_threshold_all lam h0 hpi B M
  refine ⟨N,C,hC,?_⟩
  intro n L hL Q hQ Y R
  exact hInv n Q L Y R (hN L hL Q hQ)

/-- A two-sided inverse of the actual scaled reference Jacobian implies
nonsingularity of its actual unscaled Gaudin matrix. -/
theorem referenceGaudin_det_ne_zero_of_scaled_inverse {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (hi : referenceScaledGaudin lam h0 hpi Q L Y*referenceGaudinInverse lam h0 hpi Q L Y=1) :
    (gaudinMatrix lam (fun _ => 0) L Y).det ≠ 0 := by
  have hs : Function.Surjective (referenceScaledGaudin lam h0 hpi Q L Y) := by
    intro z
    refine ⟨referenceGaudinInverse lam h0 hpi Q L Y z,?_⟩
    exact congrArg (fun T : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => T z) hi
  have hg : Function.Surjective (gaudinCLM lam (fun _ => 0) L Y) := by
    intro z
    obtain ⟨v,hv⟩ := hs z
    exact ⟨referenceInverseDensityOperator lam h0 hpi Q L Y v,hv⟩
  have hu : IsUnit (gaudinMatrix lam (fun _ => 0) L Y) := Matrix.mulVec_surjective_iff_isUnit.mp hg
  exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det _).mp hu)

/-- In particular the actual finite reference Gaudin matrices are
nonsingular uniformly for all sufficiently large bounded-cutoff data. -/
theorem bounded_cutoff_referenceGaudin_det_ne_zero_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (B : ℝ) :
    ∃ N : ℕ,∀ (n L : ℕ),N ≤ L → ∀ Q : ℝ,Q ≤ B →
      ∀ (Y : Fin n → ℝ),ReferenceQuantileData lam h0 hpi Q L Y →
        (gaudinMatrix lam (fun _ => 0) L Y).det ≠ 0 := by
  obtain ⟨N,C,hC,hInv⟩ := bounded_cutoff_referenceGaudin_inverse_all lam h0 hpi B
  refine ⟨N,?_⟩
  intro n L hL Q hQ Y R
  exact referenceGaudin_det_ne_zero_of_scaled_inverse lam h0 hpi Q L Y (hInv n L hL Q hQ Y R).2.1

/-- The manuscript's full-line boundary-density threshold implies a
uniform inverse for the actual reference Jacobian, including diverging
cutoffs and both physical kernel signs. -/
theorem exists_referenceGaudin_inverse_boundary_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ D K : ℝ,0 < D ∧ 0 < K ∧ ∀ (n L : ℕ) (Q : ℝ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      D ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      referenceGaudinInverse lam h0 hpi Q L Y*referenceScaledGaudin lam h0 hpi Q L Y=1 ∧
      referenceScaledGaudin lam h0 hpi Q L Y*referenceGaudinInverse lam h0 hpi Q L Y=1 ∧
      ‖referenceGaudinInverse lam h0 hpi Q L Y‖ ≤ K := by
  obtain ⟨c,C,hc,hC,hcomp⟩ := exists_uniform_finiteInterval_comparison lam h0 hpi
  obtain ⟨M,K,hM,hK,hInv⟩ := exists_uniform_referenceGaudin_inverse_all lam h0 hpi
  refine ⟨M/c,K,div_pos hM hc,hK,?_⟩
  intro n L Q Y R hboundary
  apply hInv n Q L Y R
  intro u hu
  have hr := fullLineDensityFunction_radiallyAntitone_all lam h0 hpi u Q
    (by rw [abs_of_nonneg R.interval_nonneg]; exact abs_le.mpr hu)
  have hlo : c*fullLineDensityFunction lam h0 hpi Q ≤ finiteIntervalDensity lam h0 hpi Q u :=
    (mul_le_mul_of_nonneg_left hr hc.le).trans (hcomp Q R.interval_nonneg u (abs_le.mpr hu)).1
  have hm := (div_le_iff₀ hc).mp hboundary
  calc
    M ≤ ((L : ℝ)*fullLineDensityFunction lam h0 hpi Q)*c := hm
    _ = (L : ℝ)*(c*fullLineDensityFunction lam h0 hpi Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg L)

end
end SixVertex
