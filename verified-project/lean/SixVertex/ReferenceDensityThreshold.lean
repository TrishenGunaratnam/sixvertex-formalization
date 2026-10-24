import SixVertex.ReferenceGaudin
import SixVertex.KernelTailProfile

namespace SixVertex
noncomputable section
open Set

/-- The actual finite-interval density has one positive lower bound on
all windows with bounded endpoints, derived from the bare source. -/
theorem exists_bounded_window_density_lower (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (B : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ Q : ℝ, Q ≤ B → ∀ u ∈ Icc (-Q) Q,
      d ≤ finiteIntervalDensity lam h0 hpi Q u := by
  let d := (Real.sin lam/(2*Real.pi))*Real.exp (-2*B)
  have hs := kernelS_positive_tail_data lam h0 hpi
  refine ⟨d,mul_pos hs.lower_pos (Real.exp_pos _),?_⟩
  intro Q hQB u hu
  have hab : |u| ≤ B := abs_le.mpr ⟨by linarith [hu.1],hu.2.trans hQB⟩
  apply le_trans _ (finiteIntervalDensity_ge_source lam h0 hhalf hpi Q u)
  apply le_trans _ (hs.lower u)
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hs.lower_pos.le

/-- For bounded cutoffs, every fixed scaled-density threshold is
reached uniformly as chain length increases. -/
theorem exists_bounded_window_scaled_density_threshold (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (B M : ℝ) :
    ∃ N : ℕ, ∀ L : ℕ, N ≤ L → ∀ Q : ℝ, Q ≤ B → ∀ u ∈ Icc (-Q) Q,
      M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u := by
  obtain ⟨d,hd,hlo⟩ := exists_bounded_window_density_lower lam h0 hhalf hpi B
  obtain ⟨N,hN⟩ := exists_nat_gt (M/d)
  refine ⟨N,?_⟩
  intro L hL Q hQ u hu
  have hNL : (N : ℝ) ≤ L := Nat.cast_le.mpr hL
  have hML : M ≤ (L : ℝ)*d := by
    have hh := (div_lt_iff₀ hd).mp (hN.trans_le hNL)
    exact hh.le
  exact hML.trans (mul_le_mul_of_nonneg_left (hlo Q hQ u hu) (Nat.cast_nonneg L))

/-- Actual reference Gaudin inverses are uniformly bounded in the
regular-filling, bounded-cutoff regime. No density estimate is assumed. -/
theorem bounded_cutoff_referenceGaudin_inverse (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (B : ℝ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (n L : ℕ), N ≤ L → ∀ Q : ℝ, Q ≤ B →
      ∀ (Y : Fin n → ℝ) (R : ReferenceQuantileData lam h0 hpi Q L Y),
      referenceGaudinInverse lam h0 hpi Q L Y*referenceScaledGaudin lam h0 hpi Q L Y=1 ∧
      referenceScaledGaudin lam h0 hpi Q L Y*referenceGaudinInverse lam h0 hpi Q L Y=1 ∧
      ‖referenceGaudinInverse lam h0 hpi Q L Y‖ ≤ C := by
  obtain ⟨M,C,hM,hC,hInv⟩ := exists_uniform_referenceGaudin_inverse lam h0 hhalf hpi
  obtain ⟨N,hN⟩ := exists_bounded_window_scaled_density_threshold lam h0 hhalf hpi B M
  refine ⟨N,C,hC,?_⟩
  intro n L hL Q hQ Y R
  exact hInv n Q L Y R (hN L hL Q hQ)

end
end SixVertex
