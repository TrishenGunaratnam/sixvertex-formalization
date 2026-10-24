import SixVertex.EdgeIndexDensity

namespace SixVertex
noncomputable section

/-- The reciprocal density at every fixed right-edge index is bounded
above and below by constants times the inverse index. These are the
actual weights required for one-sided edge extraction. -/
theorem exists_edge_reciprocal_density_constants (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ a A : ℝ, 0 < a ∧ 0 < A ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ), 0 < L → L=2*n →
      ∀ (Y : Fin n → ℝ), ConsecutiveRoots lam b L Y 0 → ∀ j : Fin n,
        (∀ k ∈ Finset.range L, b k ≤ Y j) →
          a/((n : ℝ)-(j.val : ℝ)) ≤ (countingSlope lam b L Y (Y j))⁻¹ ∧
            (countingSlope lam b L Y (Y j))⁻¹ ≤ A/((n : ℝ)-(j.val : ℝ)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := exists_edge_index_density_constants lam hhalf hpi
  refine ⟨1/C,2/c,one_div_pos.mpr hC,div_pos (by norm_num) hc,?_⟩
  intro n b L hL hfill Y hroots j hcenters
  have hb := hbound n b L hL hfill Y hroots j hcenters
  let N : ℝ := (n : ℝ)-(j.val : ℝ)
  have hN1 : 1 ≤ N := by
    have hh : (j.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    dsimp [N]
    linarith
  have hN : 0 < N := lt_of_lt_of_le (by norm_num) hN1
  have hrho : 0 < countingSlope lam b L Y (Y j) :=
    countingSlope_pos_nonpositiveK lam b L hL Y (Y j) hhalf.le hpi
  have hup : countingSlope lam b L Y (Y j) ≤ C*N := hb.2.trans
    (mul_le_mul_of_nonneg_left (by dsimp [N]; linarith : (n : ℝ)-(j.val : ℝ)-1/2 ≤ N) hC.le)
  have hlo : (c/2)*N ≤ countingSlope lam b L Y (Y j) := by
    have hh := mul_le_mul_of_nonneg_left (by linarith : N/2 ≤ N-1/2) hc.le
    have hh1 := hb.1
    dsimp [N] at hh
    nlinarith only [hh1,hh]
  change (1/C)/N ≤ (countingSlope lam b L Y (Y j))⁻¹ ∧
    (countingSlope lam b L Y (Y j))⁻¹ ≤ (2/c)/N
  constructor
  · have hi := one_div_le_one_div_of_le hrho hup
    calc
      _ = (1 : ℝ)/(C*N) := by field_simp [hC.ne',hN.ne']
      _ ≤ _ := by simpa only [one_div] using hi
  · have hi := one_div_le_one_div_of_le (mul_pos (div_pos hc (by norm_num)) hN) hlo
    calc
      _ ≤ (1 : ℝ)/((c/2)*N) := by simpa only [one_div] using hi
      _ = _ := by field_simp [hc.ne',hN.ne']

end
end SixVertex
