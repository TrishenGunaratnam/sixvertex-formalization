import SixVertex.KernelTailProfile

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Uniform local linear growth of the actual counting density for bounded
real site arrays. The positive source contribution alone gives the bound. -/
theorem exists_local_counting_density_growth (lam : ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (R B : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ),
      (∀ a ∈ Finset.range L, |b a| ≤ B) → ∀ u : ℝ, |u| ≤ R →
        d*(L : ℝ) ≤ countingSlope lam b L Y u := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let d : ℝ := (Real.sin lam/(2*Real.pi))*Real.exp (-2*(R+B))
  have hs := kernelS_positive_tail_data lam h0 hpi
  refine ⟨d,mul_pos hs.lower_pos (Real.exp_pos _),?_⟩
  intro n b L Y hb u hu
  have hlo (a : ℕ) (ha : a ∈ Finset.range L) : d ≤ kernelS lam (u-b a) := by
    have hab : |u-b a| ≤ R+B := (abs_sub u (b a)).trans (add_le_add hu (hb a ha))
    apply le_trans _ (hs.lower (u-b a))
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hs.lower_pos.le
  have hk : (∑ j : Fin n, kernelK lam (u-Y j)) ≤ 0 :=
    Finset.sum_nonpos (fun j _ => kernelK_nonpos lam _ hhalf hpi)
  have hsum := Finset.sum_le_sum hlo
  have hsum' : d*(L : ℝ) ≤ ∑ a ∈ Finset.range L, kernelS lam (u-b a) := by
    simpa only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,mul_comm] using hsum
  unfold countingSlope
  linarith

end
end SixVertex
