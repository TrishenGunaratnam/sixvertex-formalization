import SixVertex.EdgeIndexDensity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem counting_adjacent_gap_mass {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0) (i j : Fin n) (hji : j.val=i.val+1) :
    (∫ v in Y i..Y j, countingSlope lam b L Y v)=1 := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun v _ => hasDerivAt_countingXi lam b L Y v h0 hpi)
    (countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi).intervalIntegrable]
  have hi : countingXi lam b L Y (Y i)=countingTarget n 0 i := congrFun hroots.2 i
  have hj : countingXi lam b L Y (Y j)=countingTarget n 0 j := congrFun hroots.2 j
  rw [hi,hj]
  have hc : (j.val : ℝ)=(i.val : ℝ)+1 := by exact_mod_cast hji
  unfold countingTarget
  rw [hc]
  ring

/-- Each fixed right-edge index has a positive lower gap uniformly
in all chain lengths and real arrays. No root lies beyond a bare
center as a hypothesis for this lower bound. -/
theorem exists_adjacent_root_gap_lower (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ D : ℝ, 0 < D ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ), 0 < L → L=2*n →
      ∀ (Y : Fin n → ℝ), ConsecutiveRoots lam b L Y 0 → ∀ i j : Fin n, j.val=i.val+1 →
        (D*((n : ℝ)-(i.val : ℝ)-1/2))⁻¹ ≤ Y j-Y i := by
  obtain ⟨D,hD,hbound⟩ := exists_countingSlope_tail_upper lam hhalf hpi
  refine ⟨D,hD,?_⟩
  intro n b L hL hfill Y hroots i j hji
  have hij : i < j := by change i.val < j.val; omega
  have hYij : Y i ≤ Y j := (hroots.1 hij).le
  have hT : 0 < (n : ℝ)-(i.val : ℝ)-1/2 := by
    have hh : (i.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt i.isLt
    linarith
  have hcoef : 0 < D*((n : ℝ)-(i.val : ℝ)-1/2) := mul_pos hD hT
  have hxi := (countingXi_strictMono_nonpositiveK lam b L hL Y hhalf.le hpi).monotone
  have hnode : countingXi lam b L Y (Y i)=countingTarget n 0 i := congrFun hroots.2 i
  have hpt (v : ℝ) (hv : v ∈ Icc (Y i) (Y j)) :
      countingSlope lam b L Y v ≤ D*((n : ℝ)-(i.val : ℝ)-1/2) := by
    have hb := hbound n b L hL hfill Y v
    have ht : (∫ w in Ioi v, countingSlope lam b L Y w) ≤ (n : ℝ)-(i.val : ℝ)-1/2 := by
      rw [integral_Ioi_countingSlope_half lam b L hL hfill Y hhalf.le hpi v]
      have hh := hxi hv.1
      rw [hnode] at hh
      unfold countingTarget at hh
      simp only [zero_div] at hh
      linarith
    exact hb.trans (mul_le_mul_of_nonneg_left ht hD.le)
  have hi := intervalIntegral.integral_mono_on hYij
    (countingSlope_integrable_nonpositiveK lam b L hL Y hhalf.le hpi).intervalIntegrable
    intervalIntegrable_const hpt
  rw [counting_adjacent_gap_mass lam b L hL Y hhalf.le hpi hroots i j hji,intervalIntegral.integral_const] at hi
  change 1 ≤ (Y j-Y i)*(D*((n : ℝ)-(i.val : ℝ)-1/2)) at hi
  apply (mul_le_mul_iff_left₀ hcoef).mp
  rw [inv_mul_cancel₀ hcoef.ne']
  nlinarith only [hi]

end
end SixVertex
