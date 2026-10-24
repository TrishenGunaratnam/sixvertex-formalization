import SixVertex.EdgeIndexDensity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Comparison of the inward tail at adjacent roots. Every inward
center lies on the positive side of both tail arguments. -/
theorem exists_inward_tail_shift_constant (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ A : ℝ, 0 < A ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ), 0 < L → L=2*n →
      ∀ (Y : Fin n → ℝ), StrictMono Y → ∀ i j : Fin n, j.val=i.val+1 →
        (∀ a ∈ Finset.range L, b a ≤ Y i) →
          inwardCountingTail lam b L Y j ≤ A*Real.exp (-2*(Y j-Y i))*(∫ v in Ioi (Y i), countingSlope lam b L Y v) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let cS := Real.sin lam/(2*Real.pi)
  let CS := 2/(Real.pi*(Real.sin (lam/2))^2)
  let cK := |Real.sin (2*lam)|/(2*Real.pi)
  let CK := 2/(Real.pi*(Real.sin lam)^2)
  have hs : PositiveKernelTailData (kernelS lam) cS CS := kernelS_positive_tail_data lam h0 hpi
  have hk : PositiveKernelTailData (fun u => -kernelK lam u) cK CK := negative_kernel_positive_tail_data lam hhalf hpi
  let A : ℝ := max (CS/cS) (CK/cK)
  have hA : 0 < A := lt_max_of_lt_left (div_pos hs.upper_pos hs.lower_pos)
  refine ⟨A,hA,?_⟩
  intro n b L hL hfill Y hY i j hji hcenters
  have hij : i < j := by change i.val < j.val; omega
  have hg : 0 ≤ Y j-Y i := sub_nonneg.mpr (hY hij).le
  let F : ℝ := A*Real.exp (-2*(Y j-Y i))
  have hF : 0 ≤ F := mul_nonneg hA.le (Real.exp_pos _).le
  have hSbound (a : ℕ) (ha : a ∈ Finset.range L) :
      kernelTail (kernelS lam) (Y j-b a) ≤ F*kernelTail (kernelS lam) (Y i-b a) := by
    have hh := hs.shift_bound (Y i-b a) (Y j-Y i) (sub_nonneg.mpr (hcenters a ha)) hg
    rw [show Y i-b a+(Y j-Y i)=Y j-b a by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
      (kernelTail_nonneg _ hs.nonnegative _))
  have hKbound (k : Fin n) (hkidx : k ∈ Finset.Iio j) :
      kernelTail (fun v => -kernelK lam v) (Y j-Y k) ≤ F*kernelTail (fun v => -kernelK lam v) (Y i-Y k) := by
    have hki : k ≤ i := by
      have hh := Finset.mem_Iio.mp hkidx
      change k.val ≤ i.val
      have hh' : k.val < j.val := hh
      omega
    have hh := hk.shift_bound (Y i-Y k) (Y j-Y i) (sub_nonneg.mpr (hY.monotone hki)) hg
    rw [show Y i-Y k+(Y j-Y i)=Y j-Y k by ring] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le)
      (kernelTail_nonneg _ hk.nonnegative _))
  have hsubset : (∑ k ∈ Finset.Iio j, kernelTail (fun v => -kernelK lam v) (Y i-Y k)) ≤
      ∑ k : Fin n, kernelTail (fun v => -kernelK lam v) (Y i-Y k) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun k _ _ => kernelTail_nonneg _ hk.nonnegative _)
  unfold inwardCountingTail
  calc
    _ ≤ (∑ a ∈ Finset.range L, F*kernelTail (kernelS lam) (Y i-b a))+
        ∑ k ∈ Finset.Iio j, F*kernelTail (fun v => -kernelK lam v) (Y i-Y k) :=
      add_le_add (Finset.sum_le_sum hSbound) (Finset.sum_le_sum hKbound)
    _ = F*((∑ a ∈ Finset.range L, kernelTail (kernelS lam) (Y i-b a))+
        ∑ k ∈ Finset.Iio j, kernelTail (fun v => -kernelK lam v) (Y i-Y k)) := by
      rw [← Finset.mul_sum,← Finset.mul_sum,mul_add]
    _ ≤ F*((∑ a ∈ Finset.range L, kernelTail (kernelS lam) (Y i-b a))+
        ∑ k : Fin n, kernelTail (fun v => -kernelK lam v) (Y i-Y k)) :=
      mul_le_mul_of_nonneg_left (add_le_add le_rfl hsubset) hF
    _ = _ := by rw [countingTail_decomposition lam b L hL hfill Y hhalf.le hpi (Y i)]

/-- Adjacent sparse terminal roots have a uniform upper gap once the
inner one lies beyond every bare center. -/
theorem exists_adjacent_edge_gap_upper (lam : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ), 0 < L → L=2*n →
      ∀ (Y : Fin n → ℝ), ConsecutiveRoots lam b L Y 0 → ∀ i j : Fin n, j.val=i.val+1 →
        (∀ a ∈ Finset.range L, b a ≤ Y i) → Y j-Y i ≤ C := by
  obtain ⟨A,hA,hshift⟩ := exists_inward_tail_shift_constant lam hhalf hpi
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hm : 0 < 1-kernelL1Mass (kernelK lam) := sub_pos.mpr (kernelK_L1_mass_lt_one lam h0 hpi)
  let B : ℝ := 3*A/(1-kernelL1Mass (kernelK lam))
  have hB : 0 < B := div_pos (mul_pos (by norm_num) hA) hm
  refine ⟨|Real.log B|/2+1,by positivity,?_⟩
  intro n b L hL hfill Y hroots i j hji hcenters
  have hl := inwardCountingTail_lower lam b L hL hfill Y hhalf.le hpi hroots j
  have hu := hshift n b L hL hfill Y hroots.1 i j hji hcenters
  rw [countingTail_at_root lam b L hL hfill Y hhalf.le hpi hroots i] at hu
  have hjpos : 0 < (n : ℝ)-(j.val : ℝ)-1/2 := by
    have hh : (j.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    linarith
  have hcast : (j.val : ℝ)=(i.val : ℝ)+1 := by exact_mod_cast hji
  have hratio : (n : ℝ)-(i.val : ℝ)-1/2 ≤ 3*((n : ℝ)-(j.val : ℝ)-1/2) := by
    have hh : (j.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    linarith
  have hscale : 0 ≤ A*Real.exp (-2*(Y j-Y i)) := mul_nonneg hA.le (Real.exp_pos _).le
  have hh := hl.trans (hu.trans (mul_le_mul_of_nonneg_left hratio hscale))
  have hbasic : 1-kernelL1Mass (kernelK lam) ≤ 3*A*Real.exp (-2*(Y j-Y i)) := by
    apply (mul_le_mul_iff_right₀ hjpos).mp
    nlinarith only [hh]
  have hmultiply := mul_le_mul_of_nonneg_right hbasic (Real.exp_pos (2*(Y j-Y i))).le
  have hex : Real.exp (-2*(Y j-Y i))*Real.exp (2*(Y j-Y i))=1 := by
    rw [← Real.exp_add,show -2*(Y j-Y i)+2*(Y j-Y i)=0 by ring,Real.exp_zero]
  have hExp : Real.exp (2*(Y j-Y i)) ≤ B := by
    apply (le_div_iff₀ hm).mpr
    have hp : (3*A*Real.exp (-2*(Y j-Y i)))*Real.exp (2*(Y j-Y i))=3*A := by rw [mul_assoc,hex,mul_one]
    rw [hp] at hmultiply
    nlinarith only [hmultiply]
  have hlog := (Real.le_log_iff_exp_le hB).mpr hExp
  linarith [le_abs_self (Real.log B)]

end
end SixVertex
