import SixVertex.ArraySiteCounting
import SixVertex.KernelTailProfile

namespace SixVertex
noncomputable section
open Set

/-- The actual bare source sum has density of order1/d throughout the
finite bulk of the equally spaced site array. -/
theorem exists_array_site_source_lower_bound (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ c : ℝ, 0 < c ∧ ∀ (L : ℕ) (d : ℝ), 0 < d → d ≤ 1 → ∀ u : ℝ,
      |u|+1 ≤ (L : ℝ)*d/4 → c/d ≤ ∑ a ∈ Finset.range L, kernelS lam (u-arraySite L d a) := by
  have hs := kernelS_positive_tail_data lam h0 hpi
  let c : ℝ := (Real.sin lam/(2*Real.pi))*Real.exp (-2)
  have hc : 0 < c := mul_pos hs.lower_pos (Real.exp_pos _)
  have hmin (x : ℝ) (hx : |x| ≤ 1) : c ≤ kernelS lam x := by
    apply le_trans _ (hs.lower x)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hs.lower_pos.le
  refine ⟨c,hc,?_⟩
  intro L d hd hd1 u hspan
  let Y : Fin L → ℝ := fun j => arraySite L d j.val
  have hp (j : Fin L) :
      c*((Ici (Y j)).indicator (fun _ : ℝ => (1 : ℝ)) (u+1)-
        (Ici (Y j)).indicator (fun _ : ℝ => (1 : ℝ)) (u-1)) ≤ kernelS lam (u-Y j) := by
    simp only [Set.indicator,Set.mem_Ici]
    by_cases ha : Y j ≤ u-1
    · have hz : Y j ≤ u+1 := by linarith
      simp only [ha,hz,ite_true,sub_self,mul_zero]
      exact (kernelS_pos lam _ h0 hpi).le
    · by_cases hz : Y j ≤ u+1
      · simp only [ha,hz,ite_true,ite_false,sub_zero,mul_one]
        apply hmin
        exact abs_le.mpr ⟨by linarith,by linarith⟩
      · simp only [ha,hz,ite_false,sub_self,mul_zero]
        exact (kernelS_pos lam _ h0 hpi).le
  have hsum := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin L))) => hp j)
  have hi : (∑ j : Fin L, c*((Ici (Y j)).indicator (fun _ : ℝ => (1 : ℝ)) (u+1)-
        (Ici (Y j)).indicator (fun _ : ℝ => (1 : ℝ)) (u-1)))=
      c*((rootCountLe Y (u+1) : ℝ)-(rootCountLe Y (u-1) : ℝ)) := by
    rw [rootCountLe_eq_sum_indicators,rootCountLe_eq_sum_indicators,← Finset.sum_sub_distrib,Finset.mul_sum]
  rw [hi] at hsum
  have hsource : (∑ j : Fin L, kernelS lam (u-Y j))=
      ∑ a ∈ Finset.range L, kernelS lam (u-arraySite L d a) :=
    Fin.sum_univ_eq_sum_range (fun a => kernelS lam (u-arraySite L d a)) L
  rw [hsource] at hsum
  have hcount := arraySite_unit_window_count L d hd hd1 u hspan
  calc
    _ = c*(1/d) := by ring
    _ ≤ c*((rootCountLe Y (u+1) : ℝ)-(rootCountLe Y (u-1) : ℝ)) :=
      mul_le_mul_of_nonneg_left hcount hc.le
    _ ≤ _ := hsum

/-- Negative interactions can only increase the actual counting density,
so the grid lower bound is uniform in every finite root configuration. -/
theorem exists_array_counting_density_lower (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n L : ℕ) (d : ℝ), 0 < d → d ≤ 1 → ∀ (Z : Fin n → ℝ) (u : ℝ),
      |u|+1 ≤ (L : ℝ)*d/4 → c/d ≤ countingSlope lam (arraySite L d) L Z u := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  obtain ⟨c,hc,hsource⟩ := exists_array_site_source_lower_bound lam h0 hpi
  refine ⟨c,hc,?_⟩
  intro n L d hd hd1 Z u hspan
  have hs := hsource L d hd hd1 u hspan
  have hk : (∑ j : Fin n, kernelK lam (u-Z j)) ≤ 0 :=
    Finset.sum_nonpos (fun j _ => kernelK_nonpos lam _ hhalf hpi)
  unfold countingSlope
  linarith

end
end SixVertex
