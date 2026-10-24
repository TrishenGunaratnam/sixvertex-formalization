import SixVertex.ReferenceRootStability

namespace SixVertex
noncomputable section
open Set

/-- A global Lipschitz constant for the actual interaction kernel. -/
theorem kernelK_global_lipschitz_bound (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (u v : ℝ) :
    |kernelK lam v-kernelK lam u| ≤ ‖physicalKernelPrimeFunction lam h0 hpi‖*|v-u| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (univ : Set ℝ)) => (hasDerivAt_kernelK lam x h0 hpi).hasDerivWithinAt)
    (fun x (_ : x ∈ (univ : Set ℝ)) => by
      exact (physicalKernelPrimeFunction lam h0 hpi).norm_coe_le_norm x)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ u) (mem_univ v)
  simpa only [Real.norm_eq_abs] using h

/-- Counting-density variation caused by a uniform physical displacement. -/
theorem countingSlope_displacement_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y Z : Fin n → ℝ) (t : ℝ)
    (ht : ∀ j, |Z j-Y j| ≤ t) (u : ℝ) :
    |countingSlope lam b L Z u-countingSlope lam b L Y u| ≤
      (n : ℝ)*‖physicalKernelPrimeFunction lam h0 hpi‖*t := by
  have hid : countingSlope lam b L Z u-countingSlope lam b L Y u=
      -(∑ j : Fin n, (kernelK lam (u-Z j)-kernelK lam (u-Y j))) := by
    unfold countingSlope
    rw [Finset.sum_sub_distrib]
    ring
  rw [hid,abs_neg]
  calc
    _ ≤ ∑ j : Fin n, |kernelK lam (u-Z j)-kernelK lam (u-Y j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j : Fin n, ‖physicalKernelPrimeFunction lam h0 hpi‖*t := by
      apply Finset.sum_le_sum
      intro j _
      have he := kernelK_global_lipschitz_bound lam h0 hpi (u-Y j) (u-Z j)
      have heq : (u-Z j)-(u-Y j)=-(Z j-Y j) := by ring
      rw [heq,abs_neg] at he
      exact he.trans (mul_le_mul_of_nonneg_left (ht j) (norm_nonneg _))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]; ring

/-- The constructed reference data itself forces sub-half filling. -/
theorem ReferenceQuantileData.subhalf_filling {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) : 2*n < L := by
  have hh := mul_lt_mul_of_pos_left (finiteIntervalMass_lt_half lam h0 hhalf hpi Q)
    (Nat.cast_pos.mpr R.chain_pos : (0 : ℝ) < L)
  rw [R.mass] at hh
  have hf : (2 : ℝ)*(n : ℝ) < (L : ℝ) := by linarith
  exact_mod_cast hf

/-- The actual corrected root density is L*r_Q+O(1) on the entire line,
uniformly over bounded cutoffs and all finite reference configurations. -/
theorem bounded_cutoff_corrected_density_error (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (B : ℝ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (n L : ℕ), N ≤ L → ∀ Q : ℝ, Q ≤ B →
      ∀ (Y Z : Fin n → ℝ) (R : ReferenceQuantileData lam h0 hpi Q L Y),
      countingSystem lam (fun _ => 0) L Z=countingTarget n 0 → ∀ u : ℝ,
        |countingSlope lam (fun _ => 0) L Z u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C := by
  obtain ⟨N,C,hC,hdis⟩ := bounded_cutoff_reference_root_displacement lam h0 hhalf hpi B
  let A := ‖physicalKernelPrimeFunction lam h0 hpi‖
  have hA : 0 ≤ A := norm_nonneg _
  let D := kernelL1Mass (kernelKPrime lam)/2
  have hD : 0 ≤ D := div_nonneg (kernelL1Mass_nonneg _) (by norm_num)
  refine ⟨N,A*C+D,add_nonneg (mul_nonneg hA hC) hD,?_⟩
  intro n L hL Q hQ Y Z R hZ u
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr R.chain_pos
  have hnL : n ≤ L := by have hf := ReferenceQuantileData.subhalf_filling lam h0 hhalf hpi Q L Y R; omega
  have hnLR : (n : ℝ) ≤ L := Nat.cast_le.mpr hnL
  have hvar : |countingSlope lam (fun _ => 0) L Z u-countingSlope lam (fun _ => 0) L Y u| ≤ A*C := by
    calc
      _ ≤ (n : ℝ)*A*(C/(L : ℝ)) := countingSlope_displacement_bound lam h0 hpi (fun _ => 0) L Y Z (C/(L : ℝ)) (hdis n L hL Q hQ Y Z R hZ) u
      _ ≤ (L : ℝ)*A*(C/(L : ℝ)) := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hnLR hA) (div_nonneg hC hLp.le)
      _ = _ := by field_simp [hLp.ne']
  have hid : countingSlope lam (fun _ => 0) L Z u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u=
      (countingSlope lam (fun _ => 0) L Z u-countingSlope lam (fun _ => 0) L Y u)+
        (countingSlope lam (fun _ => 0) L Y u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) := by ring
  rw [hid]
  exact (abs_add_le _ _).trans (add_le_add hvar (reference_density_uniform_error lam h0 hhalf hpi Q L Y R u))

end
end SixVertex
