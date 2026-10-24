import SixVertex.FiniteCountingOrder
import SixVertex.KernelTailProfile
import SixVertex.WindowComparison
import SixVertex.GlobalRootExistence

namespace SixVertex
noncomputable section
open Set

/-- A local derivative lower bound gives a lower phase increment. -/
theorem countingS_increment_lower (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (B d : ℝ) (hlo : ∀ u ∈ Icc (-B) B, d ≤ kernelS lam u)
    (x y : ℝ) (hx : x ∈ Icc (-B) B) (hy : y ∈ Icc (-B) B) (hxy : x ≤ y) :
    d*(y-x) ≤ countingS lam y-countingS lam x := by
  have hd : Differentiable ℝ (countingS lam) := fun u => (hasDerivAt_countingS lam u h0 hpi).differentiableAt
  apply (convex_Icc (-B) B).mul_sub_le_image_sub_of_le_deriv hd.continuous.continuousOn hd.differentiableOn _ x hx y hy hxy
  intro u hu
  rw [(hasDerivAt_countingS lam u h0 hpi).deriv]
  exact hlo u (interior_subset hu)

/-- A bounded reference residual yields an actual root bracket once the
bare phase increases enough across the proposed displacement. -/
theorem homogeneous_roots_residual_bracket {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (L : ℕ) (hL : 0 < L)
    (Y Z : Fin n → ℝ) (twist B d E t : ℝ)
    (hY : ∀ i, |Y i| ≤ B) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hd : ∀ u ∈ Icc (-(B+1)) (B+1), d ≤ kernelS lam u)
    (hEt : E ≤ (L : ℝ)*d*t)
    (hres : ∀ i, |countingSystem lam (fun _ => 0) L Y i-countingTarget n twist i| ≤ E)
    (hZ : countingSystem lam (fun _ => 0) L Z=countingTarget n twist) :
    ∀ i, |Z i-Y i| ≤ t := by
  apply homogeneous_roots_bracket lam hhalf hpi L hL Y Z twist t hZ
  · intro i
    have hy := abs_le.mp (hY i)
    have hinc := countingS_increment_lower lam h0 hpi (B+1) d hd (Y i-t) (Y i)
      ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩ (by linarith)
    have hi := (abs_le.mp (hres i)).2
    have hincL := mul_le_mul_of_nonneg_left hinc (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    have htrans := homogeneous_countingSystem_translate lam L Y (-t) i
    simp only [← sub_eq_add_neg] at htrans
    rw [htrans]
    nlinarith
  · intro i
    have hy := abs_le.mp (hY i)
    have hinc := countingS_increment_lower lam h0 hpi (B+1) d hd (Y i) (Y i+t)
      ⟨by linarith,by linarith⟩ ⟨by linarith,by linarith⟩ (by linarith)
    have hi := (abs_le.mp (hres i)).1
    have hincL := mul_le_mul_of_nonneg_left hinc (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    rw [homogeneous_countingSystem_translate]
    nlinarith

/-- Uniform physical O(1/L) correction from actual reference quantiles
to any exact homogeneous roots, for all bounded reference cutoffs. -/
theorem bounded_cutoff_reference_root_displacement (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (B : ℝ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (n L : ℕ), N ≤ L → ∀ Q : ℝ, Q ≤ B →
      ∀ (Y Z : Fin n → ℝ) (R : ReferenceQuantileData lam h0 hpi Q L Y),
      countingSystem lam (fun _ => 0) L Z=countingTarget n 0 →
        ∀ i, |Z i-Y i| ≤ C/(L : ℝ) := by
  have hs := kernelS_positive_tail_data lam h0 hpi
  let d : ℝ := (Real.sin lam/(2*Real.pi))*Real.exp (-2*(B+1))
  have hdp : 0 < d := mul_pos hs.lower_pos (Real.exp_pos _)
  have hd : ∀ u ∈ Icc (-(B+1)) (B+1), d ≤ kernelS lam u := by
    intro u hu
    have hab : |u| ≤ B+1 := abs_le.mpr hu
    apply le_trans _ (hs.lower u)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hs.lower_pos.le
  let E := kernelL1Mass (kernelK lam)/2
  let C := E/d
  have hE : 0 ≤ E := div_nonneg (kernelL1Mass_nonneg _) (by norm_num)
  have hC : 0 ≤ C := div_nonneg hE hdp.le
  obtain ⟨N,hN⟩ := exists_nat_gt C
  refine ⟨N,C,hC,?_⟩
  intro n L hNL Q hQB Y Z R hZ
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr R.chain_pos
  have hCL : C ≤ (L : ℝ) := (hN.trans_le (Nat.cast_le.mpr hNL)).le
  apply homogeneous_roots_residual_bracket lam h0 hhalf hpi L R.chain_pos Y Z 0 B d E (C/(L : ℝ))
    (fun i => abs_le.mpr ⟨by linarith [(R.location i).1],by linarith [(R.location i).2]⟩)
    (div_nonneg hC hLp.le) ((div_le_one hLp).mpr hCL) hd
  · dsimp [C]
    field_simp
    exact le_refl _
  · intro i
    have hh := norm_le_pi_norm (countingSystem lam (fun _ => 0) L Y-countingTarget n 0) i
    have hh' : |countingSystem lam (fun _ => 0) L Y i-countingTarget n 0 i| ≤
        ‖countingSystem lam (fun _ => 0) L Y-countingTarget n 0‖ := by
      simpa only [Real.norm_eq_abs,Pi.sub_apply] using hh
    apply hh'.trans
    change ‖countingSystem lam (fun _ => 0) L Y-countingTarget n 0‖ ≤ kernelL1Mass (kernelK lam)/2
    rw [kernelL1Mass,integral_abs_kernelK lam h0 hpi]
    exact reference_bethe_residual_norm lam h0 hhalf hpi Q L Y R
  · exact hZ

/-- The actual root correction is bounded in the manuscript's density
scaled displacement coordinates, uniformly for bounded cutoffs. -/
theorem bounded_cutoff_reference_weighted_displacement (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (B : ℝ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (n L : ℕ), N ≤ L → ∀ Q : ℝ, Q ≤ B →
      ∀ (Y Z : Fin n → ℝ) (R : ReferenceQuantileData lam h0 hpi Q L Y),
      countingSystem lam (fun _ => 0) L Z=countingTarget n 0 →
        ∀ i, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)*|Z i-Y i| ≤ C := by
  obtain ⟨N,C,hC,hbound⟩ := bounded_cutoff_reference_root_displacement lam h0 hhalf hpi B
  let A := ‖fullLineDensityFunction lam h0 hpi‖
  have hA : 0 ≤ A := norm_nonneg _
  refine ⟨N,A*C,mul_nonneg hA hC,?_⟩
  intro n L hL Q hQ Y Z R hZ i
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr R.chain_pos
  have hr : finiteIntervalDensity lam h0 hpi Q (Y i) ≤ A :=
    (finiteIntervalDensity_le_fullLineDensity lam h0 hhalf hpi Q (Y i)).trans
      ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using (fullLineDensityFunction lam h0 hpi).norm_coe_le_norm (Y i)))
  have hd := hbound n L hL Q hQ Y Z R hZ i
  calc
    _ ≤ (L : ℝ)*A*(C/(L : ℝ)) := mul_le_mul
      (mul_le_mul_of_nonneg_left hr hLp.le) hd (abs_nonneg _) (mul_nonneg hLp.le hA)
    _ = _ := by field_simp [hLp.ne']

/-- Exact roots exist within a uniformly bounded density-scaled
displacement of the constructed quantiles in every bounded cutoff window. -/
theorem exists_bounded_cutoff_reference_root_correction (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (B : ℝ) :
    ∃ N : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (n L : ℕ), N ≤ L → ∀ Q : ℝ, Q ≤ B →
      ∀ (Y : Fin n → ℝ) (R : ReferenceQuantileData lam h0 hpi Q L Y),
      ∃ Z : Fin n → ℝ, ConsecutiveRoots lam (fun _ => 0) L Z 0 ∧
        ∀ i, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)*|Z i-Y i| ≤ C := by
  obtain ⟨N,C,hC,hbound⟩ := bounded_cutoff_reference_weighted_displacement lam h0 hhalf hpi B
  refine ⟨N,C,hC,?_⟩
  intro n L hL Q hQ Y R
  have hmass := mul_lt_mul_of_pos_left (finiteIntervalMass_lt_half lam h0 hhalf hpi Q)
    (Nat.cast_pos.mpr R.chain_pos : (0 : ℝ) < L)
  rw [R.mass] at hmass
  have hfillR : (2 : ℝ)*(n : ℝ) ≤ (L : ℝ) := by linarith
  have hfill : 2*n ≤ L := by exact_mod_cast hfillR
  obtain ⟨Z,hZ,_⟩ := exists_unique_nonpositiveKernel_roots lam (fun _ => 0) L R.chain_pos hhalf hpi n hfill
  exact ⟨Z,hZ,hbound n L hL Q hQ Y Z R hZ.2⟩

end
end SixVertex
