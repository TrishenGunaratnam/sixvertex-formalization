import SixVertex.ReferenceShiftDrift
import SixVertex.CorrectedRootDensity

namespace SixVertex
noncomputable section
open Set

/-- Exact homogeneous roots are uniformly close to the actual reference
quantiles in density-scaled coordinates. The threshold precedes every Q. -/
theorem uniform_reference_weighted_root_displacement (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ M radius : ℝ, 0 < M ∧ 0 < radius ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y Z : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) →
      countingSystem lam (fun _ => 0) L Z=countingTarget n 0 →
        ∀ i, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)*|Z i-Y i| ≤ radius := by
  let h := kernelL1Mass (kernelK lam)
  let delta := (1-h)/2
  let E := h/2
  let radius : ℝ := 1+E/delta
  have hh : h < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  have hh0 : 0 ≤ h := kernelL1Mass_nonneg _
  have hd : 0 < delta := by dsimp [delta]; linarith
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hrad : 0 < radius := by dsimp [radius]; positivity
  have hradE : E ≤ delta*radius := by
    dsimp [radius]
    have he : delta*(1+E/delta)=delta+E := by field_simp
    rw [he]
    linarith
  obtain ⟨M,hM,hdrift⟩ := exists_uniform_referenceShift_drift lam h0 hhalf hpi radius hrad.le
  refine ⟨M,radius,hM,hrad,?_⟩
  intro n Q L Y Z R hlower hZ
  let F : ℝ → Fin n → ℝ := fun t => countingSystem lam (fun _ => 0) L (referenceShift lam h0 hpi Q L Y t)
  have hF0 : F 0=countingSystem lam (fun _ => 0) L Y := by
    change countingSystem lam (fun _ => 0) L (fun j => Y j+0/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))=_
    simp only [zero_div,add_zero]
  have hdF (t : ℝ) (i : Fin n) := referenceShift_counting_hasDerivAt lam h0 hpi Q L Y t i
  have hinc (i : Fin n) (a b : ℝ) (ha : a ∈ Icc (-radius) radius) (hb : b ∈ Icc (-radius) radius) (hab : a ≤ b) :
      delta*(b-a) ≤ F b i-F a i := by
    have hdif : Differentiable ℝ (fun t => F t i) := fun t => (hdF t i).differentiableAt
    apply (convex_Icc (-radius) radius).mul_sub_le_image_sub_of_le_deriv hdif.continuous.continuousOn hdif.differentiableOn _ a ha b hb hab
    intro t ht
    rw [(hdF t i).deriv]
    exact hdrift n Q L Y R hlower t (interior_subset ht) i
  have hres (i : Fin n) : |F 0 i-countingTarget n 0 i| ≤ E := by
    rw [hF0]
    have hn := norm_le_pi_norm (countingSystem lam (fun _ => 0) L Y-countingTarget n 0) i
    have he : ‖countingSystem lam (fun _ => 0) L Y-countingTarget n 0‖ ≤ E := by
      change ‖countingSystem lam (fun _ => 0) L Y-countingTarget n 0‖ ≤ kernelL1Mass (kernelK lam)/2
      rw [kernelL1Mass,integral_abs_kernelK lam h0 hpi]
      exact reference_bethe_residual_norm lam h0 hhalf hpi Q L Y R
    exact (by simpa only [Pi.sub_apply,Real.norm_eq_abs] using hn :
      |countingSystem lam (fun _ => 0) L Y i-countingTarget n 0 i| ≤ ‖countingSystem lam (fun _ => 0) L Y-countingTarget n 0‖).trans he
  have hzero : (0 : ℝ) ∈ Icc (-radius) radius := ⟨by linarith,hrad.le⟩
  have hlo : ∀ i, F (-radius) i ≤ countingTarget n 0 i := by
    intro i
    have hi := hinc i (-radius) 0 ⟨le_refl _,by linarith⟩ hzero (by linarith)
    have hr := (abs_le.mp (hres i)).2
    linarith
  have hhi : ∀ i, countingTarget n 0 i ≤ F radius i := by
    intro i
    have hi := hinc i 0 radius hzero ⟨by linarith,le_refl _⟩ hrad.le
    have hr := (abs_le.mp (hres i)).1
    linarith
  have hlow := homogeneous_countingSystem_order_reflecting lam hhalf hpi L R.chain_pos
    (referenceShift lam h0 hpi Q L Y (-radius)) Z (fun i => by rw [hZ]; exact hlo i)
  have hhigh := homogeneous_countingSystem_order_reflecting lam hhalf hpi L R.chain_pos
    Z (referenceShift lam h0 hpi Q L Y radius) (fun i => by rw [hZ]; exact hhi i)
  intro i
  let w := (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)
  have hwp : 0 < w := mul_pos (Nat.cast_pos.mpr R.chain_pos) (finiteIntervalDensity_pos lam h0 hhalf hpi Q (Y i))
  have hlowi : Y i+(-radius)/w ≤ Z i := hlow i
  have hhighi : Z i ≤ Y i+radius/w := hhigh i
  have hbound : |Z i-Y i| ≤ radius/w := abs_le.mpr ⟨by rw [neg_div] at hlowi; linarith,by linarith⟩
  exact (mul_le_mul_of_nonneg_left hbound hwp.le).trans_eq (by field_simp [hwp.ne'])

/-- Actual ordered roots with a uniform weighted correction exist once
the true reference density is large, with no bounded-cutoff hypothesis. -/
theorem exists_uniform_reference_root_correction (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ M radius : ℝ, 0 < M ∧ 0 < radius ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v) →
      ∃ Z : Fin n → ℝ, ConsecutiveRoots lam (fun _ => 0) L Z 0 ∧
        ∀ i, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)*|Z i-Y i| ≤ radius := by
  obtain ⟨M,radius,hM,hrad,hbound⟩ := uniform_reference_weighted_root_displacement lam h0 hhalf hpi
  refine ⟨M,radius,hM,hrad,?_⟩
  intro n Q L Y R hlower
  have hf := ReferenceQuantileData.subhalf_filling lam h0 hhalf hpi Q L Y R
  obtain ⟨Z,hZ,_⟩ := exists_unique_nonpositiveKernel_roots lam (fun _ => 0) L R.chain_pos hhalf hpi n hf.le
  exact ⟨Z,hZ,hbound n Q L Y Z R hlower hZ.2⟩

end
end SixVertex
