import SixVertex.PhysicalAtomWeights

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- Exact interval mass for the existing actual atomic measure whenever
its genuine inverse-counting-density weights are nonnegative. -/
theorem rootQuadratureMeasure_Icc_of_density_nonneg {n : ℕ} (lam : ℝ) (b : ℕ → ℝ)
    (L : ℕ) (X : Fin n → ℝ) (hpos : ∀ j,0 ≤ countingSlope lam b L X (X j)) (a z : ℝ) :
    rootQuadratureMeasure lam b L X (Icc a z)=
      ENNReal.ofReal (∑ j ∈ rootsInInterval X a z,(countingSlope lam b L X (X j))⁻¹) := by
  have hp (j : Fin n) : 0 ≤ (countingSlope lam b L X (X j))⁻¹ := inv_nonneg.mpr (hpos j)
  rw [rootQuadratureMeasure,Measure.sum_apply_of_countable,tsum_fintype,
    ENNReal.ofReal_sum_of_nonneg (fun j _ => hp j)]
  simp only [Measure.smul_apply,smul_eq_mul,Measure.dirac_apply' _ measurableSet_Icc]
  rw [rootsInInterval,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : a ≤ X j ∧ X j ≤ z
  · rw [if_pos hj,Set.indicator_of_mem (show X j ∈ Icc a z from hj)]
    simp
  · rw [if_neg hj,Set.indicator_of_notMem (show X j ∉ Icc a z from hj)]
    simp

/-- Exact integration against the existing actual atomic measure,with
its signs verified at the actual root coordinates. -/
theorem integral_rootQuadratureMeasure_of_density_nonneg {n : ℕ} (lam : ℝ) (b : ℕ → ℝ)
    (L : ℕ) (X : Fin n → ℝ) (hpos : ∀ j,0 ≤ countingSlope lam b L X (X j)) (phi : ℝ → ℝ) :
    (∫ x,phi x ∂rootQuadratureMeasure lam b L X)=
      ∑ j : Fin n,phi (X j)/countingSlope lam b L X (X j) := by
  unfold rootQuadratureMeasure
  rw [integral_sum_dirac (fun _ => ENNReal.ofReal_ne_top),tsum_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [ENNReal.toReal_ofReal (inv_nonneg.mpr (hpos j))]
  simp only [smul_eq_mul,div_eq_mul_inv,mul_comm]

/-- The actual inverse-counting-density measure has uniformly bounded
mass on every unit interval throughout the physical range,including
moving sparse-edge intervals,near the actual reference configurations. -/
theorem exists_weighted_configuration_unit_quadrature_mass_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius : ℝ) (hrad : 0 ≤ radius) :
    ∃ M B : ℝ,0 < M ∧ 0 < B ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) →
      (∀ j,0 < countingSlope lam (fun _ => 0) L X (X j)) ∧
      ∀ a : ℝ,rootQuadratureMeasure lam (fun _ => 0) L X (Icc a (a+1)) ≤ ENNReal.ofReal B := by
  obtain ⟨M,C,hM,hC,hcomp⟩ := exists_weighted_root_atom_comparison_all lam h0 hpi radius hrad
  let delta := radius/M
  let len := 1+2*delta
  let E := Real.exp (physicalDensityLogConstant lam*len)
  let B := 2*(E^2*len+E/M)
  have hd : 0 ≤ delta := div_nonneg hrad hM.le
  have hlen : 0 < len := by dsimp [len]; linarith
  have hE : 0 < E := Real.exp_pos _
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨M,B,hM,hB,?_⟩
  intro n Q L Y X R hlower hclose
  have hw (j : Fin n) : 0 < (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j) :=
    hM.trans_le (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩)
  have hpoint := hcomp n Q L Y X R hlower hclose
  refine ⟨fun j => (hpoint j).1,?_⟩
  intro a
  have hphysical (j : Fin n) : |X j-Y j| ≤ delta := (hclose j).trans
    (div_le_div₀ hrad le_rfl hM (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩))
  have hsub : rootsInInterval X a (a+1) ⊆ rootsInInterval Y (a-delta) (a+1+delta) := by
    intro j hj
    have hx := (Finset.mem_filter.mp hj).2
    have he := abs_le.mp (hphysical j)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
  have href := reference_weighted_interval_mass_bound_all lam h0 hpi Q L Y R M hM hlower
    (a-delta) (a+1+delta) (by linarith)
  have hlen_eq : (a+1+delta)-(a-delta)=len := by dsimp [len]; ring
  rw [hlen_eq] at href
  rw [rootQuadratureMeasure_Icc_of_density_nonneg lam (fun _ => 0) L X (fun j => (hpoint j).1.le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ j ∈ rootsInInterval X a (a+1),2/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) :=
      Finset.sum_le_sum (fun j _ => (hpoint j).2.1)
    _ = 2*(∑ j ∈ rootsInInterval X a (a+1),((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))⁻¹) := by
      simp only [div_eq_mul_inv,Finset.mul_sum]
    _ ≤ 2*(∑ j ∈ rootsInInterval Y (a-delta) (a+1+delta),((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => inv_nonneg.mpr (hw j).le)
    _ ≤ _ := mul_le_mul_of_nonneg_left href (by norm_num)

end
end SixVertex
