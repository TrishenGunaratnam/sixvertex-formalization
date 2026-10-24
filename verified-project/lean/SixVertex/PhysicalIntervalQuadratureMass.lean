import SixVertex.PhysicalActualQuadrature

namespace SixVertex
noncomputable section
open Set MeasureTheory

/-- Actual inverse-counting-density mass is uniformly bounded on every
interval of a prescribed fixed length,including moving edge intervals. -/
theorem exists_weighted_configuration_interval_quadrature_mass_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius ell : ℝ) (hrad : 0 ≤ radius) (hell : 0 ≤ ell) :
    ∃ M B : ℝ,0 < M ∧ 0 < B ∧ ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) →
      (∀ j,0 < countingSlope lam (fun _ => 0) L X (X j)) ∧
      ∀ a : ℝ,rootQuadratureMeasure lam (fun _ => 0) L X (Icc a (a+ell)) ≤ ENNReal.ofReal B := by
  obtain ⟨M,C,hM,hC,hcomp⟩ := exists_weighted_root_atom_comparison_all lam h0 hpi radius hrad
  let delta := radius/M
  let len := ell+2*delta
  let E := Real.exp (physicalDensityLogConstant lam*len)
  let B := 2*(E^2*len+E/M)
  have hd : 0 ≤ delta := div_nonneg hrad hM.le
  have hlen : 0 ≤ len := by dsimp [len]; positivity
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
  have hsub : rootsInInterval X a (a+ell) ⊆ rootsInInterval Y (a-delta) (a+ell+delta) := by
    intro j hj
    have hx := (Finset.mem_filter.mp hj).2
    have he := abs_le.mp (hphysical j)
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,⟨by linarith [hx.1],by linarith [hx.2]⟩⟩
  have href := reference_weighted_interval_mass_bound_all lam h0 hpi Q L Y R M hM hlower
    (a-delta) (a+ell+delta) (by linarith)
  have hlen_eq : (a+ell+delta)-(a-delta)=len := by dsimp [len]; ring
  rw [hlen_eq] at href
  rw [rootQuadratureMeasure_Icc_of_density_nonneg lam (fun _ => 0) L X (fun j => (hpoint j).1.le)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ ∑ j ∈ rootsInInterval X a (a+ell),2/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) :=
      Finset.sum_le_sum (fun j _ => (hpoint j).2.1)
    _ = 2*(∑ j ∈ rootsInInterval X a (a+ell),((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))⁻¹) := by
      simp only [div_eq_mul_inv,Finset.mul_sum]
    _ ≤ 2*(∑ j ∈ rootsInInterval Y (a-delta) (a+ell+delta),((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))⁻¹) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j _ _ => inv_nonneg.mpr (hw j).le)
    _ ≤ _ := mul_le_mul_of_nonneg_left href (by norm_num)

end
end SixVertex
