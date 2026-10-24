import SixVertex.PhysicalPerturbedGaudin

namespace SixVertex
noncomputable section
open Set Filter Topology
open scoped Matrix

/-- Actual ordered roots with weighted quantile control, uniform density
error and a nonsingular actual Gaudin matrix, for all physical lambda. -/
theorem exists_weighted_reference_regular_roots_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ M₀ radius C : ℝ,0 < M₀ ∧ 0 < radius ∧ 0 < C ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      ∃ X : Fin n → ℝ,ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
          (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) L X).det ≠ 0 := by
  obtain ⟨m,radius,C,hm,hrad,hC,hroots⟩ := exists_weighted_reference_roots_and_density_all lam h0 hpi
  obtain ⟨m',hm',hdet⟩ := exists_weighted_gaudin_nonsingularity_threshold_all lam h0 hpi radius hrad.le
  refine ⟨max m m',radius,C,hm.trans_le (le_max_left _ _),hrad,hC,?_⟩
  intro n Q L Y R hlower
  obtain ⟨X,hX,hclose,hdensity⟩ := hroots n Q L Y R
    (fun u hu => (le_max_left _ _).trans (hlower u hu))
  exact ⟨X,hX,hclose,hdensity,hdet n Q L Y X R
    (fun u hu => (le_max_right _ _).trans (hlower u hu)) hclose⟩

/-- The manuscript boundary-density criterion gives actual nonsingular
ordered roots, including unbounded continuum cutoffs. -/
theorem exists_boundary_reference_regular_roots_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ D radius C : ℝ,0 < D ∧ 0 < radius ∧ 0 < C ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      D ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ∃ X : Fin n → ℝ,ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
          (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) L X).det ≠ 0 := by
  obtain ⟨c,C',hc,hC',hcomp⟩ := exists_uniform_finiteInterval_comparison lam h0 hpi
  obtain ⟨M,radius,C,hM,hrad,hC,hroots⟩ := exists_weighted_reference_regular_roots_all lam h0 hpi
  refine ⟨M/c,radius,C,div_pos hM hc,hrad,hC,?_⟩
  intro n Q L Y R hboundary
  apply hroots n Q L Y R
  intro u hu
  have hr := fullLineDensityFunction_radiallyAntitone_all lam h0 hpi u Q
    (by rw [abs_of_nonneg R.interval_nonneg]; exact abs_le.mpr hu)
  have hlo : c*fullLineDensityFunction lam h0 hpi Q ≤ finiteIntervalDensity lam h0 hpi Q u :=
    (mul_le_mul_of_nonneg_left hr hc.le).trans (hcomp Q R.interval_nonneg u (abs_le.mpr hu)).1
  have hm := (div_le_iff₀ hc).mp hboundary
  calc
    M ≤ ((L : ℝ)*fullLineDensityFunction lam h0 hpi Q)*c := hm
    _ = (L : ℝ)*(c*fullLineDensityFunction lam h0 hpi Q) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg L)

/-- The actual homogeneous roots under the boundary-density criterion
have a genuine real-analytic twist branch, with the exact actual Gaudin
response identity at every sufficiently nearby twist. -/
theorem exists_boundary_reference_root_twist_branch_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ D radius C : ℝ,0 < D ∧ 0 < radius ∧ 0 < C ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      D ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ∃ (X : Fin n → ℝ) (ψ : ℝ → Fin n → ℝ),
        ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
          (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) L X).det ≠ 0 ∧
        ψ 0=X ∧ AnalyticAt ℝ ψ 0 ∧
        ∀ᶠ t in nhds 0,ConsecutiveRoots lam (fun _ => 0) L (ψ t) t ∧ AnalyticAt ℝ ψ t ∧
          gaudinMatrix lam (fun _ => 0) L (ψ t) *ᵥ deriv ψ t=(fun _ => 1/Real.pi) := by
  obtain ⟨D,radius,C,hD,hrad,hC,hroots⟩ := exists_boundary_reference_regular_roots_all lam h0 hpi
  refine ⟨D,radius,C,hD,hrad,hC,?_⟩
  intro n Q L Y R hboundary
  obtain ⟨X,hX,hclose,hdens,hdet⟩ := hroots n Q L Y R hboundary
  obtain ⟨ψ,hbase,hanalytic,hnear⟩ := exists_analytic_root_branch lam (fun _ => 0) L h0 hpi X 0 hX hdet
  exact ⟨X,ψ,hX,hclose,hdens,hdet,hbase,hanalytic,hnear⟩

end
end SixVertex
