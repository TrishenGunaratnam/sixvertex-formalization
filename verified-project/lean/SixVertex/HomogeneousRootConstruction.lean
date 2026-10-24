import SixVertex.ExitKernelComparison

namespace SixVertex
noncomputable section
open Set Filter Topology

/-- The paper's full-line boundary criterion supplies one actual
reference root-and-density correction, uniformly before all cutoffs. -/
theorem boundary_reference_root_and_density_correction (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ threshold radius C : ℝ, 0 < threshold ∧ 0 < radius ∧ 0 ≤ C ∧
      ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ), ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      threshold ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ∃ Z : Fin n → ℝ, ConsecutiveRoots lam (fun _ => 0) L Z 0 ∧
        (∀ i, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)*|Z i-Y i| ≤ radius) ∧
        ∀ u : ℝ, |countingSlope lam (fun _ => 0) L Z u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C := by
  obtain ⟨M,radius,C,hM,hrad,hC,hcorr⟩ := uniform_reference_root_and_density_correction lam h0 hhalf hpi
  let d := 1-kernelL1Mass (kernelK lam)
  have hd : 0 < d := sub_pos.mpr (kernelK_L1_mass_lt_one lam h0 hpi)
  refine ⟨M/d,radius,C,div_pos hM hd,hrad,hC,?_⟩
  intro n Q L Y R hboundary
  apply hcorr n Q L Y R
  intro u hu
  have hlow := mul_le_mul_of_nonneg_left
    (finiteIntervalDensity_boundary_lower lam h0 hhalf hpi Q R.interval_nonneg u hu)
    (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hMd : M ≤ ((L : ℝ)*fullLineDensityFunction lam h0 hpi Q)*d := (div_le_iff₀ hd).mp hboundary
  nlinarith only [hlow,hMd]

/-- Construct the actual quantiles and exact roots from a prescribed
finite filling mass. Every constant is fixed before n,L,Q. -/
theorem negative_kernel_homogeneous_root_construction (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ threshold radius C : ℝ, 0 < threshold ∧ 0 < radius ∧ 0 ≤ C ∧
      ∀ (n L : ℕ) (Q : ℝ), 0 < L → 0 ≤ Q →
      (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ) →
      threshold ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ∃ Y Z : Fin n → ℝ, ReferenceQuantileData lam h0 hpi Q L Y ∧
        ConsecutiveRoots lam (fun _ => 0) L Z 0 ∧
        (∀ i, (L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y i)*|Z i-Y i| ≤ radius) ∧
        ∀ u : ℝ, |countingSlope lam (fun _ => 0) L Z u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C := by
  obtain ⟨threshold,radius,C,hth,hrad,hC,hcorr⟩ := boundary_reference_root_and_density_correction lam h0 hhalf hpi
  refine ⟨threshold,radius,C,hth,hrad,hC,?_⟩
  intro n L Q hL hQ hmass hboundary
  obtain ⟨Y,hY,hlev⟩ := exists_finiteInterval_midQuantiles lam h0 hhalf hpi Q hQ L n hL hmass
  have R : ReferenceQuantileData lam h0 hpi Q L Y :=
    ⟨hQ,hL,hmass,hY,(fun j => (hlev j).1),(fun j => (hlev j).2)⟩
  obtain ⟨Z,hZ,hdis,hdens⟩ := hcorr n Q L Y R hboundary
  exact ⟨Y,Z,R,hZ,hdis,hdens⟩

/-- The constructed correction applies eventually to every dense-boundary
family, including cutoffs tending to infinity. -/
theorem eventual_negative_kernel_homogeneous_roots (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ radius C : ℝ, 0 < radius ∧ 0 ≤ C ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ),
      (∀ i, 0 < L i) → (∀ i, 0 ≤ Q i) →
      (∀ i, (L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop →
      ∀ᶠ i in l, ∃ Y Z : Fin (n i) → ℝ, ReferenceQuantileData lam h0 hpi (Q i) (L i) Y ∧
        ConsecutiveRoots lam (fun _ => 0) (L i) Z 0 ∧
        (∀ j, (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y j)*|Z j-Y j| ≤ radius) ∧
        ∀ u : ℝ, |countingSlope lam (fun _ => 0) (L i) Z u-(L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u| ≤ C := by
  obtain ⟨threshold,radius,C,_,hrad,hC,hcorr⟩ := negative_kernel_homogeneous_root_construction lam h0 hhalf hpi
  refine ⟨radius,C,hrad,hC,?_⟩
  intro ι l n L Q hL hQ hmass hdense
  filter_upwards [hdense.eventually (eventually_ge_atTop threshold)] with i hi
  exact hcorr (n i) (L i) (Q i) (hL i) (hQ i) (hmass i) hi

end
end SixVertex
