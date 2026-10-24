import SixVertex.StrictFillingMass
import SixVertex.HomogeneousRootConstruction

namespace SixVertex
noncomputable section
open Set Filter Topology

/-- At fixed filling below half, the actual boundary density multiplied
by chain length diverges. No assumed cutoff bound is needed. -/
theorem regular_filling_boundary_dense {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (l : Filter ι) (L : ι → ℕ) (Q : ι → ℝ)
    (hQ : ∀ i, 0 ≤ Q i) (hL : Tendsto L l atTop) (rho : ℝ) (hrho : rho < 1/2)
    (hfill : Tendsto (fun i => finiteIntervalMass lam h0 hpi (Q i)) l (𝓝 rho)) :
    Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop := by
  obtain ⟨B,hB,hQB⟩ := finiteIntervalCutoff_eventually_bounded lam h0 hhalf hpi Q l rho hrho hfill
  have hrB := fullLineDensityFunction_pos lam h0 hhalf hpi B
  have hcast : Tendsto (fun i => (L i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hL
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [hQB,hcast.eventually (eventually_ge_atTop (a/fullLineDensityFunction lam h0 hpi B))] with i hi hLi
  have hr : fullLineDensityFunction lam h0 hpi B ≤ fullLineDensityFunction lam h0 hpi (Q i) := by
    apply fullLineDensityFunction_radiallyAntitone lam h0 hhalf hpi (Q i) B
    rw [abs_of_nonneg (hQ i),abs_of_nonneg hB]
    exact hi
  exact ((div_le_iff₀ hrB).mp hLi).trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (L i)))

/-- The negative-kernel regular-filling root construction, with exact
finite mass selection and the paper's n/L filling convention. -/
theorem eventual_regular_filling_roots (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    ∃ radius C : ℝ, 0 < radius ∧ 0 ≤ C ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ) (rho : ℝ), rho < 1/2 →
      (∀ i, 0 < L i) → (∀ i, 0 ≤ Q i) →
      (∀ i, (L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto L l atTop → Tendsto (fun i => (n i : ℝ)/(L i : ℝ)) l (𝓝 rho) →
      ∀ᶠ i in l, ∃ Y Z : Fin (n i) → ℝ, ReferenceQuantileData lam h0 hpi (Q i) (L i) Y ∧
        ConsecutiveRoots lam (fun _ => 0) (L i) Z 0 ∧
        (∀ j, (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y j)*|Z j-Y j| ≤ radius) ∧
        ∀ u : ℝ, |countingSlope lam (fun _ => 0) (L i) Z u-(L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u| ≤ C := by
  obtain ⟨radius,C,hrad,hC,hcorr⟩ := eventual_negative_kernel_homogeneous_roots lam h0 hhalf hpi
  refine ⟨radius,C,hrad,hC,?_⟩
  intro ι l n L Q rho hrho hLpos hQ hmass hLinf hfill
  have hm (i : ι) : (n i : ℝ)/(L i : ℝ)=finiteIntervalMass lam h0 hpi (Q i) := by
    apply (div_eq_iff (Nat.cast_pos.mpr (hLpos i)).ne').mpr
    nlinarith only [hmass i]
  have hfillM : Tendsto (fun i => finiteIntervalMass lam h0 hpi (Q i)) l (𝓝 rho) :=
    hfill.congr' (Eventually.of_forall hm)
  exact hcorr l n L Q hLpos hQ hmass (regular_filling_boundary_dense lam h0 hhalf hpi l L Q hQ hLinf rho hrho hfillM)

end
end SixVertex
