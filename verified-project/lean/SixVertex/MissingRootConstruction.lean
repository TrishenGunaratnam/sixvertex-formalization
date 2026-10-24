import SixVertex.BoundaryMassDeficit
import SixVertex.HomogeneousRootConstruction

namespace SixVertex
noncomputable section
open Set Filter Topology

/-- Actual root construction whenever the number of missing roots from
half filling diverges. The cutoff may tend to infinity. -/
theorem eventual_missing_root_construction (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ radius C : ℝ, 0 < radius ∧ 0 ≤ C ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ),
      (∀ i, 0 < L i) → (∀ i, 0 ≤ Q i) →
      (∀ i, (L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto (fun i => (L i : ℝ)/2-(n i : ℝ)) l atTop →
      ∀ᶠ i in l, ∃ Y Z : Fin (n i) → ℝ, ReferenceQuantileData lam h0 hpi (Q i) (L i) Y ∧
        ConsecutiveRoots lam (fun _ => 0) (L i) Z 0 ∧
        (∀ j, (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y j)*|Z j-Y j| ≤ radius) ∧
        ∀ u : ℝ, |countingSlope lam (fun _ => 0) (L i) Z u-(L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u| ≤ C := by
  obtain ⟨radius,C,hrad,hC,hcorr⟩ := eventual_negative_kernel_homogeneous_roots lam h0 hhalf.le hpi
  refine ⟨radius,C,hrad,hC,?_⟩
  intro ι l n L Q hL hQ hmass hholes
  have he (i : ι) : (L i : ℝ)*(1/2-finiteIntervalMass lam h0 hpi (Q i))=(L i : ℝ)/2-(n i : ℝ) := by
    nlinarith only [hmass i]
  have hm : Tendsto (fun i => (L i : ℝ)*(1/2-finiteIntervalMass lam h0 hpi (Q i))) l atTop :=
    hholes.congr' (Eventually.of_forall (fun i => (he i).symm))
  exact hcorr l n L Q hL hQ hmass (boundary_density_dense_of_missing_mass lam h0 hhalf hpi l L Q hQ hm)

end
end SixVertex
