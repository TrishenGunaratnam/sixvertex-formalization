import SixVertex.PhysicalRegularRoots
import SixVertex.RegularFillingConstruction
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace SixVertex
noncomputable section
open Set Filter Topology

/-- The manuscript construction with prescribed actual finite mass,
including actual quantiles, ordered roots and nonsingularity, throughout
the physical range. -/
theorem physical_homogeneous_root_construction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ D radius C : ℝ,0 < D ∧ 0 < radius ∧ 0 < C ∧
    ∀ (n L : ℕ) (Q : ℝ),0 < L → 0 ≤ Q →
      (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ) →
      D ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ∃ Y X : Fin n → ℝ,ReferenceQuantileData lam h0 hpi Q L Y ∧
        ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        (∀ j,(L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)*|X j-Y j| ≤ radius) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
          (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) L X).det ≠ 0 := by
  obtain ⟨D,radius,C,hD,hrad,hC,hroots⟩ := exists_boundary_reference_regular_roots_all lam h0 hpi
  refine ⟨D,radius,C,hD,hrad,hC,?_⟩
  intro n L Q hL hQ hmass hboundary
  obtain ⟨Y,hY,hlevel⟩ := exists_finiteInterval_midQuantiles_all lam h0 hpi Q hQ L n hL hmass
  have R : ReferenceQuantileData lam h0 hpi Q L Y :=
    ⟨hQ,hL,hmass,hY,(fun j => (hlevel j).1),(fun j => (hlevel j).2)⟩
  obtain ⟨X,hX,hclose,hdens,hdet⟩ := hroots n Q L Y R hboundary
  refine ⟨Y,X,R,hX,?_,hdens,hdet⟩
  intro j
  have hw := mul_pos (Nat.cast_pos.mpr hL : (0 : ℝ) < L) (finiteIntervalDensity_pos_all lam h0 hpi Q (Y j))
  exact (mul_comm _ _).trans_le ((le_div_iff₀ hw).mp (hclose j))

/-- Every family satisfying the manuscript dense-boundary criterion has
eventual actual ordered roots with uniform density control and
nonsingular Gaudin matrices, for both kernel signs. -/
theorem eventual_physical_homogeneous_roots (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ radius C : ℝ,0 < radius ∧ 0 < C ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ),
      (∀ i,0 < L i) → (∀ i,0 ≤ Q i) →
      (∀ i,(L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop →
      ∀ᶠ i in l,∃ Y X : Fin (n i) → ℝ,ReferenceQuantileData lam h0 hpi (Q i) (L i) Y ∧
        ConsecutiveRoots lam (fun _ => 0) (L i) X 0 ∧
        (∀ j,(L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y j)*|X j-Y j| ≤ radius) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) (L i) X u-
          (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) (L i) X).det ≠ 0 := by
  obtain ⟨D,radius,C,hD,hrad,hC,hroots⟩ := physical_homogeneous_root_construction lam h0 hpi
  refine ⟨radius,C,hrad,hC,?_⟩
  intro ι l n L Q hL hQ hmass hdense
  filter_upwards [hdense.eventually (eventually_ge_atTop D)] with i hi
  exact hroots (n i) (L i) (Q i) (hL i) (hQ i) (hmass i) hi

/-- At fixed filling below half,the actual boundary density times L
diverges throughout the physical range; cutoff boundedness is derived
from the actual mass limit. -/
theorem regular_filling_boundary_dense_all {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (l : Filter ι) (L : ι → ℕ) (Q : ι → ℝ)
    (hQ : ∀ i,0 ≤ Q i) (hL : Tendsto L l atTop) (rho : ℝ) (hrho : rho < 1/2)
    (hfill : Tendsto (fun i => finiteIntervalMass lam h0 hpi (Q i)) l (nhds rho)) :
    Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop := by
  obtain ⟨B,hB,hQB⟩ := finiteIntervalCutoff_eventually_bounded_all lam h0 hpi Q l rho hrho hfill
  have hrB := fullLineDensityFunction_pos_all lam h0 hpi B
  have hcast : Tendsto (fun i => (L i : ℝ)) l atTop := tendsto_natCast_atTop_atTop.comp hL
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [hQB,hcast.eventually (eventually_ge_atTop (a/fullLineDensityFunction lam h0 hpi B))] with i hi hLi
  have hr : fullLineDensityFunction lam h0 hpi B ≤ fullLineDensityFunction lam h0 hpi (Q i) := by
    apply fullLineDensityFunction_radiallyAntitone_all lam h0 hpi (Q i) B
    rw [abs_of_nonneg (hQ i),abs_of_nonneg hB]
    exact hi
  exact ((div_le_iff₀ hrB).mp hLi).trans (mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (L i)))

/-- The all-physical regular-filling root construction uses exactly the
paper's n/L convention and the actual finite-window mass. -/
theorem eventual_regular_filling_roots_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ radius C : ℝ,0 < radius ∧ 0 < C ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ) (rho : ℝ),rho < 1/2 →
      (∀ i,0 < L i) → (∀ i,0 ≤ Q i) →
      (∀ i,(L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto L l atTop → Tendsto (fun i => (n i : ℝ)/(L i : ℝ)) l (nhds rho) →
      ∀ᶠ i in l,∃ Y X : Fin (n i) → ℝ,ReferenceQuantileData lam h0 hpi (Q i) (L i) Y ∧
        ConsecutiveRoots lam (fun _ => 0) (L i) X 0 ∧
        (∀ j,(L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y j)*|X j-Y j| ≤ radius) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) (L i) X u-
          (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) (L i) X).det ≠ 0 := by
  obtain ⟨radius,C,hrad,hC,hroots⟩ := eventual_physical_homogeneous_roots lam h0 hpi
  refine ⟨radius,C,hrad,hC,?_⟩
  intro ι l n L Q rho hrho hLpos hQ hmass hL hfill
  have hm (i : ι) : (n i : ℝ)/(L i : ℝ)=finiteIntervalMass lam h0 hpi (Q i) := by
    apply (div_eq_iff (Nat.cast_pos.mpr (hLpos i)).ne').mpr
    nlinarith only [hmass i]
  have hfillM : Tendsto (fun i => finiteIntervalMass lam h0 hpi (Q i)) l (nhds rho) :=
    hfill.congr' (Eventually.of_forall hm)
  exact hroots l n L Q hLpos hQ hmass
    (regular_filling_boundary_dense_all lam h0 hpi l L Q hQ hL rho hrho hfillM)

/-- The exact positive-power lower bound appearing in Lemma3.1 implies
eventual actual roots and their uniform estimates, including when Q
is unbounded. -/
theorem eventual_power_boundary_roots_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ radius C : ℝ,0 < radius ∧ 0 < C ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ) (a c : ℝ),0 < a → 0 < c →
      (∀ i,0 < L i) → (∀ i,0 ≤ Q i) →
      (∀ i,(L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto L l atTop →
      (∀ᶠ i in l,c*(L i : ℝ)^a ≤ (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) →
      ∀ᶠ i in l,∃ Y X : Fin (n i) → ℝ,ReferenceQuantileData lam h0 hpi (Q i) (L i) Y ∧
        ConsecutiveRoots lam (fun _ => 0) (L i) X 0 ∧
        (∀ j,(L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y j)*|X j-Y j| ≤ radius) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) (L i) X u-
          (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) (L i) X).det ≠ 0 := by
  obtain ⟨radius,C,hrad,hC,hroots⟩ := eventual_physical_homogeneous_roots lam h0 hpi
  refine ⟨radius,C,hrad,hC,?_⟩
  intro ι l n L Q a c ha hc hLpos hQ hmass hL hpower
  apply hroots l n L Q hLpos hQ hmass
  have hpow : Tendsto (fun i => (L i : ℝ)^a) l atTop :=
    (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop.comp hL)
  have hscale : Tendsto (fun i => c*(L i : ℝ)^a) l atTop :=
    (tendsto_const_mul_atTop_of_pos hc).mpr hpow
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hpower,hscale.eventually (eventually_ge_atTop b)] with i hi hbi
  exact hbi.trans hi

/-- The bounded-cutoff alternative of the paper gives actual roots
uniformly for all sufficiently large chains, without requiring a filling
limit or an assumed finite-Jacobian determinant. -/
theorem bounded_cutoff_physical_regular_roots_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (B : ℝ) :
    ∃ radius C : ℝ,∃ N : ℕ,0 < radius ∧ 0 < C ∧
    ∀ (n L : ℕ),N ≤ L → ∀ (Q : ℝ),Q ≤ B → ∀ Y : Fin n → ℝ,
      ReferenceQuantileData lam h0 hpi Q L Y →
      ∃ X : Fin n → ℝ,ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
          (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) L X).det ≠ 0 := by
  obtain ⟨M,radius,C,hM,hrad,hC,hroots⟩ := exists_weighted_reference_regular_roots_all lam h0 hpi
  obtain ⟨N,hN⟩ := exists_bounded_window_scaled_density_threshold_all lam h0 hpi B M
  refine ⟨radius,C,N,hrad,hC,?_⟩
  intro n L hL Q hQ Y R
  exact hroots n Q L Y R (hN L hL Q hQ)

end
end SixVertex
