import SixVertex.PhysicalUniformQuadrature
import SixVertex.PhysicalFillingConstruction

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal Matrix

/-- Joint conclusions about one actual root list. Each field refers to
the existing counting map,matrix and inverse-density atomic measure. -/
structure PhysicalRootMeasureData {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ) (radius C B D ell eps : ℝ) : Prop where
  roots : ConsecutiveRoots lam (fun _ => 0) L X 0
  weighted_close : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))
  density_error : ∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
    (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C
  nonsingular : (gaudinMatrix lam (fun _ => 0) L X).det ≠ 0
  atom_positive : ∀ j,0 < countingSlope lam (fun _ => 0) L X (X j)
  unit_mass : ∀ a : ℝ,rootQuadratureMeasure lam (fun _ => 0) L X (Icc a (a+1)) ≤ ENNReal.ofReal B
  twist_branch : ∃ psi : ℝ → Fin n → ℝ,psi 0=X ∧ AnalyticAt ℝ psi 0 ∧
    ∀ᶠ t in nhds 0,ConsecutiveRoots lam (fun _ => 0) L (psi t) t ∧ AnalyticAt ℝ psi t ∧
      gaudinMatrix lam (fun _ => 0) L (psi t) *ᵥ deriv psi t=(fun _ => 1/Real.pi)
  quadrature : ∀ (a N : ℝ),-Q ≤ a → a+ell ≤ Q → 0 < N →
    (∀ u ∈ Icc (a-eps) (a+ell+eps),N ≤ countingSlope lam (fun _ => 0) L X u) →
    ∀ (phi : BoundedRealFunction) (K : ℝ≥0),LipschitzWith K (fun x => phi x) →
    (∀ x,x ∉ Icc a (a+ell) → phi x=0) →
    |(∫ x,phi x ∂rootQuadratureMeasure lam (fun _ => 0) L X)-(∫ x : ℝ,phi x)| ≤
      (D/N)*((K : ℝ)+‖phi‖)

/-- One actual root list simultaneously satisfies the finite equations,
uniform root and density estimates,actual measure bounds and quadrature,
and a genuine analytic twist branch,throughout the physical range. -/
theorem exists_weighted_reference_root_measure_data_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (ell eps : ℝ) (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ M radius C B D : ℝ,0 < M ∧ 0 < radius ∧ 0 < C ∧ 0 < B ∧ 0 < D ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      ∃ X : Fin n → ℝ,PhysicalRootMeasureData lam h0 hpi Q L Y X radius C B D ell eps := by
  obtain ⟨mr,radius,C,hmr,hrad,hC,hroots⟩ := exists_weighted_reference_regular_roots_all lam h0 hpi
  obtain ⟨mm,B,hmm,hB,hmass⟩ := exists_weighted_configuration_unit_quadrature_mass_all lam h0 hpi radius hrad.le
  obtain ⟨mq,D,hmq,hD,hquad⟩ := exists_uniform_actual_density_quadrature_all lam h0 hpi radius ell eps hrad.le hell heps
  let M := max mr (max mm mq)
  have hM : 0 < M := hmr.trans_le (le_max_left _ _)
  have hr : mr ≤ M := le_max_left _ _
  have hm : mm ≤ M := (le_max_left _ _).trans (le_max_right _ _)
  have hq : mq ≤ M := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨M,radius,C,B,D,hM,hrad,hC,hB,hD,?_⟩
  intro n Q L Y R hlower
  obtain ⟨X,hX,hclose,hdens,hdet⟩ := hroots n Q L Y R (fun u hu => hr.trans (hlower u hu))
  have hmassX := hmass n Q L Y X R (fun u hu => hm.trans (hlower u hu)) hclose
  refine ⟨X, {
    roots := hX
    weighted_close := hclose
    density_error := hdens
    nonsingular := hdet
    atom_positive := hmassX.1
    unit_mass := hmassX.2
    twist_branch := ?_
    quadrature := ?_
  }⟩
  · exact exists_analytic_root_branch lam (fun _ => 0) L h0 hpi X 0 hX hdet
  · exact hquad n Q L Y X R (fun u hu => hq.trans (hlower u hu)) hclose

/-- The paper's boundary-density criterion supplies one actual root list
with all joint measure and analytic conclusions,including unbounded Q. -/
theorem exists_boundary_reference_root_measure_data_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (ell eps : ℝ) (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ T radius C B D : ℝ,0 < T ∧ 0 < radius ∧ 0 < C ∧ 0 < B ∧ 0 < D ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      T ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ∃ X : Fin n → ℝ,PhysicalRootMeasureData lam h0 hpi Q L Y X radius C B D ell eps := by
  obtain ⟨c,C',hc,hC',hcomp⟩ := exists_uniform_finiteInterval_comparison lam h0 hpi
  obtain ⟨M,radius,C,B,D,hM,hrad,hC,hB,hD,hroots⟩ := exists_weighted_reference_root_measure_data_all lam h0 hpi ell eps hell heps
  refine ⟨M/c,radius,C,B,D,div_pos hM hc,hrad,hC,hB,hD,?_⟩
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

/-- Finite mass data construct their own reference quantiles and actual
roots with all the joint measure estimates;no reference configuration
is supplied as an external hypothesis. -/
theorem physical_root_measure_construction_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (ell eps : ℝ) (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ T radius C B D : ℝ,0 < T ∧ 0 < radius ∧ 0 < C ∧ 0 < B ∧ 0 < D ∧
    ∀ (n L : ℕ) (Q : ℝ),0 < L → 0 ≤ Q →
      (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ) →
      T ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ∃ Y X : Fin n → ℝ,ReferenceQuantileData lam h0 hpi Q L Y ∧
        PhysicalRootMeasureData lam h0 hpi Q L Y X radius C B D ell eps := by
  obtain ⟨T,radius,C,B,D,hT,hrad,hC,hB,hD,hroots⟩ := exists_boundary_reference_root_measure_data_all lam h0 hpi ell eps hell heps
  refine ⟨T,radius,C,B,D,hT,hrad,hC,hB,hD,?_⟩
  intro n L Q hL hQ hmass hboundary
  obtain ⟨Y,hY,hlevel⟩ := exists_finiteInterval_midQuantiles_all lam h0 hpi Q hQ L n hL hmass
  have R : ReferenceQuantileData lam h0 hpi Q L Y :=
    ⟨hQ,hL,hmass,hY,(fun j => (hlevel j).1),(fun j => (hlevel j).2)⟩
  obtain ⟨X,hX⟩ := hroots n Q L Y R hboundary
  exact ⟨Y,X,R,hX⟩

/-- The joint actual root-measure construction applies eventually to
every mass-selected dense-boundary family,with all constants fixed
before that family and its finite root counts. -/
theorem eventual_physical_root_measure_data_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (ell eps : ℝ) (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ radius C B D : ℝ,0 < radius ∧ 0 < C ∧ 0 < B ∧ 0 < D ∧
    ∀ {ι : Type} (l : Filter ι) (n L : ι → ℕ) (Q : ι → ℝ),
      (∀ i,0 < L i) → (∀ i,0 ≤ Q i) →
      (∀ i,(L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop →
      ∀ᶠ i in l,∃ Y X : Fin (n i) → ℝ,ReferenceQuantileData lam h0 hpi (Q i) (L i) Y ∧
        PhysicalRootMeasureData lam h0 hpi (Q i) (L i) Y X radius C B D ell eps := by
  obtain ⟨T,radius,C,B,D,hT,hrad,hC,hB,hD,hroots⟩ := physical_root_measure_construction_all lam h0 hpi ell eps hell heps
  refine ⟨radius,C,B,D,hrad,hC,hB,hD,?_⟩
  intro ι l n L Q hL hQ hmass hdense
  filter_upwards [hdense.eventually (eventually_ge_atTop T)] with i hi
  exact hroots (n i) (L i) (Q i) (hL i) (hQ i) (hmass i) hi

/-- Actual root lists can be selected as families,not just pointwise
existence witnesses,and eventually share all the joint estimates. -/
theorem exists_physical_root_measure_families_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (ell eps : ℝ) (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ radius C B D : ℝ,0 < radius ∧ 0 < C ∧ 0 < B ∧ 0 < D ∧
    ∀ {ι : Type} (l : Filter ι) (n L : ι → ℕ) (Q : ι → ℝ),
      (∀ i,0 < L i) → (∀ i,0 ≤ Q i) →
      (∀ i,(L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop →
      ∃ Y X : (i : ι) → Fin (n i) → ℝ,
        ∀ᶠ i in l,ReferenceQuantileData lam h0 hpi (Q i) (L i) (Y i) ∧
          PhysicalRootMeasureData lam h0 hpi (Q i) (L i) (Y i) (X i) radius C B D ell eps := by
  classical
  obtain ⟨radius,C,B,D,hrad,hC,hB,hD,hroots⟩ := eventual_physical_root_measure_data_all lam h0 hpi ell eps hell heps
  refine ⟨radius,C,B,D,hrad,hC,hB,hD,?_⟩
  intro ι l n L Q hL hQ hmass hdense
  let P (i : ι) (w : (Fin (n i) → ℝ) × (Fin (n i) → ℝ)) : Prop :=
    ReferenceQuantileData lam h0 hpi (Q i) (L i) w.1 ∧
      PhysicalRootMeasureData lam h0 hpi (Q i) (L i) w.1 w.2 radius C B D ell eps
  let sol (i : ι) := Classical.epsilon (P i)
  refine ⟨(fun i => (sol i).1),(fun i => (sol i).2),?_⟩
  filter_upwards [hroots l n L Q hL hQ hmass hdense] with i hi
  obtain ⟨Y,X,hR,hX⟩ := hi
  exact Classical.epsilon_spec (show ∃ w,P i w from ⟨(Y,X),hR,hX⟩)

/-- The actual selected root measures converge locally to Lebesgue
measure in occupied windows whose actual counting density diverges. -/
theorem physical_root_measure_data_quadrature_tendsto {ι : Type} (lam : ℝ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (l : Filter ι)
    (n L : ι → ℕ) (Q : ι → ℝ) (Y X : (i : ι) → Fin (n i) → ℝ)
    (radius C B D ell eps a : ℝ) (N : ι → ℝ)
    (hdata : ∀ᶠ i in l,PhysicalRootMeasureData lam h0 hpi (Q i) (L i) (Y i) (X i) radius C B D ell eps)
    (hwindow : ∀ᶠ i in l,-(Q i) ≤ a ∧ a+ell ≤ Q i)
    (hN : Tendsto N l atTop)
    (hlocal : ∀ᶠ i in l,∀ u ∈ Icc (a-eps) (a+ell+eps),N i ≤ countingSlope lam (fun _ => 0) (L i) (X i) u)
    (phi : BoundedRealFunction) (K : ℝ≥0) (hLip : LipschitzWith K (fun x => phi x))
    (hs : ∀ x,x ∉ Icc a (a+ell) → phi x=0) :
    Tendsto (fun i => ∫ x,phi x ∂rootQuadratureMeasure lam (fun _ => 0) (L i) (X i))
      l (nhds (∫ x : ℝ,phi x)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun i => (D/N i)*((K : ℝ)+‖phi‖))
    (Eventually.of_forall (fun i => norm_nonneg _))
  · filter_upwards [hdata,hwindow,hlocal,hN.eventually (eventually_ge_atTop 1)] with i hdi hwi hli hNi
    rw [Real.norm_eq_abs]
    exact hdi.quadrature a (N i) hwi.1 hwi.2 (lt_of_lt_of_le zero_lt_one hNi) hli phi K hLip hs
  · simpa only [zero_mul] using (tendsto_const_nhds.div_atTop hN).mul_const ((K : ℝ)+‖phi‖)

/-- Uniform measure constants apply to every already-constructed dense
boundary family. The roots need not be reselected for a different test
window or enlargement. -/
theorem eventual_measure_data_of_boundary_dense_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (radius C ell eps : ℝ) (hrad : 0 ≤ radius)
    (hell : 0 ≤ ell) (heps : 0 < eps) :
    ∃ B D : ℝ,0 < B ∧ 0 < D ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ) (Y X : (i : ι) → Fin (n i) → ℝ),
      (∀ᶠ i in l,ReferenceQuantileData lam h0 hpi (Q i) (L i) (Y i) ∧
        ConsecutiveRoots lam (fun _ => 0) (L i) (X i) 0 ∧
        (∀ j,(L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y i j)*|X i j-Y i j| ≤ radius) ∧
        (∀ u : ℝ,|countingSlope lam (fun _ => 0) (L i) (X i) u-
          (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u| ≤ C) ∧
        (gaudinMatrix lam (fun _ => 0) (L i) (X i)).det ≠ 0) →
      Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop →
      ∀ᶠ i in l,PhysicalRootMeasureData lam h0 hpi (Q i) (L i) (Y i) (X i) radius C B D ell eps := by
  obtain ⟨mm,B,hmm,hB,hmass⟩ := exists_weighted_configuration_unit_quadrature_mass_all lam h0 hpi radius hrad
  obtain ⟨mq,D,hmq,hD,hquad⟩ := exists_uniform_actual_density_quadrature_all lam h0 hpi radius ell eps hrad hell heps
  obtain ⟨c,C',hc,hC',hcomp⟩ := exists_uniform_finiteInterval_comparison lam h0 hpi
  let M := max mm mq
  refine ⟨B,D,hB,hD,?_⟩
  intro ι l n L Q Y X hbase hdense
  filter_upwards [hbase,hdense.eventually (eventually_ge_atTop (M/c))] with i hi hbi
  obtain ⟨R,hX,hdis,hdens,hdet⟩ := hi
  have hlower : ∀ u ∈ Icc (-(Q i)) (Q i),M ≤ (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u := by
    intro u hu
    have hr := fullLineDensityFunction_radiallyAntitone_all lam h0 hpi u (Q i)
      (by rw [abs_of_nonneg R.interval_nonneg]; exact abs_le.mpr hu)
    have hlo : c*fullLineDensityFunction lam h0 hpi (Q i) ≤ finiteIntervalDensity lam h0 hpi (Q i) u :=
      (mul_le_mul_of_nonneg_left hr hc.le).trans (hcomp (Q i) R.interval_nonneg u (abs_le.mpr hu)).1
    have hm := (div_le_iff₀ hc).mp hbi
    calc
      M ≤ ((L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i))*c := hm
      _ = (L i : ℝ)*(c*fullLineDensityFunction lam h0 hpi (Q i)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (Nat.cast_nonneg (L i))
  have hclose (j : Fin (n i)) : |X i j-Y i j| ≤ radius/((L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (Y i j)) := by
    have hw := mul_pos (Nat.cast_pos.mpr R.chain_pos : (0 : ℝ) < L i)
      (finiteIntervalDensity_pos_all lam h0 hpi (Q i) (Y i j))
    apply (le_div_iff₀ hw).mpr
    simpa only [mul_comm] using hdis j
  have hm := hmass (n i) (Q i) (L i) (Y i) (X i) R
    (fun u hu => (le_max_left _ _).trans (hlower u hu)) hclose
  refine {
    roots := hX
    weighted_close := hclose
    density_error := hdens
    nonsingular := hdet
    atom_positive := hm.1
    unit_mass := hm.2
    twist_branch := ?_
    quadrature := ?_
  }
  · exact exists_analytic_root_branch lam (fun _ => 0) (L i) h0 hpi (X i) 0 hX hdet
  · exact hquad (n i) (Q i) (L i) (Y i) (X i) R
      (fun u hu => (le_max_right _ _).trans (hlower u hu)) hclose

/-- Select the actual root families once,before every compact test
window. Every fixed window then has uniform eventual mass,quadrature
and branch conclusions for those same selected roots. -/
theorem exists_universal_physical_root_measure_families_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ radius C : ℝ,0 < radius ∧ 0 < C ∧ ∀ {ι : Type} (l : Filter ι)
      (n L : ι → ℕ) (Q : ι → ℝ),
      (∀ i,0 < L i) → (∀ i,0 ≤ Q i) →
      (∀ i,(L i : ℝ)*finiteIntervalMass lam h0 hpi (Q i)=(n i : ℝ)) →
      Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop →
      ∃ Y X : (i : ι) → Fin (n i) → ℝ,
        (∀ᶠ i in l,ReferenceQuantileData lam h0 hpi (Q i) (L i) (Y i)) ∧
        ∀ (ell eps : ℝ),0 ≤ ell → 0 < eps → ∃ B D : ℝ,0 < B ∧ 0 < D ∧
          ∀ᶠ i in l,PhysicalRootMeasureData lam h0 hpi (Q i) (L i) (Y i) (X i) radius C B D ell eps := by
  classical
  obtain ⟨radius,C,hrad,hC,hroots⟩ := eventual_physical_homogeneous_roots lam h0 hpi
  refine ⟨radius,C,hrad,hC,?_⟩
  intro ι l n L Q hL hQ hmass hdense
  let P (i : ι) (w : (Fin (n i) → ℝ) × (Fin (n i) → ℝ)) : Prop :=
    ReferenceQuantileData lam h0 hpi (Q i) (L i) w.1 ∧
      ConsecutiveRoots lam (fun _ => 0) (L i) w.2 0 ∧
      (∀ j,(L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) (w.1 j)*|w.2 j-w.1 j| ≤ radius) ∧
      (∀ u : ℝ,|countingSlope lam (fun _ => 0) (L i) w.2 u-
        (L i : ℝ)*finiteIntervalDensity lam h0 hpi (Q i) u| ≤ C) ∧
      (gaudinMatrix lam (fun _ => 0) (L i) w.2).det ≠ 0
  let sol (i : ι) := Classical.epsilon (P i)
  let Y : (i : ι) → Fin (n i) → ℝ := fun i => (sol i).1
  let X : (i : ι) → Fin (n i) → ℝ := fun i => (sol i).2
  have hbase : ∀ᶠ i in l,P i (sol i) := by
    filter_upwards [hroots l n L Q hL hQ hmass hdense] with i hi
    obtain ⟨Y',X',hR,hX,hdis,hdens,hdet⟩ := hi
    exact Classical.epsilon_spec (show ∃ w,P i w from ⟨(Y',X'),hR,hX,hdis,hdens,hdet⟩)
  refine ⟨Y,X,hbase.mono (fun i hi => hi.1),?_⟩
  intro ell eps hell heps
  obtain ⟨B,D,hB,hD,hevent⟩ := eventual_measure_data_of_boundary_dense_all lam h0 hpi radius C ell eps hrad.le hell heps
  exact ⟨B,D,hB,hD,hevent l n L Q Y X hbase hdense⟩

end
end SixVertex
