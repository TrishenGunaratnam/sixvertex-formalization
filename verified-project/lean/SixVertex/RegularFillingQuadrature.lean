import SixVertex.ReferenceCountingWindow
import SixVertex.RegularFillingConstruction
import SixVertex.HalfFilledQuadrature

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal

/-- Uniform C/L bounded-Lipschitz quadrature on a compact interval
proved to be occupied by the actual corrected root configuration. -/
theorem exists_reference_window_quadrature_rate (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (A : ℝ) (hA : 0 < A) :
    ∃ threshold C : ℝ, ∃ N : ℕ, 0 < threshold ∧ 0 < C ∧
      ∀ (n L : ℕ) (Q : ℝ) (Y Z : Fin n → ℝ), ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      N ≤ L → A+1 ≤ Q → threshold ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ConsecutiveRoots lam (fun _ => 0) L Z 0 →
      ∀ phi : BoundedRealFunction, LipschitzWith 1 (fun x => phi x) → ‖phi‖ ≤ 1 →
      (∀ x, x ∉ Icc (-A) A → phi x=0) →
      |(∫ x, phi x ∂rootQuadratureMeasure lam (fun _ => 0) L Z)-(∫ x : ℝ, phi x)| ≤ C/(L : ℝ) := by
  obtain ⟨threshold,N,hth,hwindow⟩ := exists_reference_occupied_counting_window lam h0 hhalf hpi A hA.le
  obtain ⟨d,hd,hgrowth⟩ := exists_local_counting_density_growth lam hhalf hpi A 0
  let C : ℝ := A*(1+kernelLogConstant lam)/d
  have hC : 0 < C := div_pos (mul_pos hA (by linarith [kernelLogConstant_nonneg lam])) hd
  refine ⟨threshold,C,N,hth,hC,?_⟩
  intro n L Q Y Z R hL hQ hboundary hZ phi hLip hnorm hs
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr R.chain_pos
  have he := unit_bounded_lipschitz_quadrature_error lam (fun _ => 0) L R.chain_pos Z hhalf hpi hZ phi hLip hnorm
    (-A) A (d*(L : ℝ)) (by linarith) (mul_pos hd hLp) hs
    (fun x hx => hgrowth n (fun _ => 0) L Z (fun _ _ => by simp) x (abs_le.mpr hx))
    (hwindow n L Q Y Z R hL hQ hboundary hZ.2)
  apply he.trans_eq
  dsimp [C]
  field_simp [hd.ne',hLp.ne']
  ring

/-- Local convergence for every unit bounded-Lipschitz test when the
reference interval eventually contains its enlarged support and the
paper's boundary density grows. -/
theorem dense_reference_quadrature_tendsto {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (A : ℝ) (hA : 0 < A)
    (l : Filter ι) (n L : ι → ℕ) (Q : ι → ℝ) (Y Z : (i : ι) → Fin (n i) → ℝ)
    (R : ∀ i, ReferenceQuantileData lam h0 hpi (Q i) (L i) (Y i))
    (hZ : ∀ i, ConsecutiveRoots lam (fun _ => 0) (L i) (Z i) 0)
    (hL : Tendsto L l atTop) (hQ : ∀ᶠ i in l, A+1 ≤ Q i)
    (hdense : Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop)
    (phi : BoundedRealFunction) (hLip : LipschitzWith 1 (fun x => phi x)) (hnorm : ‖phi‖ ≤ 1)
    (hs : ∀ x, x ∉ Icc (-A) A → phi x=0) :
    Tendsto (fun i => ∫ x, phi x ∂rootQuadratureMeasure lam (fun _ => 0) (L i) (Z i))
      l (𝓝 (∫ x : ℝ, phi x)) := by
  obtain ⟨threshold,C,N,_,_,hbound⟩ := exists_reference_window_quadrature_rate lam h0 hhalf hpi A hA
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun i => C/(L i : ℝ)) (Eventually.of_forall (fun i => norm_nonneg _))
  · filter_upwards [hQ,hL.eventually (eventually_ge_atTop N),hdense.eventually (eventually_ge_atTop threshold)] with i hQi hLi hdi
    rw [Real.norm_eq_abs]
    exact hbound (n i) (L i) (Q i) (Y i) (Z i) (R i) hLi hQi hdi (hZ i) phi hLip hnorm hs
  · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hL)

/-- A filling limit above a fixed finite-window mass eventually selects
a cutoff beyond that window. -/
theorem finiteIntervalCutoff_eventually_ge {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (l : Filter ι) (Q : ι → ℝ)
    (B rho : ℝ) (hrho : finiteIntervalMass lam h0 hpi B < rho)
    (hfill : Tendsto (fun i => finiteIntervalMass lam h0 hpi (Q i)) l (𝓝 rho)) :
    ∀ᶠ i in l, B ≤ Q i := by
  filter_upwards [hfill.eventually (Ioi_mem_nhds hrho)] with i hi
  by_contra hn
  have hQi : Q i ≤ B := (lt_of_not_ge hn).le
  have hm := finiteIntervalMass_monotone lam h0 hhalf hpi hQi
  linarith

/-- The regular-filling quadrature limit on a compact interval, at all
fillings sufficiently close to half to contain that interval. -/
theorem regular_filling_quadrature_tendsto {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (A : ℝ) (hA : 0 < A)
    (l : Filter ι) (n L : ι → ℕ) (Q : ι → ℝ) (Y Z : (i : ι) → Fin (n i) → ℝ)
    (R : ∀ i, ReferenceQuantileData lam h0 hpi (Q i) (L i) (Y i))
    (hZ : ∀ i, ConsecutiveRoots lam (fun _ => 0) (L i) (Z i) 0)
    (hL : Tendsto L l atTop) (rho : ℝ) (hrho : rho < 1/2)
    (hwindow : finiteIntervalMass lam h0 hpi (A+1) < rho)
    (hfill : Tendsto (fun i => (n i : ℝ)/(L i : ℝ)) l (𝓝 rho))
    (phi : BoundedRealFunction) (hLip : LipschitzWith 1 (fun x => phi x)) (hnorm : ‖phi‖ ≤ 1)
    (hs : ∀ x, x ∉ Icc (-A) A → phi x=0) :
    Tendsto (fun i => ∫ x, phi x ∂rootQuadratureMeasure lam (fun _ => 0) (L i) (Z i))
      l (𝓝 (∫ x : ℝ, phi x)) := by
  have hm (i : ι) : (n i : ℝ)/(L i : ℝ)=finiteIntervalMass lam h0 hpi (Q i) := by
    apply (div_eq_iff (Nat.cast_pos.mpr (R i).chain_pos).ne').mpr
    nlinarith only [(R i).mass]
  have hfillM : Tendsto (fun i => finiteIntervalMass lam h0 hpi (Q i)) l (𝓝 rho) :=
    hfill.congr' (Eventually.of_forall hm)
  exact dense_reference_quadrature_tendsto lam h0 hhalf hpi A hA l n L Q Y Z R hZ hL
    (finiteIntervalCutoff_eventually_ge lam h0 hhalf hpi l Q (A+1) rho hwindow hfillM)
    (regular_filling_boundary_dense lam h0 hhalf hpi l L Q (fun i => (R i).interval_nonneg) hL rho hrho hfillM)
    phi hLip hnorm hs

end
end SixVertex
