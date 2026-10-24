import SixVertex.LipschitzQuadrature
import SixVertex.LocalDensityGrowth

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal

/-- Uniform C/L error against every unit bounded-Lipschitz test supported
in a fixed compact interval, for every bounded real-array half-filled chain. -/
theorem exists_half_filled_quadrature_rate (lam : ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (R B : ℝ) (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ) (b : ℕ → ℝ) (L : ℕ), 0 < L → L=2*n →
      ∀ (Y : Fin n → ℝ), ConsecutiveRoots lam b L Y 0 →
      (∀ a ∈ Finset.range L, |b a| ≤ B) →
      ∀ phi : BoundedRealFunction, LipschitzWith 1 (fun x => phi x) → ‖phi‖ ≤ 1 →
      (∀ x, x ∉ Icc (-R) R → phi x=0) →
      |(∫ x, phi x ∂rootQuadratureMeasure lam b L Y)-(∫ x : ℝ, phi x)| ≤ C/(L : ℝ) := by
  obtain ⟨d,hd,hgrowth⟩ := exists_local_counting_density_growth lam hhalf hpi R B
  let C : ℝ := R*(1+kernelLogConstant lam)/d
  have hC : 0 < C := by
    dsimp [C]
    exact div_pos (mul_pos hR (by linarith [kernelLogConstant_nonneg lam])) hd
  refine ⟨C,hC,?_⟩
  intro n b L hL hfill Y hroots hb phi hLip hnorm hs
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hM : 0 < d*(L : ℝ) := mul_pos hd hLp
  have he := unit_bounded_lipschitz_quadrature_error lam b L hL Y hhalf hpi hroots phi hLip hnorm
    (-R) R (d*(L : ℝ)) (by linarith) hM hs
    (fun x hx => hgrowth n b L Y hb x (abs_le.mpr hx))
    (fun x _ => countingXi_half_bounds lam b L hL hfill Y hhalf hpi x)
  apply he.trans_eq
  dsimp [C]
  field_simp [hd.ne',hLp.ne']
  ring

/-- Local convergence for unit bounded-Lipschitz tests is a consequence
of the proved rate for actual half-filled chains, not a density hypothesis. -/
theorem half_filled_quadrature_tendsto (lam : ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (R B : ℝ) (hR : 0 < R)
    (n L : ℕ → ℕ) (b : ℕ → ℕ → ℝ) (Y : (m : ℕ) → Fin (n m) → ℝ)
    (hLinf : Tendsto L atTop atTop)
    (hfill : ∀ m, L m=2*n m)
    (hroots : ∀ m, 0 < L m → ConsecutiveRoots lam (b m) (L m) (Y m) 0)
    (hb : ∀ m, ∀ a ∈ Finset.range (L m), |b m a| ≤ B)
    (phi : BoundedRealFunction) (hLip : LipschitzWith 1 (fun x => phi x)) (hnorm : ‖phi‖ ≤ 1)
    (hs : ∀ x, x ∉ Icc (-R) R → phi x=0) :
    Tendsto (fun m : ℕ => ∫ x, phi x ∂rootQuadratureMeasure lam (b m) (L m) (Y m))
      atTop (𝓝 (∫ x : ℝ, phi x)) := by
  obtain ⟨C,hC,hbound⟩ := exists_half_filled_quadrature_rate lam hhalf hpi R B hR
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (g := fun m => C/(L m : ℝ)) (Eventually.of_forall (fun m => norm_nonneg _))
  · filter_upwards [hLinf.eventually (eventually_ge_atTop 1)] with m hm
    rw [Real.norm_eq_abs]
    exact hbound (n m) (b m) (L m) (by omega) (hfill m) (Y m) (hroots m (by omega)) (hb m) phi hLip hnorm hs
  · exact tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp hLinf)

end
end SixVertex
