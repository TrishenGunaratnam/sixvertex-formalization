import SixVertex.PhysicalNewtonRoots
import SixVertex.PhysicalPerturbedOrder
import SixVertex.PhysicalReferenceThreshold

namespace SixVertex
noncomputable section
open Set Filter Topology

/-- The actual density error is smaller than the expanded-window
continuum lower bound once the density scale exceeds a fixed threshold. -/
theorem exists_configuration_density_positivity_threshold (lam radius : ℝ) :
    ∃ M₀ : ℝ,0 < M₀ ∧ ∀ M : ℝ,M₀ ≤ M →
      kernelL1Mass (kernelKPrime lam)/2+
        (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
          (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) <
      M*Real.exp (-(physicalDensityLogConstant lam*(radius/M))) := by
  have hδ : Tendsto (fun M : ℝ => radius/M) atTop (nhds 0) := tendsto_id.const_div_atTop radius
  have hb : Tendsto (fun M : ℝ => physicalReferenceKernelRowErrorConstant lam/M) atTop (nhds 0) :=
    tendsto_id.const_div_atTop _
  have he : Tendsto (fun M : ℝ => Real.exp (kernelLogConstant lam*(radius/M))) atTop (nhds 1) := by
    simpa only [mul_zero,Real.exp_zero,Function.comp_def] using
      (Real.continuous_exp.tendsto _).comp (hδ.const_mul (kernelLogConstant lam))
  have hf : Tendsto (fun M : ℝ => Real.exp (-(physicalDensityLogConstant lam*(radius/M)))) atTop (nhds 1) := by
    simpa only [mul_zero,neg_zero,Real.exp_zero,Function.comp_def] using
      (Real.continuous_exp.tendsto _).comp (hδ.const_mul (physicalDensityLogConstant lam)).neg
  have hv := ((he.const_mul (kernelLogConstant lam)).mul_const radius).mul
    (hb.const_add (kernelL1Mass (kernelK lam)))
  have hlim := (hv.const_add (kernelL1Mass (kernelKPrime lam)/2)).div_atTop tendsto_id
  have hsmall := hlim.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1/2))
  have hlarge := hf.eventually (lt_mem_nhds (by norm_num : (1/2 : ℝ) < 1))
  obtain ⟨m,hm⟩ := eventually_atTop.1 (hsmall.and hlarge)
  refine ⟨max m 1,lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _),?_⟩
  intro M hM
  have hMp : 0 < M := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) ((le_max_right m 1).trans hM)
  obtain ⟨hs,hl⟩ := hm M ((le_max_left _ _).trans hM)
  have hs' := (div_lt_iff₀ hMp).mp hs
  have hl' := mul_lt_mul_of_pos_left hl hMp
  exact hs'.trans (by nlinarith only [hl'])

/-- Actual ordered homogeneous Bethe roots exist near the actual
continuum mid-quantiles for every physical lambda under a single
uniform scaled-density threshold. -/
theorem exists_weighted_reference_consecutive_roots_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ M₀ radius : ℝ,0 < M₀ ∧ 0 < radius ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      ∃ X : Fin n → ℝ,ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)) := by
  obtain ⟨m,radius,hm,hrad,hroots⟩ := exists_weighted_reference_counting_solution_all lam h0 hpi
  obtain ⟨m',hm',hpos⟩ := exists_configuration_density_positivity_threshold lam radius
  let M₀ := max m m'
  have hM : 0 < M₀ := hm.trans_le (le_max_left _ _)
  refine ⟨M₀,radius,hM,hrad,?_⟩
  intro n Q L Y R hlower
  obtain ⟨X,heq,hclose⟩ := hroots n Q L Y R
    (fun u hu => (le_max_left _ _).trans (hlower u hu))
  refine ⟨X,?_,hclose⟩
  have hphysical (j : Fin n) : |X j-Y j| ≤ radius/M₀ := by
    exact (hclose j).trans (div_le_div₀ hrad.le le_rfl hM
      (hlower (Y j) ⟨(R.location j).1.le,(R.location j).2.le⟩))
  have hloc (j : Fin n) : X j ∈ Icc (-Q-radius/M₀) (Q+radius/M₀) := by
    have hd := abs_le.mp (hphysical j)
    have hy := R.location j
    exact ⟨by linarith [hy.1],by linarith [hy.2]⟩
  apply countingSystem_solution_ordered_on_interval lam h0 hpi (fun _ => 0) L X 0
    (-Q-radius/M₀) (Q+radius/M₀) hloc _ heq
  exact weighted_configuration_countingSlope_pos_expanded_all lam h0 hpi Q L Y X R M₀ hM hlower
    radius hrad.le hclose (hpos M₀ (le_max_right _ _))

/-- The actual ordered roots have a uniform whole-line density error,
with every constant fixed before all finite data and cutoffs. -/
theorem exists_weighted_reference_roots_and_density_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ M₀ radius C : ℝ,0 < M₀ ∧ 0 < radius ∧ 0 < C ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      (∀ u ∈ Icc (-Q) Q,M₀ ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u) →
      ∃ X : Fin n → ℝ,ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) ∧
        ∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
          (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C := by
  obtain ⟨M,radius,hM,hrad,hroots⟩ := exists_weighted_reference_consecutive_roots_all lam h0 hpi
  let E := kernelL1Mass (kernelKPrime lam)/2+
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M)
  have hE : 0 ≤ E := by
    have hk := kernelLogConstant_nonneg lam
    have hb := physicalReferenceKernelRowErrorConstant_nonneg lam h0
    have hm := kernelL1Mass_nonneg (kernelK lam)
    have hd := kernelL1Mass_nonneg (kernelKPrime lam)
    dsimp [E]
    positivity
  refine ⟨M,radius,E+1,hM,hrad,by linarith,?_⟩
  intro n Q L Y R hlower
  obtain ⟨X,hX,hclose⟩ := hroots n Q L Y R hlower
  refine ⟨X,hX,hclose,?_⟩
  intro u
  exact (weighted_configuration_density_error_all lam h0 hpi Q L Y X R M hM hlower radius hrad.le hclose u).trans
    (by change E ≤ E+1; linarith)

/-- The paper's boundary-density criterion suffices for actual ordered
root construction, weighted quantile stability and uniform density
approximation, even when the continuum cutoff diverges. -/
theorem exists_boundary_reference_roots_and_density_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ D radius C : ℝ,0 < D ∧ 0 < radius ∧ 0 < C ∧
    ∀ (n : ℕ) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ),
      ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      D ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      ∃ X : Fin n → ℝ,ConsecutiveRoots lam (fun _ => 0) L X 0 ∧
        (∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j))) ∧
        ∀ u : ℝ,|countingSlope lam (fun _ => 0) L X u-
          (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤ C := by
  obtain ⟨c,C',hc,hC',hcomp⟩ := exists_uniform_finiteInterval_comparison lam h0 hpi
  obtain ⟨M,radius,C,hM,hrad,hC,hroots⟩ := exists_weighted_reference_roots_and_density_all lam h0 hpi
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

end
end SixVertex
