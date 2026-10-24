import SixVertex.PhysicalJacobianVariation
import SixVertex.RootSeeds

namespace SixVertex
noncomputable section
open Set Filter Topology

/-- The actual finite-window profile retains a scaled lower bound in
an expanded window, with an explicit exponential loss. -/
theorem expanded_window_scaled_density_lower_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q) (L : ℕ) (M delta : ℝ) (hdelta : 0 ≤ delta)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (u : ℝ) (hu : u ∈ Icc (-Q-delta) (Q+delta)) :
    M*Real.exp (-(physicalDensityLogConstant lam*delta)) ≤
      (L : ℝ)*finiteIntervalDensity lam h0 hpi Q u := by
  obtain ⟨v,hv,hd⟩ : ∃ v : ℝ,v ∈ Icc (-Q) Q ∧ |u-v| ≤ delta := by
    by_cases hl : u < -Q
    · refine ⟨-Q,⟨le_rfl,by linarith⟩,?_⟩
      exact abs_le.mpr ⟨by linarith [hu.1],by linarith⟩
    · by_cases hr : Q < u
      · refine ⟨Q,⟨by linarith,le_rfl⟩,?_⟩
        exact abs_le.mpr ⟨by linarith,by linarith [hu.2]⟩
      · exact ⟨u,⟨le_of_not_gt hl,le_of_not_gt hr⟩,by simpa only [sub_self,abs_zero] using hdelta⟩
  have hf := (finiteIntervalDensity_exponential_comparison_all lam h0 hpi Q v u).1
  have he : Real.exp (-(physicalDensityLogConstant lam*delta)) ≤
      Real.exp (-(physicalDensityLogConstant lam*|u-v|)) := by
    apply Real.exp_le_exp.mpr
    exact neg_le_neg (mul_le_mul_of_nonneg_left hd (physicalDensityLogConstant_pos lam h0).le)
  have ht := (mul_le_mul_of_nonneg_right he (finiteIntervalDensity_pos_all lam h0 hpi Q v).le).trans hf
  calc
    _ ≤ ((L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)*Real.exp (-(physicalDensityLogConstant lam*delta)) :=
      mul_le_mul_of_nonneg_right (hlower v hv) (Real.exp_pos _).le
    _ = (L : ℝ)*(Real.exp (-(physicalDensityLogConstant lam*delta))*finiteIntervalDensity lam h0 hpi Q v) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg L : (0 : ℝ) ≤ L)

/-- At sufficiently dense reference data, the perturbed actual counting
density is positive throughout the expanded occupied window. -/
theorem weighted_configuration_countingSlope_pos_expanded_all {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y X : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (M : ℝ) (hM : 0 < M)
    (hlower : ∀ v ∈ Icc (-Q) Q,M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v)
    (radius : ℝ) (hrad : 0 ≤ radius)
    (hclose : ∀ j,|X j-Y j| ≤ radius/((L : ℝ)*finiteIntervalDensity lam h0 hpi Q (Y j)))
    (hlarge : kernelL1Mass (kernelKPrime lam)/2+
      (kernelLogConstant lam*Real.exp (kernelLogConstant lam*(radius/M))*radius)*
        (kernelL1Mass (kernelK lam)+physicalReferenceKernelRowErrorConstant lam/M) <
      M*Real.exp (-(physicalDensityLogConstant lam*(radius/M))))
    (u : ℝ) (hu : u ∈ Icc (-Q-radius/M) (Q+radius/M)) :
    0 < countingSlope lam (fun _ => 0) L X u := by
  have he := weighted_configuration_density_error_all lam h0 hpi Q L Y X R M hM hlower radius hrad hclose u
  have hl := expanded_window_scaled_density_lower_all lam h0 hpi Q R.interval_nonneg L M (radius/M)
    (div_nonneg hrad hM.le) hlower u hu
  linarith [(abs_le.mp he).1]

/-- Positive actual counting density on an interval containing all roots
forces a solution with consecutive counting targets to be ordered. -/
theorem countingSystem_solution_ordered_on_interval {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (b : ℕ → ℝ) (L : ℕ) (X : Fin n → ℝ) (twist a c : ℝ)
    (hloc : ∀ j,X j ∈ Icc a c)
    (hpos : ∀ u ∈ Icc a c,0 < countingSlope lam b L X u)
    (heq : countingSystem lam b L X=countingTarget n twist) :
    ConsecutiveRoots lam b L X twist := by
  have hmono : StrictMonoOn (countingXi lam b L X) (Icc a c) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc a c)
    · intro u _
      exact (hasDerivAt_countingXi lam b L X u h0 hpi).continuousAt.continuousWithinAt
    · intro u hu
      rw [(hasDerivAt_countingXi lam b L X u h0 hpi).deriv]
      exact hpos u (interior_subset hu)
  refine ⟨?_,heq⟩
  intro i j hij
  by_contra hle
  have hji : X j ≤ X i := le_of_not_gt hle
  have hc : countingXi lam b L X (X j) ≤ countingXi lam b L X (X i) :=
    hmono.monotoneOn (hloc j) (hloc i) hji
  have ht : countingSystem lam b L X i < countingSystem lam b L X j := by
    rw [heq]
    exact countingTarget_strictMono n twist hij
  exact (not_lt_of_ge hc) ht

end
end SixVertex
