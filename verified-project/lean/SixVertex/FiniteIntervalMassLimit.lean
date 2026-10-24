import SixVertex.FiniteIntervalMassBounds

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem fullLineDensityExteriorMass_tendsto_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Tendsto (fullLineDensityExteriorMass lam h0 hpi) atTop (𝓝 0) := by
  have ht := intervalIntegral_tendsto_integral (fullLineDensityFunction_integrable lam h0 hpi)
    tendsto_neg_atTop_atBot tendsto_id
  rw [integral_fullLineDensityFunction lam h0 hpi] at ht
  have hi : Tendsto (fun Q : ℝ => ∫ u in Icc (-Q) Q, fullLineDensityFunction lam h0 hpi u)
      atTop (𝓝 (1/2 : ℝ)) := by
    apply ht.congr'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with Q hQ
    simp only [id_eq]
    rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]
  have he : (fun Q : ℝ => fullLineDensityExteriorMass lam h0 hpi Q)=
      fun Q => (1/2 : ℝ)-(∫ u in Icc (-Q) Q, fullLineDensityFunction lam h0 hpi u) := by
    funext Q
    linarith [fullLineDensityExteriorMass_split lam h0 hpi Q]
  change Tendsto (fun Q : ℝ => fullLineDensityExteriorMass lam h0 hpi Q) atTop (𝓝 0)
  rw [he]
  simpa only [sub_self] using hi.const_sub (1/2 : ℝ)

/-- The finite-interval filling masses increase to exactly one half in
the negative-kernel regime. The convergence uses the actual exterior
integral and its uniform two-sided deficit comparison. -/
theorem finiteIntervalMass_tendsto_half (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    Tendsto (finiteIntervalMass lam h0 hpi) atTop (𝓝 (1/2 : ℝ)) := by
  have ht := (fullLineDensityExteriorMass_tendsto_zero lam h0 hpi).div_const (2*(1-lam/Real.pi))
  have hd : Tendsto (fun Q : ℝ => (1/2 : ℝ)-finiteIntervalMass lam h0 hpi Q) atTop (𝓝 0) := by
    apply squeeze_zero (fun Q => sub_nonneg.mpr (finiteIntervalMass_bounds lam h0 hhalf hpi Q).2)
      (fun Q => (finiteIntervalMass_deficit_bounds lam h0 hhalf hpi Q).2)
    simpa only [zero_div] using ht
  simpa only [sub_sub_cancel,sub_zero] using hd.const_sub (1/2 : ℝ)

theorem finiteIntervalMass_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    finiteIntervalMass lam h0 hpi 0=0 := by
  simp [finiteIntervalMass]

end
end SixVertex
