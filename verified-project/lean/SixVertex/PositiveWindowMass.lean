import SixVertex.PositiveWindowComparison
import SixVertex.FiniteIntervalMassLimit

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set Topology

/-- The actual positive-kernel filling deficit is comparable to the
ordinary full-line exterior mass, uniformly over the cutoff. -/
theorem finiteIntervalMass_deficit_bounds_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q : ℝ) :
    fullLineDensityExteriorMass lam h0 (by linarith [Real.pi_pos]) Q/(2*(1-lam/Real.pi)) ≤
      1/2-finiteIntervalMass lam h0 (by linarith [Real.pi_pos]) Q ∧
    1/2-finiteIntervalMass lam h0 (by linarith [Real.pi_pos]) Q ≤
      fullLineDensityExteriorMass lam h0 (by linarith [Real.pi_pos]) Q := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have hr := fullLineDensityFunction_integrable lam h0 hpi
  have hq := finiteIntervalDensity_integrable lam h0 hpi Q
  have hge : ∀ u,fullLineDensityFunction lam h0 hpi u ≤ finiteIntervalDensity lam h0 hpi Q u :=
    finiteIntervalDensity_ge_fullLine_positiveK lam h0 hh Q
  have hsplit := fullLineDensityExteriorMass_split lam h0 hpi Q
  constructor
  · have hout : fullLineDensityExteriorMass lam h0 hpi Q ≤
        ∫ u in (Icc (-Q) Q)ᶜ,finiteIntervalDensity lam h0 hpi Q u :=
      integral_mono hr.integrableOn hq.integrableOn hge
    have hsplitq : finiteIntervalMass lam h0 hpi Q+
        (∫ u in (Icc (-Q) Q)ᶜ,finiteIntervalDensity lam h0 hpi Q u)=
        ∫ u : ℝ,finiteIntervalDensity lam h0 hpi Q u :=
      integral_add_compl measurableSet_Icc hq
    have hm := finiteIntervalDensity_total_mass_equation lam h0 hpi Q
    have hd : 0 < 2*(1-lam/Real.pi) := mul_pos (by norm_num)
      (sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hpi))
    apply (div_le_iff₀ hd).mpr
    rw [show 2*lam/Real.pi=2*(lam/Real.pi) by ring] at hm
    nlinarith only [hm,hsplitq,hout]
  · have hin : (∫ u in Icc (-Q) Q,fullLineDensityFunction lam h0 hpi u) ≤
        finiteIntervalMass lam h0 hpi Q := integral_mono hr.integrableOn hq.integrableOn hge
    linarith

/-- The actual finite-window filling stays in [0,1/2] also for positive K. -/
theorem finiteIntervalMass_bounds_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q : ℝ) :
    0 ≤ finiteIntervalMass lam h0 (by linarith [Real.pi_pos]) Q ∧
      finiteIntervalMass lam h0 (by linarith [Real.pi_pos]) Q ≤ 1/2 := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have ht : 0 ≤ fullLineDensityExteriorMass lam h0 hpi Q :=
    integral_nonneg (fun u => (fullLineDensityFunction_pos_all lam h0 hpi u).le)
  have hd : 0 ≤ 1/2-finiteIntervalMass lam h0 hpi Q :=
    (div_nonneg ht (by have hx := (div_lt_one Real.pi_pos).mpr hpi; positivity)).trans
      (finiteIntervalMass_deficit_bounds_positiveK lam h0 hh Q).1
  exact ⟨integral_nonneg (fun u => (finiteIntervalDensity_pos_positiveK lam h0 hh Q u).le),by linarith⟩

/-- Positive-kernel finite-window masses converge to the true half mass;
the proof uses actual exterior integrals and no endpoint derivative. -/
theorem finiteIntervalMass_tendsto_half_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    Tendsto (finiteIntervalMass lam h0 (by linarith [Real.pi_pos])) atTop (𝓝 (1/2 : ℝ)) := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have hd : Tendsto (fun Q : ℝ => (1/2 : ℝ)-finiteIntervalMass lam h0 hpi Q) atTop (𝓝 0) := by
    apply squeeze_zero (fun Q => sub_nonneg.mpr (finiteIntervalMass_bounds_positiveK lam h0 hh Q).2)
      (fun Q => (finiteIntervalMass_deficit_bounds_positiveK lam h0 hh Q).2)
    exact fullLineDensityExteriorMass_tendsto_zero lam h0 hpi
  simpa only [sub_sub_cancel,sub_zero] using hd.const_sub (1/2 : ℝ)

end
end SixVertex
