import SixVertex.FiniteIntervalMass
import SixVertex.WindowComparison

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Ordinary mass of the actual inverse-defined full-line density
outside the interval; this is not assigned independently by a deficit. -/
def fullLineDensityExteriorMass (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) : ℝ :=
  ∫ u in (Icc (-Q) Q)ᶜ, fullLineDensityFunction lam h0 hpi u

theorem fullLineDensityExteriorMass_split (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) :
    (∫ u in Icc (-Q) Q, fullLineDensityFunction lam h0 hpi u)+
      fullLineDensityExteriorMass lam h0 hpi Q=1/2 := by
  have h := integral_add_compl (s := Icc (-Q) Q) measurableSet_Icc
    (fullLineDensityFunction_integrable lam h0 hpi)
  rwa [integral_fullLineDensityFunction lam h0 hpi] at h

/-- The finite-interval filling deficit is comparable to the actual
full-line exterior mass, with constants uniform in Q. This follows from
Fubini, positivity and r_Q <= r, without a hyperbolic formula. -/
theorem finiteIntervalMass_deficit_bounds (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) :
    fullLineDensityExteriorMass lam h0 hpi Q ≤ 1/2-finiteIntervalMass lam h0 hpi Q ∧
      1/2-finiteIntervalMass lam h0 hpi Q ≤
        fullLineDensityExteriorMass lam h0 hpi Q/(2*(1-lam/Real.pi)) := by
  have hr := fullLineDensityFunction_integrable lam h0 hpi
  have hQ := finiteIntervalDensity_integrable lam h0 hpi Q
  have hle : ∀ u, finiteIntervalDensity lam h0 hpi Q u ≤ fullLineDensityFunction lam h0 hpi u :=
    finiteIntervalDensity_le_fullLineDensity lam h0 hhalf hpi Q
  have hsplit := fullLineDensityExteriorMass_split lam h0 hpi Q
  constructor
  · have hin : finiteIntervalMass lam h0 hpi Q ≤ ∫ u in Icc (-Q) Q, fullLineDensityFunction lam h0 hpi u :=
      integral_mono hQ.integrableOn hr.integrableOn hle
    linarith
  · have hout : (∫ u in (Icc (-Q) Q)ᶜ, finiteIntervalDensity lam h0 hpi Q u) ≤
        fullLineDensityExteriorMass lam h0 hpi Q :=
      integral_mono hQ.integrableOn hr.integrableOn hle
    have hsplitQ : finiteIntervalMass lam h0 hpi Q+
        (∫ u in (Icc (-Q) Q)ᶜ, finiteIntervalDensity lam h0 hpi Q u)=
        ∫ u : ℝ, finiteIntervalDensity lam h0 hpi Q u :=
      integral_add_compl measurableSet_Icc hQ
    have hm := finiteIntervalDensity_total_mass_equation lam h0 hpi Q
    have hden : 0 < 2*(1-lam/Real.pi) := mul_pos (by norm_num)
      (sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hpi))
    apply (le_div_iff₀ hden).mpr
    rw [show 2*lam/Real.pi=2*(lam/Real.pi) by ring] at hm
    nlinarith [hsplitQ,hout]

theorem finiteIntervalMass_bounds (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) :
    0 ≤ finiteIntervalMass lam h0 hpi Q ∧ finiteIntervalMass lam h0 hpi Q ≤ 1/2 := by
  have htail : 0 ≤ fullLineDensityExteriorMass lam h0 hpi Q :=
    integral_nonneg (fun u => (fullLineDensityFunction_pos lam h0 hhalf hpi u).le)
  have hdef := (finiteIntervalMass_deficit_bounds lam h0 hhalf hpi Q).1
  exact ⟨integral_nonneg (fun u => (finiteIntervalDensity_pos lam h0 hhalf hpi Q u).le),by linarith⟩

/-- Both the integrand and the integration window increase with Q. -/
theorem finiteIntervalMass_monotone (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) : Monotone (finiteIntervalMass lam h0 hpi) := by
  intro Q T hQT
  calc
    _ = ∫ u : ℝ, windowedFunction Q (finiteIntervalDensity lam h0 hpi Q) u := by
      rw [windowedFunction,integral_indicator measurableSet_Icc]
      rfl
    _ ≤ ∫ u : ℝ, windowedFunction T (finiteIntervalDensity lam h0 hpi T) u := by
      apply integral_mono (windowedFunction_integrable Q _) (windowedFunction_integrable T _)
      intro u
      by_cases huQ : u ∈ Icc (-Q) Q
      · have huT : u ∈ Icc (-T) T := ⟨by linarith [huQ.1],by linarith [huQ.2]⟩
        simp only [windowedFunction,Set.indicator_of_mem huQ,Set.indicator_of_mem huT]
        exact finiteIntervalDensity_monotone_Q lam h0 hhalf hpi Q T hQT u
      · by_cases huT : u ∈ Icc (-T) T
        · simp only [windowedFunction,Set.indicator_of_notMem huQ,Set.indicator_of_mem huT]
          exact (finiteIntervalDensity_pos lam h0 hhalf hpi T u).le
        · simp only [windowedFunction,Set.indicator_of_notMem huQ,Set.indicator_of_notMem huT]
          exact le_rfl
    _ = _ := by rw [windowedFunction,integral_indicator measurableSet_Icc]; rfl

end
end SixVertex
