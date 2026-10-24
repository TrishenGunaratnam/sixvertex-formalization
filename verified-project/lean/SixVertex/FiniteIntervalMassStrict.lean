import SixVertex.FiniteIntervalMassLimit

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- The actual full-line density has positive mass outside every finite
interval, using positivity and continuity on a disjoint unit interval. -/
theorem fullLineDensityExteriorMass_pos (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) :
    0 < fullLineDensityExteriorMass lam h0 hpi Q := by
  have hab : Q+1 < Q+2 := by linarith
  have hp := intervalIntegral.integral_pos hab (fullLineDensityFunction lam h0 hpi).continuous.continuousOn
    (fun u _ => (fullLineDensityFunction_pos lam h0 hhalf hpi u).le)
    ⟨Q+1,⟨le_rfl,hab.le⟩,fullLineDensityFunction_pos lam h0 hhalf hpi (Q+1)⟩
  have hpset : 0 < ∫ u in Icc (Q+1) (Q+2), fullLineDensityFunction lam h0 hpi u := by
    rwa [intervalIntegral.integral_of_le hab.le,← integral_Icc_eq_integral_Ioc] at hp
  have hsub : Icc (Q+1) (Q+2) ⊆ (Icc (-Q) Q)ᶜ := by
    intro u hu hn
    have hh := hn.2
    linarith [hu.1]
  have hle : (∫ u in Icc (Q+1) (Q+2), fullLineDensityFunction lam h0 hpi u) ≤
      fullLineDensityExteriorMass lam h0 hpi Q :=
    setIntegral_mono_set (fullLineDensityFunction_integrable lam h0 hpi).integrableOn
      (Eventually.of_forall (fun u => (fullLineDensityFunction_pos lam h0 hhalf hpi u).le))
      (Eventually.of_forall (fun _ hu => hsub hu))
  exact hpset.trans_le hle

theorem finiteIntervalMass_lt_half (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) :
    finiteIntervalMass lam h0 hpi Q < 1/2 := by
  have hp := fullLineDensityExteriorMass_pos lam h0 hhalf hpi Q
  have hd := (finiteIntervalMass_deficit_bounds lam h0 hhalf hpi Q).1
  linarith

theorem finiteIntervalMass_pos (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 < Q) :
    0 < finiteIntervalMass lam h0 hpi Q := by
  have hab : -Q < Q := by linarith
  have hp := intervalIntegral.integral_pos hab (finiteIntervalDensity lam h0 hpi Q).continuous.continuousOn
    (fun u _ => (finiteIntervalDensity_pos lam h0 hhalf hpi Q u).le)
    ⟨0,⟨by linarith,by linarith⟩,finiteIntervalDensity_pos lam h0 hhalf hpi Q 0⟩
  change 0 < ∫ u in Icc (-Q) Q, finiteIntervalDensity lam h0 hpi Q u
  rwa [intervalIntegral.integral_of_le hab.le,← integral_Icc_eq_integral_Ioc] at hp

/-- Approaching half filling forces the finite-interval endpoint to
escape to infinity. This makes the occupied-window exhaustion explicit. -/
theorem finiteIntervalBoundary_tendsto_atTop {α : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (q : α → ℝ) (l : Filter α)
    (hfill : Tendsto (fun a => finiteIntervalMass lam h0 hpi (q a)) l (𝓝 (1/2 : ℝ))) :
    Tendsto q l atTop := by
  apply tendsto_atTop.mpr
  intro B
  have he := hfill.eventually (Ioi_mem_nhds (finiteIntervalMass_lt_half lam h0 hhalf hpi B))
  filter_upwards [he] with a ha
  by_contra hn
  have hq : q a ≤ B := (lt_of_not_ge hn).le
  exact (not_le_of_gt ha) (finiteIntervalMass_monotone lam h0 hhalf hpi hq)

end
end SixVertex
