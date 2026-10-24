import SixVertex.StrictPositiveFillingMass

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

/-- Strict filling-mass monotonicity in every physical parameter regime. -/
theorem finiteIntervalMass_strictMonoOn_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    StrictMonoOn (finiteIntervalMass lam h0 hpi) (Ici (0 : ℝ)) := by
  by_cases hh : Real.pi/2 ≤ lam
  · exact finiteIntervalMass_strictMonoOn lam h0 hh hpi
  · exact finiteIntervalMass_strictMonoOn_positiveK lam h0 (lt_of_not_ge hh)

/-- The actual finite-window filling stays within its physical range. -/
theorem finiteIntervalMass_bounds_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) :
    0 ≤ finiteIntervalMass lam h0 hpi Q ∧ finiteIntervalMass lam h0 hpi Q ≤ 1/2 := by
  by_cases hh : Real.pi/2 ≤ lam
  · exact finiteIntervalMass_bounds lam h0 hh hpi Q
  · exact finiteIntervalMass_bounds_positiveK lam h0 (lt_of_not_ge hh) Q

/-- The actual filling limit is one half throughout the physical range. -/
theorem finiteIntervalMass_tendsto_half_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Tendsto (finiteIntervalMass lam h0 hpi) atTop (𝓝 (1/2 : ℝ)) := by
  by_cases hh : Real.pi/2 ≤ lam
  · exact finiteIntervalMass_tendsto_half lam h0 hh hpi
  · exact finiteIntervalMass_tendsto_half_positiveK lam h0 (lt_of_not_ge hh)

/-- At every finite positive cutoff the actual filling is strictly
between zero and one half. -/
theorem finiteIntervalMass_strict_bounds_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (hQ : 0 < Q) : 0 < finiteIntervalMass lam h0 hpi Q ∧ finiteIntervalMass lam h0 hpi Q < 1/2 := by
  have hm := finiteIntervalMass_strictMonoOn_all lam h0 hpi
  have hp := hm (show (0 : ℝ) ∈ Ici 0 by simp) hQ.le hQ
  rw [finiteIntervalMass_zero] at hp
  have hu := hm hQ.le (show Q+1 ∈ Ici (0 : ℝ) by change 0 ≤ Q+1; linarith) (by linarith : Q < Q+1)
  exact ⟨hp,hu.trans_le (finiteIntervalMass_bounds_all lam h0 hpi (Q+1)).2⟩

/-- Every subhalf filling has a unique actual nonnegative cutoff,
uniformly covering both signs of the interaction kernel and the free point. -/
theorem exists_unique_finiteIntervalCutoff_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (rho : ℝ) (hrho : 0 < rho) (hrhalf : rho < 1/2) :
    ∃! Q : ℝ,0 ≤ Q ∧ finiteIntervalMass lam h0 hpi Q=rho := by
  by_cases hh : Real.pi/2 ≤ lam
  · exact exists_unique_finiteIntervalCutoff lam h0 hh hpi rho hrho hrhalf
  · exact exists_unique_finiteIntervalCutoff_positiveK lam h0 (lt_of_not_ge hh) rho hrho hrhalf

/-- Subhalf limiting filling forces eventually bounded actual cutoffs,
for every physical lambda. -/
theorem finiteIntervalCutoff_eventually_bounded_all {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ι → ℝ) (l : Filter ι) (rho : ℝ) (hrho : rho < 1/2)
    (hfill : Tendsto (fun i => finiteIntervalMass lam h0 hpi (Q i)) l (𝓝 rho)) :
    ∃ B : ℝ,0 ≤ B ∧ ∀ᶠ i in l,Q i ≤ B := by
  have he := (finiteIntervalMass_tendsto_half_all lam h0 hpi).eventually (Ioi_mem_nhds hrho)
  obtain ⟨B,hB,hBm⟩ := ((eventually_ge_atTop (0 : ℝ)).and he).exists
  refine ⟨B,hB,?_⟩
  filter_upwards [hfill.eventually (Iio_mem_nhds hBm)] with i hi
  by_contra hn
  have hBi : B ≤ Q i := (lt_of_not_ge hn).le
  have hm := (finiteIntervalMass_strictMonoOn_all lam h0 hpi).monotoneOn hB (hB.trans hBi) hBi
  linarith

end
end SixVertex
