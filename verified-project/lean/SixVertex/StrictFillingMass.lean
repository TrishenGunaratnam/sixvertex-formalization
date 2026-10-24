import SixVertex.MassParameterContinuity

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

/-- The ordinary finite-window filling mass is strictly increasing on
nonnegative cutoffs, not merely nondecreasing. -/
theorem finiteIntervalMass_strictMonoOn (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    StrictMonoOn (finiteIntervalMass lam h0 hpi) (Ici (0 : ℝ)) := by
  intro Q hQ T hT hQT
  change 0 ≤ Q at hQ
  change 0 ≤ T at hT
  let r := finiteIntervalDensity lam h0 hpi Q
  have hi (a b : ℝ) : IntervalIntegrable (fun u => r u) volume a b := r.continuous.intervalIntegrable a b
  have hp : 0 < ∫ u in Q..T, r u := intervalIntegral.integral_pos hQT r.continuous.continuousOn
    (fun u _ => (finiteIntervalDensity_pos lam h0 hhalf hpi Q u).le)
    ⟨Q,⟨le_rfl,hQT.le⟩,finiteIntervalDensity_pos lam h0 hhalf hpi Q Q⟩
  have hn : 0 ≤ ∫ u in -T..(-Q), r u := intervalIntegral.integral_nonneg (by linarith)
    (fun u _ => (finiteIntervalDensity_pos lam h0 hhalf hpi Q u).le)
  have ha := intervalIntegral.integral_add_adjacent_intervals (hi (-T) (-Q)) (hi (-Q) Q)
  have hb := intervalIntegral.integral_add_adjacent_intervals (hi (-T) Q) (hi Q T)
  have hq : finiteIntervalMass lam h0 hpi Q=∫ u in -Q..Q, r u := by
    rw [intervalIntegral.integral_of_le (by linarith [hQ] : -Q ≤ Q),← integral_Icc_eq_integral_Ioc]
    rfl
  have hTQ : (∫ u in -T..T, r u) ≤ finiteIntervalMass lam h0 hpi T := by
    rw [intervalIntegral.integral_of_le (by linarith [hT] : -T ≤ T),← integral_Icc_eq_integral_Ioc]
    apply integral_mono r.continuous.integrableOn_Icc (finiteIntervalDensity lam h0 hpi T).continuous.integrableOn_Icc
    intro u
    exact finiteIntervalDensity_monotone_Q lam h0 hhalf hpi Q T hQT.le u
  rw [hq]
  linarith

/-- Every prescribed strictly sub-half filling has a unique nonnegative
cutoff, for the actual inverse-defined density. -/
theorem exists_unique_finiteIntervalCutoff (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (rho : ℝ) (hrho : 0 < rho) (hrhalf : rho < 1/2) :
    ∃! Q : ℝ, 0 ≤ Q ∧ finiteIntervalMass lam h0 hpi Q=rho := by
  obtain ⟨Q,hQ,hm⟩ := exists_finiteIntervalCutoff lam h0 hhalf hpi rho hrho hrhalf
  refine ⟨Q,⟨hQ.le,hm⟩,?_⟩
  intro T hT
  exact (finiteIntervalMass_strictMonoOn lam h0 hhalf hpi).injOn hT.1 hQ.le (hT.2.trans hm.symm)

/-- A filling family converging strictly below half has bounded cutoffs.
This makes the first stage of the regular-filling procedure explicit. -/
theorem finiteIntervalCutoff_eventually_bounded {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ι → ℝ) (l : Filter ι)
    (rho : ℝ) (hrho : rho < 1/2)
    (hfill : Tendsto (fun i => finiteIntervalMass lam h0 hpi (Q i)) l (𝓝 rho)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ i in l, Q i ≤ B := by
  have he := (finiteIntervalMass_tendsto_half lam h0 hhalf hpi).eventually (Ioi_mem_nhds hrho)
  obtain ⟨B,hB,hBm⟩ := ((eventually_ge_atTop (0 : ℝ)).and he).exists
  refine ⟨B,hB,?_⟩
  filter_upwards [hfill.eventually (Iio_mem_nhds hBm)] with i hi
  by_contra hn
  have hBi : B ≤ Q i := (lt_of_not_ge hn).le
  have hm := finiteIntervalMass_monotone lam h0 hhalf hpi hBi
  linarith

end
end SixVertex
