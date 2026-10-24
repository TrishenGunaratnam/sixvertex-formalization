import SixVertex.DyadicEnergy
import SixVertex.LogDyadic

namespace SixVertex
noncomputable section
open MeasureTheory Set
open scoped ENNReal

def absoluteLogEnergy (μ ν : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ p : ℂ × ℂ, logSingularity (dist p.1 p.2) ∂μ.prod ν

def proximityEnergy (μ ν : Measure ℂ) : ℝ≥0∞ :=
  ∫⁻ p : ℂ × ℂ, dyadicProximity (dist p.1 p.2) ∂μ.prod ν

def squareEnergy (μ : Measure ℂ) : ℝ≥0∞ :=
  ∑' j : ℕ, μ.prod μ (planeSameCellPairs j)

theorem proximityEnergy_series (μ ν : Measure ℂ) :
    proximityEnergy μ ν=∑' j, μ.prod ν (planeClosePairs j) := by
  change (∫⁻ p : ℂ × ℂ, ∑' j : ℕ, (planeClosePairs j).indicator 1 p ∂μ.prod ν)=_
  rw [lintegral_tsum]
  · congr 1
    funext j
    exact lintegral_indicator_one (planeClosePairs_measurable j)
  · intro j
    exact (measurable_const.indicator (planeClosePairs_measurable j)).aemeasurable

theorem squareEnergy_integral (μ : Measure ℂ) :
    squareEnergy μ=∫⁻ p : ℂ × ℂ, ∑' j : ℕ, (planeSameCellPairs j).indicator 1 p ∂μ.prod μ := by
  rw [lintegral_tsum]
  · unfold squareEnergy
    apply tsum_congr
    intro j
    exact (lintegral_indicator_one (planeSameCellPairs_measurable j)).symm
  · intro j
    exact (measurable_const.indicator (planeSameCellPairs_measurable j)).aemeasurable

theorem squareKernel_le_dyadic (p : ℂ × ℂ) :
    (∑' j : ℕ, (planeSameCellPairs j).indicator 1 p) ≤ 1+dyadicProximity (dist p.1 p.2) := by
  rw [tsum_eq_zero_add' ENNReal.summable]
  apply add_le_add
  · by_cases h : p ∈ planeSameCellPairs 0 <;> simp [h]
  · apply ENNReal.tsum_le_tsum
    intro j
    by_cases hs : p ∈ planeSameCellPairs (j+1)
    · have hd := planeDyadicCell_distance (j+1) p.1 p.2 hs
      have hp : 2*((2 : ℝ)^(j+1))⁻¹=((2 : ℝ)^j)⁻¹ := by
        rw [pow_succ,mul_inv]
        ring
      rw [hp] at hd
      simp only [Set.indicator_of_mem hs, Pi.one_apply, if_pos hd.le]
      exact le_rfl
    · simp [Set.indicator,hs]

theorem squareEnergy_bound (μ : Measure ℂ) :
    squareEnergy μ ≤ μ.prod μ univ+proximityEnergy μ μ := by
  rw [squareEnergy_integral]
  calc
    _ ≤ ∫⁻ p : ℂ × ℂ, 1+dyadicProximity (dist p.1 p.2) ∂μ.prod μ :=
      lintegral_mono squareKernel_le_dyadic
    _ = _ := by rw [lintegral_add_left measurable_const,lintegral_const]; simp [proximityEnergy]

/-- The discrete mixed estimate, summed over every scale. The finite
neighbor count is independent of the measures and the scale. -/
theorem proximityEnergy_mixed_bound (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    proximityEnergy μ ν ≤ 9*(squareEnergy μ+squareEnergy ν) := by
  rw [proximityEnergy_series]
  calc
    _ ≤ ∑' j, 9*(μ.prod μ (planeSameCellPairs j)+ν.prod ν (planeSameCellPairs j)) :=
      ENNReal.tsum_le_tsum (fun j => planeClosePairs_mass_bound μ ν j)
    _ = _ := by rw [ENNReal.tsum_mul_left,ENNReal.tsum_add]; rfl

theorem proximityEnergy_log_bound (μ ν : Measure ℂ) :
    proximityEnergy μ ν ≤ μ.prod ν univ+ENNReal.ofReal (1/Real.log 2)*absoluteLogEnergy μ ν := by
  calc
    _ ≤ ∫⁻ p : ℂ × ℂ, 1+ENNReal.ofReal (1/Real.log 2)*logSingularity (dist p.1 p.2) ∂μ.prod ν :=
      lintegral_mono (fun p => dyadicProximity_le_logSingularity _ dist_nonneg)
    _ = _ := by
      rw [lintegral_add_left measurable_const,lintegral_const,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      simp [absoluteLogEnergy]

theorem absoluteLogEnergy_proximity_bound (μ ν : Measure ℂ) :
    absoluteLogEnergy μ ν ≤ ENNReal.ofReal (Real.log 2)*(μ.prod ν univ+proximityEnergy μ ν) := by
  calc
    _ ≤ ∫⁻ p : ℂ × ℂ, ENNReal.ofReal (Real.log 2)*(1+dyadicProximity (dist p.1 p.2)) ∂μ.prod ν :=
      lintegral_mono (fun p => logSingularity_le_dyadicProximity _ dist_nonneg)
    _ = _ := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_left measurable_const,lintegral_const]
      simp [proximityEnergy]

/-- Finite self logarithmic energy implies finite mixed absolute energy.
This theorem is stronger than the compact-support instance of Lemma 7.6. -/
theorem absoluteLogEnergy_mixed_finite (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : absoluteLogEnergy μ μ < ⊤) (hν : absoluteLogEnergy ν ν < ⊤) :
    absoluteLogEnergy μ ν < ⊤ := by
  have hp : ∀ (a : Measure ℂ) [IsFiniteMeasure a], absoluteLogEnergy a a < ⊤ →
      proximityEnergy a a < ⊤ := by
    intro a ha hlog
    exact (proximityEnergy_log_bound a a).trans_lt
      (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hlog⟩)
  have hs : ∀ (a : Measure ℂ) [IsFiniteMeasure a], absoluteLogEnergy a a < ⊤ →
      squareEnergy a < ⊤ := by
    intro a ha hlog
    exact (squareEnergy_bound a).trans_lt (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _,hp a hlog⟩)
  have hm : proximityEnergy μ ν < ⊤ :=
    (proximityEnergy_mixed_bound μ ν).trans_lt
      (ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hs μ hμ,hs ν hν⟩))
  exact (absoluteLogEnergy_proximity_bound μ ν).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.add_lt_top.mpr ⟨measure_lt_top _ _,hm⟩))

end
end SixVertex
