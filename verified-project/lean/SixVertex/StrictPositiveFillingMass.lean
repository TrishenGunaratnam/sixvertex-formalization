import SixVertex.PositiveWindowMass
import SixVertex.PositiveWindowMonotone
import SixVertex.StrictFillingMass

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

/-- Exact ordinary exterior-mass identity for the actual finite-window
density, valid for every physical parameter. -/
theorem finiteIntervalMass_deficit_exterior_identity (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) :
    2*(1-lam/Real.pi)*(1/2-finiteIntervalMass lam h0 hpi Q)=
      ∫ u in (Icc (-Q) Q)ᶜ,finiteIntervalDensity lam h0 hpi Q u := by
  have hs : finiteIntervalMass lam h0 hpi Q+
      (∫ u in (Icc (-Q) Q)ᶜ,finiteIntervalDensity lam h0 hpi Q u)=
      ∫ u : ℝ,finiteIntervalDensity lam h0 hpi Q u :=
    integral_add_compl measurableSet_Icc (finiteIntervalDensity_integrable lam h0 hpi Q)
  have hm := finiteIntervalDensity_total_mass_equation lam h0 hpi Q
  rw [show 2*lam/Real.pi=2*(lam/Real.pi) by ring] at hm
  nlinarith only [hs,hm]

/-- The actual filling mass is strictly increasing for positive K.
The proof uses exterior integrals and their strict lost-band mass,
without assuming an endpoint differentiation formula. -/
theorem finiteIntervalMass_strictMonoOn_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) :
    StrictMonoOn (finiteIntervalMass lam h0 (by linarith [Real.pi_pos])) (Ici (0 : ℝ)) := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  intro Q hQ T hT hQT
  change 0 ≤ Q at hQ
  change 0 ≤ T at hT
  let f := finiteIntervalDensity lam h0 hpi Q
  let g := finiteIntervalDensity lam h0 hpi T
  have hf := finiteIntervalDensity_integrable lam h0 hpi Q
  have hg := finiteIntervalDensity_integrable lam h0 hpi T
  have hi (a b : ℝ) : IntervalIntegrable (fun u => f u) volume a b := f.continuous.intervalIntegrable a b
  have hp : 0 < ∫ u in Q..T,f u := intervalIntegral.integral_pos hQT f.continuous.continuousOn
    (fun u _ => (finiteIntervalDensity_pos_positiveK lam h0 hh Q u).le)
    ⟨Q,⟨le_rfl,hQT.le⟩,finiteIntervalDensity_pos_positiveK lam h0 hh Q Q⟩
  have hn : 0 ≤ ∫ u in -T..(-Q),f u := intervalIntegral.integral_nonneg (by linarith)
    (fun u _ => (finiteIntervalDensity_pos_positiveK lam h0 hh Q u).le)
  have ha := intervalIntegral.integral_add_adjacent_intervals (hi (-T) (-Q)) (hi (-Q) Q)
  have hb := intervalIntegral.integral_add_adjacent_intervals (hi (-T) Q) (hi Q T)
  have hsplitQ := integral_add_compl (s := Icc (-Q) Q) measurableSet_Icc hf
  have hsplitT := integral_add_compl (s := Icc (-T) T) measurableSet_Icc hf
  have hq : (∫ u in Icc (-Q) Q,f u)=∫ u in -Q..Q,f u := by
    rw [intervalIntegral.integral_of_le (by linarith : -Q ≤ Q),← integral_Icc_eq_integral_Ioc]
  have ht : (∫ u in Icc (-T) T,f u)=∫ u in -T..T,f u := by
    rw [intervalIntegral.integral_of_le (by linarith : -T ≤ T),← integral_Icc_eq_integral_Ioc]
  change (∫ u in Icc (-Q) Q,f u)+(∫ u in (Icc (-Q) Q)ᶜ,f u)=∫ u : ℝ,f u at hsplitQ
  change (∫ u in Icc (-T) T,f u)+(∫ u in (Icc (-T) T)ᶜ,f u)=∫ u : ℝ,f u at hsplitT
  rw [hq] at hsplitQ
  rw [ht] at hsplitT
  have hout : (∫ u in (Icc (-T) T)ᶜ,g u) ≤ ∫ u in (Icc (-T) T)ᶜ,f u :=
    integral_mono hg.integrableOn hf.integrableOn
      (finiteIntervalDensity_antitone_Q_positiveK lam h0 hh Q T hQT.le)
  have hstrict : (∫ u in (Icc (-T) T)ᶜ,g u)<∫ u in (Icc (-Q) Q)ᶜ,f u := by
    linarith only [hp,hn,ha,hb,hsplitQ,hsplitT,hout]
  have hdQ := finiteIntervalMass_deficit_exterior_identity lam h0 hpi Q
  have hdT := finiteIntervalMass_deficit_exterior_identity lam h0 hpi T
  have hd : 0 < 2*(1-lam/Real.pi) := mul_pos (by norm_num)
    (sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hpi))
  change 2*(1-lam/Real.pi)*(1/2-finiteIntervalMass lam h0 hpi Q)=∫ u in (Icc (-Q) Q)ᶜ,f u at hdQ
  change 2*(1-lam/Real.pi)*(1/2-finiteIntervalMass lam h0 hpi T)=∫ u in (Icc (-T) T)ᶜ,g u at hdT
  nlinarith only [hstrict,hdQ,hdT,hd]

/-- Every strictly sub-half filling has a unique actual nonnegative
cutoff in the positive-kernel regime. -/
theorem exists_unique_finiteIntervalCutoff_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (rho : ℝ) (hrho : 0 < rho) (hrhalf : rho < 1/2) :
    ∃! Q : ℝ,0 ≤ Q ∧ finiteIntervalMass lam h0 (by linarith [Real.pi_pos]) Q=rho := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have he := (finiteIntervalMass_tendsto_half_positiveK lam h0 hh).eventually (Ioi_mem_nhds hrhalf)
  obtain ⟨A,hA,hm⟩ := ((eventually_ge_atTop (1 : ℝ)).and he).exists
  have hA0 : 0 ≤ A := by linarith
  have hin : rho ∈ Icc (finiteIntervalMass lam h0 hpi 0) (finiteIntervalMass lam h0 hpi A) := by
    rw [finiteIntervalMass_zero]
    exact ⟨hrho.le,hm.le⟩
  obtain ⟨Q,hQI,hQeq⟩ := intermediate_value_Icc hA0 (continuousOn_finiteIntervalMass_Icc lam h0 hpi A hA0) hin
  refine ⟨Q,⟨hQI.1,hQeq⟩,?_⟩
  intro T hT
  exact (finiteIntervalMass_strictMonoOn_positiveK lam h0 hh).injOn hT.1 hQI.1 (hT.2.trans hQeq.symm)

end
end SixVertex
