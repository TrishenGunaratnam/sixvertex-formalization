import SixVertex.WeightedCountingPhase
import SixVertex.KernelTailProfile

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology

/-- Fixed unit bands on either side of a compact test interval have
positive actual r_Q mass uniformly in every larger cutoff. -/
theorem exists_reference_cumulative_margin (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (A : ℝ) (hA : 0 ≤ A) :
    ∃ d : ℝ, 0 < d ∧ ∀ Q : ℝ, A+1 ≤ Q → ∀ u ∈ Icc (-A) A,
      d ≤ finiteIntervalCumulative lam h0 hpi Q u ∧
      d ≤ finiteIntervalMass lam h0 hpi Q-finiteIntervalCumulative lam h0 hpi Q u := by
  have hs := kernelS_positive_tail_data lam h0 hpi
  let d : ℝ := (Real.sin lam/(2*Real.pi))*Real.exp (-2*(A+1))
  have hd : 0 < d := mul_pos hs.lower_pos (Real.exp_pos _)
  have hlo (Q x : ℝ) (hx : x ∈ Icc (-(A+1)) (A+1)) : d ≤ finiteIntervalDensity lam h0 hpi Q x := by
    have hab : |x| ≤ A+1 := abs_le.mpr hx
    apply le_trans _ (finiteIntervalDensity_ge_source lam h0 hhalf hpi Q x)
    apply le_trans _ (hs.lower x)
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) hs.lower_pos.le
  have hunit (Q a : ℝ) (ha : -(A+1) ≤ a) (hb : a+1 ≤ A+1) :
      d ≤ ∫ x in a..(a+1), finiteIntervalDensity lam h0 hpi Q x := by
    have hh := intervalIntegral.integral_mono_on (a := a) (b := a+1) (by linarith)
      (continuous_const.intervalIntegrable (μ := volume) a (a+1))
      ((finiteIntervalDensity lam h0 hpi Q).continuous.intervalIntegrable (μ := volume) a (a+1))
      (fun x hx => hlo Q x ⟨ha.trans hx.1,hx.2.trans hb⟩)
    simpa only [intervalIntegral.integral_const,smul_eq_mul,add_sub_cancel_left,one_mul] using hh
  refine ⟨d,hd,?_⟩
  intro Q hQ u hu
  let r := finiteIntervalDensity lam h0 hpi Q
  have hpos : ∀ x : ℝ, 0 ≤ r x := fun x => (finiteIntervalDensity_pos lam h0 hhalf hpi Q x).le
  have hleft := hunit Q (-A-1) (by linarith) (by linarith)
  have hright := hunit Q A (by linarith) (by linarith)
  have hl := intervalIntegral.integral_mono_interval (a := -A-1) (b := -A-1+1) (c := -Q) (d := u)
    (by linarith) (by linarith) (by linarith [hu.1]) (Eventually.of_forall hpos)
    (r.continuous.intervalIntegrable (μ := volume) (-Q) u)
  have hr := intervalIntegral.integral_mono_interval (a := A) (b := A+1) (c := u) (d := Q)
    hu.2 (by linarith) hQ (Eventually.of_forall hpos)
    (r.continuous.intervalIntegrable (μ := volume) u Q)
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (r.continuous.intervalIntegrable (μ := volume) (-Q) u)
    (r.continuous.intervalIntegrable (μ := volume) u Q)
  change finiteIntervalCumulative lam h0 hpi Q u+(∫ x in u..Q, r x)=finiteIntervalCumulative lam h0 hpi Q Q at hadd
  rw [finiteIntervalCumulative_right lam h0 hpi Q (by linarith)] at hadd
  constructor
  · exact hleft.trans hl
  · have hh := hright.trans hr
    linarith

/-- A compact interval strictly inside the reference cutoff eventually
lies in the actual corrected counting window, with all thresholds fixed
before the finite configurations. -/
theorem exists_reference_occupied_counting_window (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (A : ℝ) (hA : 0 ≤ A) :
    ∃ threshold : ℝ, ∃ N : ℕ, 0 < threshold ∧
      ∀ (n L : ℕ) (Q : ℝ) (Y Z : Fin n → ℝ), ∀ R : ReferenceQuantileData lam h0 hpi Q L Y,
      N ≤ L → A+1 ≤ Q → threshold ≤ (L : ℝ)*fullLineDensityFunction lam h0 hpi Q →
      countingSystem lam (fun _ => 0) L Z=countingTarget n 0 →
      ∀ u ∈ Icc (-A) A, -(n : ℝ)/2 ≤ countingXi lam (fun _ => 0) L Z u ∧
        countingXi lam (fun _ => 0) L Z u ≤ (n : ℝ)/2 := by
  obtain ⟨M,C,hM,_,herror⟩ := uniform_corrected_counting_primitive_error lam h0 hhalf hpi
  obtain ⟨d,hd,hmargin⟩ := exists_reference_cumulative_margin lam h0 hhalf hpi A hA
  let c := 1-kernelL1Mass (kernelK lam)
  have hc : 0 < c := sub_pos.mpr (kernelK_L1_mass_lt_one lam h0 hpi)
  obtain ⟨N,hN⟩ := exists_nat_gt (C/d)
  refine ⟨M/c,N,div_pos hM hc,?_⟩
  intro n L Q Y Z R hL hQ hboundary hZ u hu
  have hMd : M ≤ ((L : ℝ)*fullLineDensityFunction lam h0 hpi Q)*c := (div_le_iff₀ hc).mp hboundary
  have hlower : ∀ v ∈ Icc (-Q) Q, M ≤ (L : ℝ)*finiteIntervalDensity lam h0 hpi Q v := by
    intro v hv
    have hh := mul_le_mul_of_nonneg_left
      (finiteIntervalDensity_boundary_lower lam h0 hhalf hpi Q R.interval_nonneg v hv)
      (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
    nlinarith only [hh,hMd]
  have he := abs_le.mp (herror n Q L Y Z R hlower hZ u)
  have hm := hmargin Q hQ u hu
  have hCd : C ≤ (L : ℝ)*d := ((div_lt_iff₀ hd).mp (hN.trans_le (Nat.cast_le.mpr hL))).le
  have hlo := mul_le_mul_of_nonneg_left hm.1 (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  have hhi := mul_le_mul_of_nonneg_left hm.2 (Nat.cast_nonneg L : (0 : ℝ) ≤ L)
  constructor <;> nlinarith [R.mass]

end
end SixVertex
