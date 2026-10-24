import SixVertex.KernelDecay
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

namespace SixVertex
open Filter Topology Set MeasureTheory

/-- A nonnegative derivative with finite limits at both real ends is
integrable. Both half-line integrability obligations are proved. -/
theorem integrable_nonnegative_derivative_limits (f g : ℝ → ℝ) (a b : ℝ)
    (hd : ∀ u, HasDerivAt f (g u) u) (hg : ∀ u, 0 ≤ g u)
    (hbot : Tendsto f atBot (𝓝 a)) (htop : Tendsto f atTop (𝓝 b)) : Integrable g := by
  have hright : IntegrableOn g (Ioi (0 : ℝ)) :=
    integrableOn_Ioi_deriv_of_nonneg' (fun u hu => hd u) (fun u hu => hg u) htop
  have hreflect : IntegrableOn (fun u => -g (-u)) (Ioi (0 : ℝ)) := by
    apply integrableOn_Ioi_deriv_of_nonpos' (g := fun u => f (-u))
      (fun u hu => ?_) (fun u hu => neg_nonpos.mpr (hg (-u)))
      (hbot.comp tendsto_neg_atTop_atBot)
    simpa only [Function.comp_def,mul_neg_one] using (hd (-u)).comp u (hasDerivAt_neg' u)
  have hleftOpen : IntegrableOn g (Iio (0 : ℝ)) := by
    apply (MeasurePreserving.integrableOn_comp_preimage (Measure.measurePreserving_neg volume)
      (Homeomorph.neg ℝ).measurableEmbedding).mp
    have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' Iio (0 : ℝ) = Ioi 0 := by ext x; simp
    rw [hpre]
    simpa only [Function.comp_def,Pi.neg_def,neg_neg] using hreflect.neg
  have hleft : IntegrableOn g (Iic (0 : ℝ)) := (integrableOn_Iic_iff_integrableOn_Iio (f := g) (b := (0 : ℝ))).mpr hleftOpen
  rw [← integrableOn_univ,← Iic_union_Ioi (a := (0 : ℝ)),integrableOn_union]
  exact ⟨hleft,hright⟩

theorem kernelK_nonneg (lam u : ℝ) (h0 : 0 < lam) (hhalf : lam ≤ Real.pi/2) :
    0 ≤ kernelK lam u := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have hs := Real.sin_pos_of_pos_of_lt_pi h0 hpi
  have hc : 0 ≤ Real.cos lam := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hhalf
  unfold kernelK phaseDensity
  rw [Real.sin_two_mul]
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hs.le) hc)
    (mul_pos Real.pi_pos (phase_denominator_pos lam u hs.ne')).le

theorem kernelK_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Integrable (kernelK lam) := by
  have hd := fun u => hasDerivAt_countingTheta lam u h0 hpi
  have htop : Tendsto (countingTheta lam) atTop (𝓝 (phaseEnd lam)) :=
    barePhase_tendsto_atTop atTop (fun _ => lam) id lam h0 hpi tendsto_const_nhds tendsto_id
  have hbot : Tendsto (countingTheta lam) atBot (𝓝 (-phaseEnd lam)) :=
    barePhase_tendsto_atBot atBot (fun _ => lam) id lam h0 hpi tendsto_const_nhds tendsto_id
  by_cases hhalf : Real.pi/2 ≤ lam
  · have hi := integrable_nonnegative_derivative_limits (fun u => -countingTheta lam u)
      (fun u => -kernelK lam u) (phaseEnd lam) (-phaseEnd lam)
      (fun u => (hd u).neg) (fun u => neg_nonneg.mpr (kernelK_nonpos lam u hhalf hpi))
      (by simpa only [neg_neg] using hbot.neg) htop.neg
    simpa only [Pi.neg_def,neg_neg] using hi.neg
  · exact integrable_nonnegative_derivative_limits (countingTheta lam) (kernelK lam)
      (-phaseEnd lam) (phaseEnd lam) hd (fun u => kernelK_nonneg lam u h0 (le_of_not_ge hhalf)) hbot htop

theorem integral_kernelK (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    (∫ u : ℝ, kernelK lam u) = 1-2*lam/Real.pi := by
  have htop : Tendsto (countingTheta lam) atTop (𝓝 (phaseEnd lam)) :=
    barePhase_tendsto_atTop atTop (fun _ => lam) id lam h0 hpi tendsto_const_nhds tendsto_id
  have hbot : Tendsto (countingTheta lam) atBot (𝓝 (-phaseEnd lam)) :=
    barePhase_tendsto_atBot atBot (fun _ => lam) id lam h0 hpi tendsto_const_nhds tendsto_id
  rw [integral_of_hasDerivAt_of_tendsto (fun u => hasDerivAt_countingTheta lam u h0 hpi)
    (kernelK_integrable lam h0 hpi) hbot htop]
  unfold phaseEnd
  ring

/-- The exact L1 mass, in the manuscript's normalization, throughout
0 < lambda < pi. The zero kernel at lambda = pi/2 is included. -/
theorem integral_abs_kernelK (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    (∫ u : ℝ, |kernelK lam u|) = |1-2*lam/Real.pi| := by
  by_cases hhalf : Real.pi/2 ≤ lam
  · have he : (fun u => |kernelK lam u|) = fun u => -kernelK lam u :=
      funext (fun u => abs_of_nonpos (kernelK_nonpos lam u hhalf hpi))
    have hh : 1-2*lam/Real.pi ≤ 0 := by
      have hq : (1 : ℝ) ≤ 2*lam/Real.pi := (le_div_iff₀ Real.pi_pos).mpr (by linarith)
      linarith
    rw [he,integral_neg,integral_kernelK lam h0 hpi,abs_of_nonpos hh]
  · have he : (fun u => |kernelK lam u|) = kernelK lam :=
      funext (fun u => abs_of_nonneg (kernelK_nonneg lam u h0 (le_of_not_ge hhalf)))
    have hh : 0 ≤ 1-2*lam/Real.pi := by
      have hq : 2*lam/Real.pi ≤ (1 : ℝ) := (div_le_one Real.pi_pos).mpr (by linarith)
      linarith
    rw [he,integral_kernelK lam h0 hpi,abs_of_nonneg hh]

/-- The strict contraction constant used by the full-line Neumann series
is verified; no inverse or infinite-volume convergence is assumed here. -/
theorem kernelK_L1_mass_lt_one (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    (∫ u : ℝ, |kernelK lam u|) < 1 := by
  rw [integral_abs_kernelK lam h0 hpi]
  have hp : 0 < lam/Real.pi := div_pos h0 Real.pi_pos
  have hl : lam/Real.pi < 1 := (div_lt_one Real.pi_pos).mpr hpi
  rw [show 2*lam/Real.pi = 2*(lam/Real.pi) by ring]
  apply abs_lt.mpr
  constructor <;> linarith

theorem kernelS_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Integrable (kernelS lam) := by
  apply integrable_nonnegative_derivative_limits (countingS lam) (kernelS lam)
    (-phaseEnd (lam/2)) (phaseEnd (lam/2)) (fun u => hasDerivAt_countingS lam u h0 hpi)
    (fun u => (kernelS_pos lam u h0 hpi).le)
  · exact barePhase_tendsto_atBot atBot (fun _ => lam/2) id (lam/2) (by linarith)
      (by linarith [Real.pi_pos]) tendsto_const_nhds tendsto_id
  · exact barePhase_tendsto_atTop atTop (fun _ => lam/2) id (lam/2) (by linarith)
      (by linarith [Real.pi_pos]) tendsto_const_nhds tendsto_id

theorem integral_kernelS (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    (∫ u : ℝ, kernelS lam u) = 1-lam/Real.pi := by
  have ht := barePhase_tendsto_atTop atTop (fun _ => lam/2) id (lam/2) (by linarith : 0 < lam/2)
    (by linarith [Real.pi_pos]) tendsto_const_nhds tendsto_id
  have hb := barePhase_tendsto_atBot atBot (fun _ => lam/2) id (lam/2) (by linarith : 0 < lam/2)
    (by linarith [Real.pi_pos]) tendsto_const_nhds tendsto_id
  rw [integral_of_hasDerivAt_of_tendsto (fun u => hasDerivAt_countingS lam u h0 hpi)
    (kernelS_integrable lam h0 hpi) hb ht]
  unfold phaseEnd
  ring

end SixVertex
