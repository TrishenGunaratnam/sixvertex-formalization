import SixVertex.CountingMass
import SixVertex.KernelDerivatives
import Mathlib.Analysis.Calculus.MeanValue

namespace SixVertex
open MeasureTheory Filter Topology Set

noncomputable def countingCurvature {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℝ) : ℝ :=
  (∑ a ∈ Finset.range L, kernelSPrime lam (u-b a))-∑ j, kernelKPrime lam (u-Y j)

noncomputable def kernelLogConstant (lam : ℝ) : ℝ :=
  2/(Real.sin (lam/2))^2+2/(Real.sin lam)^2

theorem kernelLogConstant_nonneg (lam : ℝ) : 0 ≤ kernelLogConstant lam := by
  unfold kernelLogConstant
  positivity

theorem hasDerivAt_countingSlope {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    HasDerivAt (countingSlope lam b L Y) (countingCurvature lam b L Y u) u := by
  unfold countingSlope countingCurvature
  apply HasDerivAt.sub
  · apply HasDerivAt.fun_sum
    intro a ha
    simpa only [Function.comp_def,id_eq,mul_one] using
      (hasDerivAt_kernelS lam (u-b a) h0 hpi).comp u ((hasDerivAt_id u).sub_const (b a))
  · apply HasDerivAt.fun_sum
    intro j hj
    simpa only [Function.comp_def,id_eq,mul_one] using
      (hasDerivAt_kernelK lam (u-Y j) h0 hpi).comp u ((hasDerivAt_id u).sub_const (Y j))

theorem continuous_countingCurvature {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Continuous (countingCurvature lam b L Y) := by
  have hs : Continuous (kernelSPrime lam) := continuous_phaseDensityPrime (lam/2)
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have hk : Continuous (kernelKPrime lam) := continuous_phaseDensityPrime lam
    (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  unfold countingCurvature
  apply Continuous.sub
  · apply continuous_finset_sum
    intro a ha
    exact hs.comp (continuous_id.sub continuous_const)
  · apply continuous_finset_sum
    intro j hj
    exact hk.comp (continuous_id.sub continuous_const)

/-- The relative-derivative estimate in the proof of Lemma 3.1, with an
explicit constant depending only on lambda. It is uniform in the chain
length, the real site array, the real root list and the argument u. -/
theorem countingCurvature_relative_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    |countingCurvature lam b L Y u| ≤ kernelLogConstant lam*countingSlope lam b L Y u := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hsC : 2/(Real.sin (lam/2))^2 ≤ kernelLogConstant lam := by
    unfold kernelLogConstant
    have hn : 0 ≤ 2/(Real.sin lam)^2 := by positivity
    linarith
  have hkC : 2/(Real.sin lam)^2 ≤ kernelLogConstant lam := by
    unfold kernelLogConstant
    have hn : 0 ≤ 2/(Real.sin (lam/2))^2 := by positivity
    linarith
  have hs (a : ℕ) : |kernelSPrime lam (u-b a)| ≤ kernelLogConstant lam*kernelS lam (u-b a) :=
    (kernelSPrime_relative_bound lam _ h0 hpi).trans
      (mul_le_mul_of_nonneg_right hsC (kernelS_pos lam _ h0 hpi).le)
  have hk (j : Fin n) : |kernelKPrime lam (u-Y j)| ≤ kernelLogConstant lam*|kernelK lam (u-Y j)| :=
    (kernelKPrime_relative_bound lam _ h0 hpi).trans (mul_le_mul_of_nonneg_right hkC (abs_nonneg _))
  have hkabs : (∑ j : Fin n, |kernelK lam (u-Y j)|)=-(∑ j : Fin n, kernelK lam (u-Y j)) := by
    simp_rw [abs_of_nonpos (kernelK_nonpos lam _ hhalf hpi)]
    rw [Finset.sum_neg_distrib]
  unfold countingCurvature
  calc
    _ ≤ |∑ a ∈ Finset.range L, kernelSPrime lam (u-b a)|+|∑ j, kernelKPrime lam (u-Y j)| := by
      simpa only [Real.norm_eq_abs] using norm_sub_le
        (∑ a ∈ Finset.range L, kernelSPrime lam (u-b a)) (∑ j, kernelKPrime lam (u-Y j))
    _ ≤ (∑ a ∈ Finset.range L, |kernelSPrime lam (u-b a)|)+∑ j, |kernelKPrime lam (u-Y j)| :=
      add_le_add (Finset.abs_sum_le_sum_abs _ _) (Finset.abs_sum_le_sum_abs _ _)
    _ ≤ (∑ a ∈ Finset.range L, kernelLogConstant lam*kernelS lam (u-b a))+
        ∑ j, kernelLogConstant lam*|kernelK lam (u-Y j)| :=
      add_le_add (Finset.sum_le_sum (fun a ha => hs a)) (Finset.sum_le_sum (fun j hj => hk j))
    _ = _ := by
      rw [← Finset.mul_sum,← Finset.mul_sum,hkabs]
      unfold countingSlope
      ring

theorem countingCurvature_integrable {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    Integrable (countingCurvature lam b L Y) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  apply ((countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi).const_mul
    (kernelLogConstant lam)).mono' (continuous_countingCurvature lam b L Y h0 hpi).aestronglyMeasurable
  exact Eventually.of_forall (fun u => by
    simpa only [Real.norm_eq_abs] using countingCurvature_relative_bound lam b L Y hhalf hpi u)

theorem hasDerivAt_log_countingSlope {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    HasDerivAt (fun v => Real.log (countingSlope lam b L Y v))
      (countingCurvature lam b L Y u/countingSlope lam b L Y u) u := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  exact (hasDerivAt_countingSlope lam b L Y u h0 hpi).log
    (countingSlope_pos_nonpositiveK lam b L hL Y u hhalf hpi).ne'

theorem log_countingSlope_derivative_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    |countingCurvature lam b L Y u/countingSlope lam b L Y u| ≤ kernelLogConstant lam := by
  have hp:=countingSlope_pos_nonpositiveK lam b L hL Y u hhalf hpi
  rw [abs_div,abs_of_pos hp]
  exact (div_le_iff₀ hp).mpr (countingCurvature_relative_bound lam b L Y hhalf hpi u)

/-- Quantitative variation of the actual counting density, including
sparse cells: its logarithm has a chain-independent Lipschitz constant. -/
theorem log_countingSlope_lipschitz_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u v : ℝ) :
    |Real.log (countingSlope lam b L Y v)-Real.log (countingSlope lam b L Y u)| ≤
      kernelLogConstant lam*|v-u| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ (univ : Set ℝ)) =>
      (hasDerivAt_log_countingSlope lam b L hL Y hhalf hpi x).hasDerivWithinAt)
    (fun x (_ : x ∈ (univ : Set ℝ)) => by
      simpa only [Real.norm_eq_abs] using log_countingSlope_derivative_bound lam b L hL Y hhalf hpi x)
    (convex_univ : Convex ℝ (univ : Set ℝ)) (mem_univ u) (mem_univ v)
  simpa only [Real.norm_eq_abs] using h

/-- Both directions of density comparison follow from the actual log
bound; no positive lower density is assumed at infinity. -/
theorem countingSlope_exponential_comparison {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u v : ℝ) :
    Real.exp (-(kernelLogConstant lam*|v-u|))*countingSlope lam b L Y u ≤ countingSlope lam b L Y v ∧
      countingSlope lam b L Y v ≤ Real.exp (kernelLogConstant lam*|v-u|)*countingSlope lam b L Y u := by
  have hu:=countingSlope_pos_nonpositiveK lam b L hL Y u hhalf hpi
  have hv:=countingSlope_pos_nonpositiveK lam b L hL Y v hhalf hpi
  have hh:=abs_le.mp (log_countingSlope_lipschitz_bound lam b L hL Y hhalf hpi u v)
  have hlo:=Real.exp_le_exp.mpr hh.1
  have hhi:=Real.exp_le_exp.mpr hh.2
  rw [Real.exp_sub,Real.exp_log hv,Real.exp_log hu] at hlo hhi
  exact ⟨(le_div_iff₀ hu).mp hlo,(div_le_iff₀ hu).mp hhi⟩

theorem kernelK_strict_neg (lam u : ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    kernelK lam u < 0 := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hpos:=Real.sin_pos_of_pos_of_lt_pi (by linarith : 0 < 2*lam-Real.pi)
    (by linarith : 2*lam-Real.pi < Real.pi)
  have he : Real.sin (2*lam) = -Real.sin (2*lam-Real.pi) := by
    simpa only [sub_add_cancel] using Real.sin_add_pi (2*lam-Real.pi)
  have hs : Real.sin (2*lam) < 0 := by rw [he]; linarith
  exact div_neg_of_neg_of_pos hs (mul_pos Real.pi_pos
    (phase_denominator_pos lam u (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'))

/-- Each root contributes its own positive -K(0) to the counting
density. This yields a uniform atom-weight bound in the strict
negative-kernel regime, without assuming any density asymptotics. -/
theorem countingSlope_root_lower_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (j : Fin n) :
    -kernelK lam 0 ≤ countingSlope lam b L Y (Y j) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hs : 0 ≤ ∑ a ∈ Finset.range L, kernelS lam (Y j-b a) :=
    Finset.sum_nonneg (fun a ha => (kernelS_pos lam _ h0 hpi).le)
  have hk := Finset.single_le_sum (s := Finset.univ) (f := fun k : Fin n => -kernelK lam (Y j-Y k))
    (fun k hk => neg_nonneg.mpr (kernelK_nonpos lam _ hhalf hpi)) (Finset.mem_univ j)
  simp only [sub_self,Finset.sum_neg_distrib] at hk
  unfold countingSlope
  linarith

theorem reciprocal_countingSlope_root_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) (j : Fin n) :
    (countingSlope lam b L Y (Y j))⁻¹ ≤ (-kernelK lam 0)⁻¹ := by
  have hp : 0 < -kernelK lam 0 := neg_pos.mpr (kernelK_strict_neg lam 0 hhalf hpi)
  simpa only [one_div] using one_div_le_one_div_of_le hp
    (countingSlope_root_lower_bound lam b L Y hhalf.le hpi j)

end SixVertex
