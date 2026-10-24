import SixVertex.CompactCountingError
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.Deriv.Support

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set
open scoped NNReal

theorem deriv_zero_outside_Icc (f : ℝ → ℝ) (a z : ℝ)
    (hs : ∀ x, x ∉ Icc a z → f x=0) (x : ℝ) (hx : x ∉ Icc a z) : deriv f x=0 := by
  apply deriv_of_notMem_tsupport
  have ht : tsupport f ⊆ Icc a z := by
    apply closure_minimal _ isClosed_Icc
    intro y hy
    by_contra hn
    exact hy (hs y hn)
  exact fun hm => hx (ht hm)

theorem lipschitz_compact_deriv_integrable (f : ℝ → ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K f) (a z : ℝ) (haz : a ≤ z)
    (hs : ∀ x, x ∉ Icc a z → f x=0) : Integrable (deriv f) := by
  have hac : AbsolutelyContinuousOnInterval f a z :=
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval
  have hi : IntegrableOn (deriv f) (Icc a z) := by
    rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact hac.intervalIntegrable_deriv.1
  have hj := hi.integrable_indicator measurableSet_Icc
  have he : (Icc a z).indicator (deriv f)=deriv f := by
    funext x
    by_cases hx : x ∈ Icc a z
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx,deriv_zero_outside_Icc f a z hs x hx]
  rwa [he] at hj

theorem compact_test_eventually_zero_atTop (f : ℝ → ℝ) (a z : ℝ)
    (hs : ∀ x, x ∉ Icc a z → f x=0) : ∀ᶠ x in atTop, f x=0 := by
  filter_upwards [eventually_ge_atTop (z+1)] with x hx
  exact hs x (fun hh => by have hz := hh.2; linarith)

theorem compact_test_eventually_zero_atBot (f : ℝ → ℝ) (a z : ℝ)
    (hs : ∀ x, x ∉ Icc a z → f x=0) : ∀ᶠ x in atBot, f x=0 := by
  filter_upwards [eventually_le_atBot (a-1)] with x hx
  exact hs x (fun hh => by have ha := hh.1; linarith)

theorem integral_deriv_Ici_lipschitz_compact (f : ℝ → ℝ) (K : ℝ≥0)
    (hLip : LipschitzWith K f) (a z : ℝ) (haz : a ≤ z)
    (hs : ∀ x, x ∉ Icc a z → f x=0) (y : ℝ) :
    (∫ x in Ici y, deriv f x)= -f y := by
  have hi := lipschitz_compact_deriv_integrable f K hLip a z haz hs
  have ht := intervalIntegral_tendsto_integral_Ioi y hi.integrableOn tendsto_id
  have hf : ∀ t : ℝ, (∫ x in y..t, deriv f x)=f t-f y := fun t =>
    hLip.lipschitzOnWith.absolutelyContinuousOnInterval.integral_deriv_eq_sub
  simp_rw [hf] at ht
  have hz : Tendsto f atTop (𝓝 0) := tendsto_const_nhds.congr'
    ((compact_test_eventually_zero_atTop f a z hs).mono (fun _ hx => hx.symm))
  rw [integral_Ici_eq_integral_Ioi]
  have hl := tendsto_nhds_unique ht (hz.sub_const (f y))
  simpa only [zero_sub] using hl

/-- Actual integration by parts for compact Lipschitz tests and a smooth
bounded primitive. The test derivative is only required almost everywhere. -/
theorem integral_lipschitz_compact_primitive (f P p : BoundedRealFunction)
    (K : ℝ≥0) (hLip : LipschitzWith K (fun x => f x))
    (a z : ℝ) (haz : a ≤ z) (hs : ∀ x, x ∉ Icc a z → f x=0)
    (hp : Integrable (fun x => p x))
    (hdP : ∀ x, HasDerivAt (fun v => P v) (p x) x) :
    (∫ x : ℝ, f x*p x)= -(∫ x : ℝ, deriv (fun v => f v) x*P x) := by
  have hPLip : LipschitzWith ‖p‖₊ (fun x => P x) := by
    apply lipschitzWith_of_nnnorm_deriv_le (fun x => (hdP x).differentiableAt)
    intro x
    rw [(hdP x).deriv]
    exact_mod_cast p.norm_coe_le_norm x
  have hfp : Integrable (fun x : ℝ => f x*p x) := by
    have h := hp.mul_bdd f.continuous.aestronglyMeasurable (Eventually.of_forall f.norm_coe_le_norm)
    simpa only [mul_comm] using h
  have hdint := lipschitz_compact_deriv_integrable (fun x => f x) K hLip a z haz hs
  have hdPint : Integrable (fun x : ℝ => deriv (fun v => f v) x*P x) :=
    hdint.mul_bdd P.continuous.aestronglyMeasurable (Eventually.of_forall P.norm_coe_le_norm)
  have hFTC (r t : ℝ) : (∫ x in r..t, f x*p x)=
      f t*P t-f r*P r-(∫ x in r..t, deriv (fun v => f v) x*P x) := by
    have h := hLip.lipschitzOnWith.absolutelyContinuousOnInterval.integral_mul_deriv_eq_deriv_mul
      hPLip.lipschitzOnWith.absolutelyContinuousOnInterval (a := r) (b := t)
    simp_rw [show ∀ x, deriv (fun v => P v) x=p x from fun x => (hdP x).deriv] at h
    exact h
  have hleft := intervalIntegral_tendsto_integral hfp tendsto_neg_atTop_atBot tendsto_id
  have hright := intervalIntegral_tendsto_integral hdPint tendsto_neg_atTop_atBot tendsto_id
  have hzero : ∀ᶠ t : ℝ in atTop, f t*P t-f (-t)*P (-t)=0 := by
    filter_upwards [compact_test_eventually_zero_atTop (fun x => f x) a z hs,
      tendsto_neg_atTop_atBot.eventually (compact_test_eventually_zero_atBot (fun x => f x) a z hs)]
      with t ht hb
    rw [ht,hb]
    simp
  have hz : Tendsto (fun t : ℝ => f t*P t-f (-t)*P (-t)) atTop (𝓝 0) :=
    tendsto_const_nhds.congr' (hzero.mono (fun _ hx => hx.symm))
  have he : (fun t : ℝ => ∫ x in -t..t, f x*p x)=
      fun t => f t*P t-f (-t)*P (-t)-(∫ x in -t..t, deriv (fun v => f v) x*P x) :=
    funext (fun t => hFTC (-t) t)
  simp only [id_eq] at hleft hright
  rw [he] at hleft
  have hh := tendsto_nhds_unique hleft (hz.sub hright)
  simpa only [zero_sub] using hh

end
end SixVertex
