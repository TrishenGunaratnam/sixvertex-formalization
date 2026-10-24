import SixVertex.CountingSawtooth
import SixVertex.ConvolutionDerivative

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Full-line integration by parts with an actual bounded primitive.
All three products required by improper integration by parts are integrable. -/
theorem convolution_primitive_integration_by_parts (q q' P : BoundedRealFunction)
    (hq : Integrable (fun x => q x)) (hq' : Integrable (fun x => q' x))
    (p : ℝ → ℝ) (hp : Integrable p)
    (hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x)
    (hdP : ∀ x, HasDerivAt (fun y => P y) (p x) x) (u : ℝ) :
    (∫ v : ℝ, q (u-v)*p v)=(∫ v : ℝ, q' (u-v)*P v) := by
  have hqp : Integrable (fun v : ℝ => q (u-v)*p v) := by
    have h := hp.mul_bdd ((q.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Eventually.of_forall (fun v => q.norm_coe_le_norm (u-v)))
    change Integrable (fun v : ℝ => p v*q (u-v)) at h
    simpa only [mul_comm] using h
  have hqP : Integrable (fun v : ℝ => q (u-v)*P v) :=
    (hq.comp_sub_left u).mul_bdd P.continuous.aestronglyMeasurable
      (Eventually.of_forall P.norm_coe_le_norm)
  have hqpP : Integrable (fun v : ℝ => q' (u-v)*P v) :=
    (hq'.comp_sub_left u).mul_bdd P.continuous.aestronglyMeasurable
      (Eventually.of_forall P.norm_coe_le_norm)
  have h := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := fun v : ℝ => q (u-v)) (u' := fun v : ℝ => -q' (u-v))
    (v := fun v : ℝ => P v) (v' := p)
    (fun v _ => by
      simpa only [Function.comp_def,zero_sub,neg_mul,mul_neg_one] using!
        (hdq (u-v)).comp v ((hasDerivAt_const v u).sub (hasDerivAt_id v)))
    (fun v _ => hdP v) hqp (by
      convert hqpP.neg using 1
      funext v
      exact neg_mul _ _) hqP
  change (∫ v : ℝ, q (u-v)*p v)=-(∫ v : ℝ, (-q' (u-v))*P v) at h
  simp_rw [neg_mul] at h
  rw [integral_neg,neg_neg] at h
  exact h

/-- The derivative kernel integrated against one counting jump gives
its exact atomic convolution contribution. -/
theorem integral_derivative_kernel_Ici (q q' : BoundedRealFunction)
    (hq : Integrable (fun x => q x)) (hq' : Integrable (fun x => q' x))
    (hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x) (u y : ℝ) :
    (∫ v in Ici y, q' (u-v))=q (u-y) := by
  have hd : ∀ v, HasDerivAt (fun v : ℝ => q (u-v)) (-q' (u-v)) v := fun v => by
    simpa only [Function.comp_def,zero_sub,neg_mul,mul_neg_one] using!
      (hdq (u-v)).comp v ((hasDerivAt_const v u).sub (hasDerivAt_id v))
  have hi : Integrable (fun v : ℝ => q' (u-v)) := hq'.comp_sub_left u
  have ht : Tendsto (fun v : ℝ => q (u-v)) atTop (𝓝 0) :=
    tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi (a := y) (fun v _ => hd v)
      hi.neg.integrableOn (hq.comp_sub_left u).integrableOn
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := y) (fun v _ => hd v) hi.neg.integrableOn ht
  rw [integral_Ici_eq_integral_Ioi]
  change (∫ v in Ioi y, -q' (u-v))=0-q (u-y) at h
  rw [integral_neg,zero_sub] at h
  linarith

theorem rootCountLe_eq_sum_indicators {n : ℕ} (Y : Fin n → ℝ) (v : ℝ) :
    (rootCountLe Y v : ℝ)=∑ j : Fin n, (Ici (Y j)).indicator (fun _ : ℝ => (1 : ℝ)) v := by
  simp only [Set.indicator,Set.mem_Ici]
  simp only [rootCountLe,rootsAtMost,Finset.card_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

/-- The atomic part of integration by parts keeps every labelled root,
including coincidences; no unproved Stieltjes identity is used. -/
theorem integral_derivative_kernel_rootCount {n : ℕ} (Y : Fin n → ℝ) (q q' : BoundedRealFunction)
    (hq : Integrable (fun x => q x)) (hq' : Integrable (fun x => q' x))
    (hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x) (u : ℝ) :
    (∫ v : ℝ, q' (u-v)*(rootCountLe Y v : ℝ))=∑ j : Fin n, q (u-Y j) := by
  simp_rw [rootCountLe_eq_sum_indicators,Finset.mul_sum]
  rw [integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro j _
    simp_rw [← Set.indicator_mul_right (Ici (Y j)) (fun v : ℝ => q' (u-v)) (fun _ : ℝ => (1 : ℝ))]
    rw [integral_indicator measurableSet_Ici]
    simpa only [mul_one] using integral_derivative_kernel_Ici q q' hq hq' hdq u (Y j)
  · intro j _
    simp_rw [← Set.indicator_mul_right (Ici (Y j)) (fun v : ℝ => q' (u-v)) (fun _ : ℝ => (1 : ℝ))]
    apply ((hq'.comp_sub_left u).mul_const 1).indicator measurableSet_Ici

end
end SixVertex
