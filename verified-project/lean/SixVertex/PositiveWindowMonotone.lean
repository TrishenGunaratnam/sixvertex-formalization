import SixVertex.PositiveWindowComparison

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set

/-- Increasing the excluded window decreases the actual positive
exterior-convolution operator on nonnegative inputs. -/
theorem exteriorConvolutionOperator_antitone_Q (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (hpos : ∀ x,0 ≤ k x)
    (Q T : ℝ) (hQT : Q ≤ T) (f : BoundedRealFunction) (hf : ∀ x,0 ≤ f x) (u : ℝ) :
    exteriorConvolutionOperator k hk T f u ≤ exteriorConvolutionOperator k hk Q f u := by
  have hi : Integrable (fun v : ℝ => k (u-v)*f v) :=
    (hk.comp_sub_left u).mul_bdd f.continuous.aestronglyMeasurable
      (Eventually.of_forall f.norm_coe_le_norm)
  rw [exteriorConvolutionOperator_apply,exteriorConvolutionOperator_apply]
  apply setIntegral_mono_set hi.integrableOn
    (Eventually.of_forall (fun v => mul_nonneg (hpos (u-v)) (hf v)))
  filter_upwards with v hv
  intro hvQ
  exact hv ⟨by linarith [hvQ.1],by linarith [hvQ.2]⟩

/-- The actual positive-kernel finite-window density decreases pointwise
when the cutoff increases. This is the opposite pointwise direction from
negative K; filling-mass monotonicity is a separate conclusion. -/
theorem finiteIntervalDensity_antitone_Q_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q T : ℝ) (hQT : Q ≤ T) (u : ℝ) :
    finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) T u ≤
      finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  let R := physicalResolventKernel lam h0 hpi
  let hr := (physicalResolventKernel_decay lam h0 hpi).1
  let A := exteriorConvolutionOperator R hr T
  let r := fullLineDensityFunction lam h0 hpi
  let g := finiteIntervalDensity lam h0 hpi T
  let v := finiteIntervalDensity lam h0 hpi Q
  have hn : ‖A‖ < 1 := positive_exterior_resolvent_norm_lt_one lam h0 hh T
  have hp : ∀ f : BoundedRealFunction,(∀ x,0 ≤ f x) → ∀ x,0 ≤ A f x :=
    exteriorConvolutionOperator_nonnegative R hr (physicalResolventKernel_nonneg_positiveK lam h0 hh) T
  have he : g=r+A g := finiteIntervalDensity_exterior_equation lam h0 hpi T
  have hsuper : ∀ x,r x ≤ v x-A v x := by
    intro x
    have hv := congrArg (fun f : BoundedRealFunction => f x)
      (finiteIntervalDensity_exterior_equation lam h0 hpi Q)
    change v x=r x+exteriorConvolutionOperator R hr Q v x at hv
    have hm := exteriorConvolutionOperator_antitone_Q R hr
      (physicalResolventKernel_nonneg_positiveK lam h0 hh) Q T hQT v
      (fun y => (finiteIntervalDensity_pos_positiveK lam h0 hh Q y).le) x
    change A v x ≤ exteriorConvolutionOperator R hr Q v x at hm
    linarith
  exact positive_operator_fixed_point_le_supersolution A hn hp r g v he hsuper u

end
end SixVertex
