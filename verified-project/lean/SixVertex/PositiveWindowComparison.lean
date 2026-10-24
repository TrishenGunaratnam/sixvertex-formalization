import SixVertex.PositiveWindowEquation
import SixVertex.PositiveResolventFactorization
import SixVertex.PositiveOperatorComparison
import SixVertex.ExteriorComparison
import SixVertex.ExplicitDensityRadial

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set

/-- The actual positive exterior operator is a strict contraction,
uniformly over every finite cutoff. -/
theorem positive_exterior_resolvent_norm_lt_one (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q : ℝ) :
    ‖exteriorConvolutionOperator (physicalResolventKernel lam h0 (by linarith [Real.pi_pos]))
      (physicalResolventKernel_decay lam h0 (by linarith [Real.pi_pos])).1 Q‖ < 1 :=
  (exteriorConvolutionOperator_norm_bound _ _ Q).trans_lt
    ((physicalResolventKernel_L1_mass_lt_half_positiveK lam h0 hh).trans (by norm_num))

/-- The actual finite-window density is bounded below by the actual
full-line density in the positive-kernel range, on the entire line. -/
theorem finiteIntervalDensity_ge_fullLine_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q u : ℝ) :
    fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) u ≤
      finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  let A := exteriorConvolutionOperator (physicalResolventKernel lam h0 hpi)
    (physicalResolventKernel_decay lam h0 hpi).1 Q
  let r := fullLineDensityFunction lam h0 hpi
  let g := finiteIntervalDensity lam h0 hpi Q
  have hn : ‖A‖ < 1 := positive_exterior_resolvent_norm_lt_one lam h0 hh Q
  have hp : ∀ f : BoundedRealFunction,(∀ x,0 ≤ f x) → ∀ x,0 ≤ A f x :=
    exteriorConvolutionOperator_nonnegative _ _ (physicalResolventKernel_nonneg_positiveK lam h0 hh) Q
  have he : g=r+A g := finiteIntervalDensity_exterior_equation lam h0 hpi Q
  have hg : ∀ v,0 ≤ g v := positive_operator_fixed_point_nonnegative A hn hp r g
    (fun v => (fullLineDensityFunction_pos_all lam h0 hpi v).le) he
  have hx := congrArg (fun f : BoundedRealFunction => f u) he
  change g u=r u+A g u at hx
  have hAu := hp g hg u
  change r u ≤ g u
  linarith

/-- Positivity of the actual finite-window density throughout the
positive-kernel regime. -/
theorem finiteIntervalDensity_pos_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q u : ℝ) :
    0 < finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u :=
  (fullLineDensityFunction_pos_all lam h0 (by linarith [Real.pi_pos]) u).trans_le
    (finiteIntervalDensity_ge_fullLine_positiveK lam h0 hh Q u)

/-- Both actual H_Q bounds in the positive-kernel regime, with constants
independent of the cutoff. -/
theorem finiteIntervalOne_bounds_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q u : ℝ) :
    1/(1+kernelL1Mass (kernelK lam)) ≤ finiteIntervalOne lam h0 (by linarith [Real.pi_pos]) Q u ∧
      finiteIntervalOne lam h0 (by linarith [Real.pi_pos]) Q u ≤ 1 := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  let A := exteriorConvolutionOperator (physicalResolventKernel lam h0 hpi)
    (physicalResolventKernel_decay lam h0 hpi).1 Q
  let c : BoundedRealFunction := BoundedContinuousFunction.const ℝ (1/(2*(1-lam/Real.pi)))
  let g := finiteIntervalOne lam h0 hpi Q
  have hn : ‖A‖ < 1 := positive_exterior_resolvent_norm_lt_one lam h0 hh Q
  have hp : ∀ f : BoundedRealFunction,(∀ x,0 ≤ f x) → ∀ x,0 ≤ A f x :=
    exteriorConvolutionOperator_nonnegative _ _ (physicalResolventKernel_nonneg_positiveK lam h0 hh) Q
  have he : g=c+A g := finiteIntervalOne_exterior_equation lam h0 hpi Q
  have hc : ∀ v,0 ≤ c v := by
    intro v
    change 0 ≤ 1/(2*(1-lam/Real.pi))
    have hd := (div_lt_one Real.pi_pos).mpr hpi
    positivity
  have hg : ∀ v,0 ≤ g v := positive_operator_fixed_point_nonnegative A hn hp c g hc he
  have hk : kernelL1Mass (kernelK lam)=1-2*lam/Real.pi := by
    apply (integral_congr_ae (Eventually.of_forall (fun v => abs_of_nonneg (kernelK_nonneg lam v h0 hh.le)))).trans
    exact integral_kernelK lam h0 hpi
  have hd : 1+kernelL1Mass (kernelK lam)=2*(1-lam/Real.pi) := by rw [hk]; ring
  constructor
  · rw [hd]
    have hx := congrArg (fun f : BoundedRealFunction => f u) he
    change g u=1/(2*(1-lam/Real.pi))+A g u at hx
    have hAu := hp g hg u
    change 1/(2*(1-lam/Real.pi)) ≤ g u
    linarith
  · have hi : 0 ≤ ∫ v in Icc (-Q) Q,kernelK lam (u-v)*g v :=
      integral_nonneg (fun v => mul_nonneg (kernelK_nonneg lam (u-v) h0 hh.le) (hg v))
    have hx := finiteIntervalOne_equation lam h0 hpi Q u
    change g u+(∫ v in Icc (-Q) Q,kernelK lam (u-v)*g v)=1 at hx
    change g u ≤ 1
    linarith

/-- The global additive comparison follows from an actual positive
supersolution; only the exterior values of the source are bounded. -/
theorem finiteIntervalDensity_upper_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q : ℝ) (hQ : 0 ≤ Q) (u : ℝ) :
    finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u ≤
      fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) u+
      (kernelL1Mass (fun v => physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) v)/
        (1-kernelL1Mass (fun v => physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) v)))*
        fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) Q := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  let R := physicalResolventKernel lam h0 hpi
  let hr := (physicalResolventKernel_decay lam h0 hpi).1
  let tau : ℝ := kernelL1Mass (fun v => R v)
  let a : ℝ := tau/(1-tau)
  let A := exteriorConvolutionOperator R hr Q
  let r := fullLineDensityFunction lam h0 hpi
  let g := finiteIntervalDensity lam h0 hpi Q
  let v : BoundedRealFunction := r+BoundedContinuousFunction.const ℝ (a*r Q)
  have ht0 : 0 ≤ tau := kernelL1Mass_nonneg _
  have ht1 : tau < 1 := (physicalResolventKernel_L1_mass_lt_half_positiveK lam h0 hh).trans (by norm_num)
  have ha : 0 ≤ a := div_nonneg ht0 (sub_pos.mpr ht1).le
  have hq : 0 ≤ r Q := (fullLineDensityFunction_pos_all lam h0 hpi Q).le
  have hn : ‖A‖ < 1 := positive_exterior_resolvent_norm_lt_one lam h0 hh Q
  have hp : ∀ f : BoundedRealFunction,(∀ x,0 ≤ f x) → ∀ x,0 ≤ A f x :=
    exteriorConvolutionOperator_nonnegative R hr (physicalResolventKernel_nonneg_positiveK lam h0 hh) Q
  have he : g=r+A g := finiteIntervalDensity_exterior_equation lam h0 hpi Q
  have hmass : (∫ t : ℝ,R t)=tau := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun t => (abs_of_nonneg (physicalResolventKernel_nonneg_positiveK lam h0 hh t)).symm)
  have hsuper : ∀ x,r x ≤ v x-A v x := by
    intro x
    have hv : ∀ y,y ∉ Icc (-Q) Q → v y ≤ r Q+a*r Q := by
      intro y hy
      have hd : Q ≤ |y| := by
        by_contra h
        exact hy (abs_le.mp (le_of_lt (lt_of_not_ge h)))
      have hb := fullLineDensityFunction_radiallyAntitone_all lam h0 hpi Q y
        (by simpa only [abs_of_nonneg hQ] using hd)
      change r y+a*r Q ≤ r Q+a*r Q
      exact add_le_add hb le_rfl
    have hAx := exteriorConvolutionOperator_le_exterior_bound R hr
      (physicalResolventKernel_nonneg_positiveK lam h0 hh) Q v (r Q+a*r Q)
      (by positivity) hv x
    rw [hmass] at hAx
    have halg : tau*(r Q+a*r Q)=a*r Q := by
      dsimp [a]
      field_simp [(sub_pos.mpr ht1).ne']
      <;> ring
    rw [halg] at hAx
    change r x ≤ r x+a*r Q-A v x
    change A v x ≤ a*r Q at hAx
    linarith
  have hb := positive_operator_fixed_point_le_supersolution A hn hp r g v he hsuper u
  exact hb

/-- The paper's uniform relative density comparison in the positive-K
regime, including the endpoints of the finite window. -/
theorem finiteIntervalDensity_comparison_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q : ℝ) (hQ : 0 ≤ Q) (u : ℝ) (hu : |u| ≤ Q) :
    fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) u ≤
        finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u ∧
      finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u ≤
        fullLineDensityFunction lam h0 (by linarith [Real.pi_pos]) u/
        (1-kernelL1Mass (fun v => physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) v)) := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  let tau := kernelL1Mass (fun v => physicalResolventKernel lam h0 hpi v)
  have ht0 : 0 ≤ tau := kernelL1Mass_nonneg _
  have ht1 : tau < 1 := (physicalResolventKernel_L1_mass_lt_half_positiveK lam h0 hh).trans (by norm_num)
  have ha : 0 ≤ tau/(1-tau) := div_nonneg ht0 (sub_pos.mpr ht1).le
  have hb := fullLineDensityFunction_radiallyAntitone_all lam h0 hpi u Q
    (by simpa only [abs_of_nonneg hQ] using hu)
  refine ⟨finiteIntervalDensity_ge_fullLine_positiveK lam h0 hh Q u,?_⟩
  calc
    _ ≤ fullLineDensityFunction lam h0 hpi u+(tau/(1-tau))*fullLineDensityFunction lam h0 hpi Q :=
      finiteIntervalDensity_upper_positiveK lam h0 hh Q hQ u
    _ ≤ fullLineDensityFunction lam h0 hpi u+(tau/(1-tau))*fullLineDensityFunction lam h0 hpi u :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hb ha)
    _ = _ := by
      change fullLineDensityFunction lam h0 hpi u+(tau/(1-tau))*fullLineDensityFunction lam h0 hpi u=
        fullLineDensityFunction lam h0 hpi u/(1-tau)
      field_simp [(sub_pos.mpr ht1).ne']
      <;> ring

end
end SixVertex
