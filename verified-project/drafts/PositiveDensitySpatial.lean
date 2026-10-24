import SixVertex.FullLineDensitySpatial
import SixVertex.PositiveWindowComparison
import SixVertex.FiniteIntervalRegularity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Set

/-- The actual positive resolvent inherits the exact full-line spatial
comparison through its proved convolution J*r. -/
theorem physicalResolventKernel_spatial_comparison_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (u v : ℝ) :
    Real.exp (-((Real.pi/lam)*|v-u|))*physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) u ≤
        physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) v ∧
      physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) v ≤
        Real.exp ((Real.pi/lam)*|v-u|)*physicalResolventKernel lam h0 (by linarith [Real.pi_pos]) u := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  let r := fullLineDensityFunction lam h0 hpi
  have hj := positiveDressingKernel_integrable lam h0 hh
  have hupper (x y : ℝ) : physicalResolventKernel lam h0 hpi y ≤
      Real.exp ((Real.pi/lam)*|y-x|)*physicalResolventKernel lam h0 hpi x := by
    simp only [physicalResolventKernel_eq_positiveCandidate lam h0 hh]
    change (∫ t : ℝ,positiveDressingKernel lam t*r (y-t)) ≤
      Real.exp ((Real.pi/lam)*|y-x|)*(∫ t : ℝ,positiveDressingKernel lam t*r (x-t))
    rw [← integral_const_mul]
    apply integral_mono (boundedConvolution_integrand_integrable _ hj r y)
      ((boundedConvolution_integrand_integrable _ hj r x).const_mul _)
    intro t
    have he := (fullLineDensityFunction_spatial_comparison_all lam h0 hpi (x-t) (y-t)).2
    rw [show (y-t)-(x-t)=y-x by ring] at he
    have hm := mul_le_mul_of_nonneg_left he (positiveDressingKernel_nonneg lam h0 hh t)
    exact hm.trans_eq (by ring)
  refine ⟨?_,hupper u v⟩
  have he := hupper v u
  rw [abs_sub_comm u v] at he
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-((Real.pi/lam)*|v-u|))).le
  rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul] at hm
  exact hm

/-- The actual positive-K finite-window density has a global spatial
comparison with a cutoff-independent constant. -/
theorem finiteIntervalDensity_spatial_comparison_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q u v : ℝ) :
    Real.exp (-((Real.pi/lam)*|v-u|))*finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u ≤
        finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q v ∧
      finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q v ≤
        Real.exp ((Real.pi/lam)*|v-u|)*finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  let f := finiteIntervalDensity lam h0 hpi Q
  let r := fullLineDensityFunction lam h0 hpi
  let R := physicalResolventKernel lam h0 hpi
  have hR : Integrable (fun t => R t) := (physicalResolventKernel_decay lam h0 hpi).1
  have heq (x : ℝ) : f x=r x+(∫ t in (Icc (-Q) Q)ᶜ,R (x-t)*f t) := by
    have he := congrArg (fun g : BoundedRealFunction => g x)
      (finiteIntervalDensity_exterior_equation lam h0 hpi Q)
    change f x=r x+exteriorConvolutionOperator R hR Q f x at he
    rw [exteriorConvolutionOperator_apply] at he
    exact he
  have hi (x : ℝ) : Integrable (fun t : ℝ => R (x-t)*f t) :=
    (hR.comp_sub_left x).mul_bdd f.continuous.aestronglyMeasurable
      (Eventually.of_forall f.norm_coe_le_norm)
  have hupper (x y : ℝ) : f y ≤ Real.exp ((Real.pi/lam)*|y-x|)*f x := by
    have hs := (fullLineDensityFunction_spatial_comparison_all lam h0 hpi x y).2
    have hc : (∫ t in (Icc (-Q) Q)ᶜ,R (y-t)*f t) ≤
        Real.exp ((Real.pi/lam)*|y-x|)*(∫ t in (Icc (-Q) Q)ᶜ,R (x-t)*f t) := by
      rw [← integral_const_mul]
      apply integral_mono (hi y).integrableOn ((hi x).const_mul _).integrableOn
      intro t
      have hr := (physicalResolventKernel_spatial_comparison_positiveK lam h0 hh (x-t) (y-t)).2
      rw [show (y-t)-(x-t)=y-x by ring] at hr
      have hm := mul_le_mul_of_nonneg_right hr (finiteIntervalDensity_pos_positiveK lam h0 hh Q t).le
      exact hm.trans_eq (by ring)
    rw [heq y,heq x,mul_add]
    exact add_le_add hs hc
  refine ⟨?_,hupper u v⟩
  have he := hupper v u
  rw [abs_sub_comm u v] at he
  have hm := mul_le_mul_of_nonneg_left he (Real.exp_pos (-((Real.pi/lam)*|v-u|))).le
  rw [← mul_assoc,← Real.exp_add,neg_add_cancel,Real.exp_zero,one_mul] at hm
  exact hm

/-- Global logarithmic variation of the actual positive-K window
solution, uniform over every cutoff. -/
theorem finiteIntervalDensity_log_lipschitz_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q u v : ℝ) :
    |Real.log (finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q v)-
      Real.log (finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u)| ≤
      (Real.pi/lam)*|v-u| := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have hu := finiteIntervalDensity_pos_positiveK lam h0 hh Q u
  have hv := finiteIntervalDensity_pos_positiveK lam h0 hh Q v
  have hc := finiteIntervalDensity_spatial_comparison_positiveK lam h0 hh Q u v
  have hlo := Real.log_le_log (mul_pos (Real.exp_pos _) hu) hc.1
  have hhi := Real.log_le_log hv hc.2
  rw [Real.log_mul (Real.exp_pos _).ne' hu.ne',Real.log_exp] at hlo hhi
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The actual derivative from differentiating the finite-window
equation satisfies the relative bound needed for quantile stability. -/
theorem finiteIntervalDensityPrime_relative_bound_positiveK (lam : ℝ) (h0 : 0 < lam)
    (hh : lam < Real.pi/2) (Q u : ℝ) :
    |finiteIntervalDensityPrimeFunction lam h0 (by linarith [Real.pi_pos]) Q u| ≤
      (Real.pi/lam)*finiteIntervalDensity lam h0 (by linarith [Real.pi_pos]) Q u := by
  have hpi : lam < Real.pi := by linarith [Real.pi_pos]
  have hC : 0 ≤ Real.pi/lam := (div_pos Real.pi_pos h0).le
  have hl : LipschitzWith ⟨Real.pi/lam,hC⟩
      (fun v => Real.log (finiteIntervalDensity lam h0 hpi Q v)) := by
    apply LipschitzWith.of_dist_le_mul
    intro x y
    change |Real.log (finiteIntervalDensity lam h0 hpi Q x)-Real.log (finiteIntervalDensity lam h0 hpi Q y)| ≤
      (Real.pi/lam)*|x-y|
    exact finiteIntervalDensity_log_lipschitz_positiveK lam h0 hh Q y x
  have hp := finiteIntervalDensity_pos_positiveK lam h0 hh Q u
  have hd := (finiteIntervalDensity_hasDerivAt lam h0 hpi Q u).log hp.ne'
  have hb := hd.le_of_lipschitz hl
  change ‖finiteIntervalDensityPrimeFunction lam h0 hpi Q u/finiteIntervalDensity lam h0 hpi Q u‖ ≤ Real.pi/lam at hb
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hp] at hb
  exact (div_le_iff₀ hp).mp hb

end
end SixVertex
