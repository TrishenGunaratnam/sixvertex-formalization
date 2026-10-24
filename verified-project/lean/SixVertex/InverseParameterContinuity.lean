import SixVertex.WindowParameterContinuity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- The actual finite-window resolvent identity, applied to a source. -/
theorem windowConvolutionInverse_source_difference (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (hm : kernelL1Mass (fun x => k x)<1)
    (f : BoundedRealFunction) (Q T : ℝ) :
    windowConvolutionInverse k hk Q f-windowConvolutionInverse k hk T f=
      windowConvolutionInverse k hk Q
        ((windowConvolutionOperator k hk T-windowConvolutionOperator k hk Q)
          (windowConvolutionInverse k hk T f)) := by
  let q := windowConvolutionInverse k hk Q f
  let t := windowConvolutionInverse k hk T f
  have hq := windowConvolutionInverse_solves k hk hm Q f
  have ht := windowConvolutionInverse_solves k hk hm T f
  have hs : (q-t)+windowConvolutionOperator k hk Q (q-t)=
      (windowConvolutionOperator k hk T-windowConvolutionOperator k hk Q) t := by
    rw [map_sub]
    ext u
    have hqu := congrArg (fun g : BoundedRealFunction => g u) hq
    have htu := congrArg (fun g : BoundedRealFunction => g u) ht
    change (q u-t u)+(windowConvolutionOperator k hk Q q u-windowConvolutionOperator k hk Q t u)=
      windowConvolutionOperator k hk T t u-windowConvolutionOperator k hk Q t u
    change q u+windowConvolutionOperator k hk Q q u=f u at hqu
    change t u+windowConvolutionOperator k hk T t u=f u at htu
    linarith
  have hi := congrArg (fun B : BoundedRealFunction →L[ℝ] BoundedRealFunction => B (q-t))
    (windowConvolutionInverse_left k hk hm Q)
  change windowConvolutionInverse k hk Q ((q-t)+windowConvolutionOperator k hk Q (q-t))=q-t at hi
  rw [hs] at hi
  exact hi.symm

/-- A uniform Lipschitz bound for the inverse applied to a fixed source,
with no parameter derivative or limiting equation supplied as an input. -/
theorem windowConvolutionInverse_source_lipschitz_Q (k : BoundedRealFunction)
    (hk : Integrable (fun x => k x)) (hm : kernelL1Mass (fun x => k x)<1)
    (f : BoundedRealFunction) (Q T : ℝ) (hQ : 0 ≤ Q) (hT : 0 ≤ T) :
    ‖windowConvolutionInverse k hk Q f-windowConvolutionInverse k hk T f‖ ≤
      (2*((1-kernelL1Mass (fun x => k x))⁻¹)^2*‖k‖*‖f‖)*|Q-T| := by
  let c : ℝ := (1-kernelL1Mass (fun x => k x))⁻¹
  have hc : 0 ≤ c := (inv_pos.mpr (sub_pos.mpr hm)).le
  have hq : ‖windowConvolutionInverse k hk Q‖ ≤ c := windowConvolutionInverse_norm_bound k hk hm Q
  have ht : ‖windowConvolutionInverse k hk T f‖ ≤ c*‖f‖ :=
    (ContinuousLinearMap.le_opNorm _ f).trans
      (mul_le_mul_of_nonneg_right (windowConvolutionInverse_norm_bound k hk hm T) (norm_nonneg _))
  have hA : ‖windowConvolutionOperator k hk T-windowConvolutionOperator k hk Q‖ ≤ 2*‖k‖*|Q-T| := by
    simpa only [abs_sub_comm T Q] using windowConvolutionOperator_lipschitz_Q k hk T Q hT hQ
  let v := (windowConvolutionOperator k hk T-windowConvolutionOperator k hk Q)
    (windowConvolutionInverse k hk T f)
  have hv : ‖v‖ ≤ (2*‖k‖*|Q-T|)*(c*‖f‖) :=
    (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul hA ht (norm_nonneg _) (by positivity))
  rw [windowConvolutionInverse_source_difference k hk hm f Q T]
  change ‖windowConvolutionInverse k hk Q v‖ ≤ _
  calc
    _ ≤ c*‖v‖ := (ContinuousLinearMap.le_opNorm _ _).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg _))
    _ ≤ c*((2*‖k‖*|Q-T|)*(c*‖f‖)) := mul_le_mul_of_nonneg_left hv hc
    _ = _ := by dsimp [c]; ring

/-- One endpoint Lipschitz constant for the actual r_Q, for every Q>=0. -/
theorem exists_finiteIntervalDensity_lipschitz_Q (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (Q T : ℝ), 0 ≤ Q → 0 ≤ T →
      ‖finiteIntervalDensity lam h0 hpi Q-finiteIntervalDensity lam h0 hpi T‖ ≤ D*|Q-T| := by
  let k := physicalKernelFunction lam h0 hpi
  let f := physicalSourceFunction lam h0 hpi
  let D : ℝ := 2*((1-kernelL1Mass (fun x => k x))⁻¹)^2*‖k‖*‖f‖
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro Q T hQ hT
  exact windowConvolutionInverse_source_lipschitz_Q k (kernelK_integrable lam h0 hpi)
    (kernelK_L1_mass_lt_one lam h0 hpi) f Q T hQ hT

end
end SixVertex
