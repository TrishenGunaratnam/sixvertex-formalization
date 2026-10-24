import SixVertex.ReferenceQuantiles

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def reflectBoundedFunction (f : BoundedRealFunction) : BoundedRealFunction :=
  f.compContinuous ⟨fun u : ℝ => -u,continuous_neg⟩

theorem symmetric_Icc_integral_neg (g : ℝ → ℝ) (Q : ℝ) (hQ : 0 ≤ Q) :
    (∫ v in Icc (-Q) Q, g (-v))=∫ v in Icc (-Q) Q, g v := by
  have hab : -Q ≤ Q := by linarith
  calc
    _ = ∫ v in -Q..Q, g (-v) := by rw [intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc]
    _ = ∫ v in -Q..Q, g v := by
      simpa only [neg_neg] using intervalIntegral.integral_comp_neg g (a := -Q) (b := Q)
    _ = _ := by rw [intervalIntegral.integral_of_le hab,integral_Icc_eq_integral_Ioc]

theorem physicalWindowOperator_reflect (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (hQ : 0 ≤ Q) (f : BoundedRealFunction) :
    physicalWindowOperator lam h0 hpi Q (reflectBoundedFunction f)=
      reflectBoundedFunction (physicalWindowOperator lam h0 hpi Q f) := by
  ext u
  change physicalWindowOperator lam h0 hpi Q (reflectBoundedFunction f) u=
    physicalWindowOperator lam h0 hpi Q f (-u)
  rw [physicalWindowOperator_apply,physicalWindowOperator_apply]
  change (∫ v in Icc (-Q) Q, kernelK lam (u-v)*f (-v))=
    ∫ v in Icc (-Q) Q, kernelK lam (-u-v)*f v
  calc
    _ = ∫ v in Icc (-Q) Q, kernelK lam (-u-(-v))*f (-v) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun v => by
        change kernelK lam (u-v)*f (-v)=kernelK lam (-u-(-v))*f (-v)
        rw [show -u-(-v)= -(u-v) by ring,kernelK_neg])
    _ = _ := symmetric_Icc_integral_neg (fun v => kernelK lam (-u-v)*f v) Q hQ

/-- Symmetry follows from the actual kernel equation and uniqueness,
without substituting an explicit hyperbolic density formula. -/
theorem finiteIntervalDensity_neg (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (hQ : 0 ≤ Q) (u : ℝ) :
    finiteIntervalDensity lam h0 hpi Q (-u)=finiteIntervalDensity lam h0 hpi Q u := by
  have heven (x : ℝ) : physicalSourceFunction lam h0 hpi (-x)=physicalSourceFunction lam h0 hpi x := by
    exact kernelK_neg (lam/2) x
  have hs : reflectBoundedFunction (finiteIntervalDensity lam h0 hpi Q)+
      physicalWindowOperator lam h0 hpi Q (reflectBoundedFunction (finiteIntervalDensity lam h0 hpi Q))=
      physicalSourceFunction lam h0 hpi := by
    rw [physicalWindowOperator_reflect lam h0 hpi Q hQ]
    ext x
    have h := congrArg (fun f : BoundedRealFunction => f (-x))
      (physicalWindowInverse_solves lam h0 hpi Q (physicalSourceFunction lam h0 hpi))
    change finiteIntervalDensity lam h0 hpi Q (-x)+
      physicalWindowOperator lam h0 hpi Q (finiteIntervalDensity lam h0 hpi Q) (-x)=physicalSourceFunction lam h0 hpi x
    rwa [heven x] at h
  have hu := congrArg (fun f : BoundedRealFunction => f u)
    (physicalWindowInverse_solution_unique lam h0 hpi Q (physicalSourceFunction lam h0 hpi)
      (reflectBoundedFunction (finiteIntervalDensity lam h0 hpi Q)) hs)
  exact hu.symm

theorem finiteIntervalCumulative_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (hQ : 0 ≤ Q) :
    finiteIntervalCumulative lam h0 hpi Q 0=finiteIntervalMass lam h0 hpi Q/2 := by
  let r := finiteIntervalDensity lam h0 hpi Q
  have he : (∫ v in -Q..0, r v)=(∫ v in 0..Q, r v) := by
    have h := intervalIntegral.integral_comp_neg (fun v => r v) (a := -Q) (b := 0)
    simp only [neg_zero,neg_neg] at h
    have hev : (fun v : ℝ => r (-v))=(fun v => r v) := funext (finiteIntervalDensity_neg lam h0 hpi Q hQ)
    rwa [hev] at h
  have hs := intervalIntegral.integral_add_adjacent_intervals
    (r.continuous.intervalIntegrable (μ := volume) (-Q) 0)
    (r.continuous.intervalIntegrable (μ := volume) 0 Q)
  have hr : (∫ v in -Q..Q, r v)=finiteIntervalMass lam h0 hpi Q :=
    finiteIntervalCumulative_right lam h0 hpi Q hQ
  change (∫ v in -Q..0, r v)=finiteIntervalMass lam h0 hpi Q/2
  linarith

end
end SixVertex
