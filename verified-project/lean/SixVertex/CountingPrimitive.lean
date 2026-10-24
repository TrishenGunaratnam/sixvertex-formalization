import SixVertex.CountingDensity
import SixVertex.ConvolutionLimits

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem barePhase_abs_bound (theta u : ℝ) : |barePhase theta u| ≤ 1/2 := by
  unfold barePhase
  rw [abs_div,abs_of_pos Real.pi_pos]
  apply (div_le_iff₀ Real.pi_pos).mpr
  apply abs_le.mpr
  constructor
  · linarith [Real.neg_pi_div_two_lt_arctan ((Real.cos theta/Real.sin theta)*(Real.sinh u/Real.cosh u))]
  · linarith [Real.arctan_lt_pi_div_two ((Real.cos theta/Real.sin theta)*(Real.sinh u/Real.cosh u))]

def phasePrimitiveFunction (theta : ℝ) : BoundedRealFunction :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun u => barePhase theta u+phaseEnd theta)
    ((contDiff_barePhase theta).continuous.add continuous_const) (1/2+|phaseEnd theta|) (fun u =>
      (abs_add_le (barePhase theta u) (phaseEnd theta)).trans (add_le_add (barePhase_abs_bound theta u) le_rfl))

def sourcePrimitiveFunction (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) : BoundedRealFunction :=
  ∑ a ∈ Finset.range L, translateBoundedFunction (phasePrimitiveFunction (lam/2)) (b a)

def atomicPrimitiveFunction {n : ℕ} (lam : ℝ) (Y : Fin n → ℝ) : BoundedRealFunction :=
  ∑ j : Fin n, translateBoundedFunction (phasePrimitiveFunction lam) (Y j)

theorem sourcePrimitiveFunction_apply (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (u : ℝ) :
    sourcePrimitiveFunction lam b L u=∑ a ∈ Finset.range L, (countingS lam (u-b a)+phaseEnd (lam/2)) := by
  unfold sourcePrimitiveFunction
  rw [BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

theorem atomicPrimitiveFunction_apply {n : ℕ} (lam : ℝ) (Y : Fin n → ℝ) (u : ℝ) :
    atomicPrimitiveFunction lam Y u=∑ j : Fin n, (countingTheta lam (u-Y j)+phaseEnd lam) := by
  unfold atomicPrimitiveFunction
  rw [BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  rfl

theorem sourcePrimitiveFunction_hasDerivAt (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (u : ℝ) :
    HasDerivAt (fun v => sourcePrimitiveFunction lam b L v) (bareDensityFunction lam h0 hpi b L u) u := by
  simp_rw [sourcePrimitiveFunction_apply]
  rw [bareDensityFunction_apply]
  apply HasDerivAt.fun_sum
  intro a _
  simpa only [Function.comp_def,id_eq,mul_one] using
    ((hasDerivAt_countingS lam (u-b a) h0 hpi).comp u ((hasDerivAt_id u).sub_const (b a))).add_const
      (phaseEnd (lam/2))

theorem phasePrimitiveFunction_tendsto_atBot (theta : ℝ) (h0 : 0 < theta) (hpi : theta < Real.pi) :
    Tendsto (fun u => phasePrimitiveFunction theta u) atBot (𝓝 0) := by
  have h := (barePhase_tendsto_atBot atBot (fun _ : ℝ => theta) id theta h0 hpi tendsto_const_nhds tendsto_id).add_const (phaseEnd theta)
  change Tendsto (fun u => barePhase theta u+phaseEnd theta) atBot (𝓝 0)
  simpa only [id_eq,neg_add_cancel] using h

theorem sourcePrimitiveFunction_tendsto_atBot (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) : Tendsto (fun u => sourcePrimitiveFunction lam b L u) atBot (𝓝 0) := by
  have h := tendsto_finsetSum (Finset.range L) (fun a _ =>
    (phasePrimitiveFunction_tendsto_atBot (lam/2) (by linarith) (by linarith [Real.pi_pos])).comp
      (real_shift_tendsto_atBot (b a)))
  have hs : Tendsto (fun u => ∑ a ∈ Finset.range L, phasePrimitiveFunction (lam/2) (u-b a)) atBot (𝓝 0) := by
    simpa only [Function.comp_def,Finset.sum_const_zero] using h
  apply hs.congr
  intro u
  rw [sourcePrimitiveFunction_apply]
  apply Finset.sum_congr rfl
  intro a _
  rfl

theorem bareDensityFunction_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) : Integrable (fun u => bareDensityFunction lam h0 hpi b L u) := by
  simp_rw [bareDensityFunction_apply]
  apply integrable_finsetSum
  intro a _
  exact (kernelS_integrable lam h0 hpi).comp_sub_right (b a)

theorem dressedBareDensityFunction_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) : Integrable (fun u => dressedBareDensityFunction lam h0 hpi b L u) :=
  physicalInverse_preserves_integrable lam h0 hpi _ (bareDensityFunction_integrable lam h0 hpi b L)

def dressedSourcePrimitiveFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) : BoundedRealFunction :=
  sourcePrimitiveFunction lam b L-
    boundedConvolution (fun x => physicalResolventKernel lam h0 hpi x)
      (physicalResolventKernel_decay lam h0 hpi).1 (sourcePrimitiveFunction lam b L)

theorem dressedSourcePrimitiveFunction_eq_inverse (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) :
    dressedSourcePrimitiveFunction lam h0 hpi b L=
      boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi) (sourcePrimitiveFunction lam b L) :=
  (physicalInverse_resolvent_representation lam h0 hpi _).symm

theorem dressedSourcePrimitiveFunction_hasDerivAt (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (u : ℝ) :
    HasDerivAt (fun v => dressedSourcePrimitiveFunction lam h0 hpi b L v)
      (dressedBareDensityFunction lam h0 hpi b L u) u := by
  have h := (sourcePrimitiveFunction_hasDerivAt lam h0 hpi b L u).sub
    (boundedConvolutionValue_hasDerivAt (fun x => physicalResolventKernel lam h0 hpi x)
      (physicalResolventKernel_decay lam h0 hpi).1 (sourcePrimitiveFunction lam b L)
      (bareDensityFunction lam h0 hpi b L) (sourcePrimitiveFunction_hasDerivAt lam h0 hpi b L) u)
  have he := congrArg (fun f : BoundedRealFunction => f u)
    (physicalInverse_resolvent_representation lam h0 hpi (bareDensityFunction lam h0 hpi b L))
  convert h using 1 <;> first | rfl | exact he

theorem dressedSourcePrimitiveFunction_tendsto_atBot (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) :
    Tendsto (fun u => dressedSourcePrimitiveFunction lam h0 hpi b L u) atBot (𝓝 0) := by
  have hs := sourcePrimitiveFunction_tendsto_atBot lam h0 hpi b L
  have ht := boundedConvolution_tendsto_atBot (fun x => physicalResolventKernel lam h0 hpi x)
    (physicalResolventKernel_decay lam h0 hpi).1 (sourcePrimitiveFunction lam b L) 0 hs
  have h := hs.sub ht
  change Tendsto (fun u => sourcePrimitiveFunction lam b L u-
    boundedConvolutionValue (fun x => physicalResolventKernel lam h0 hpi x) (sourcePrimitiveFunction lam b L) u) atBot (𝓝 0)
  simpa only [mul_zero,sub_zero] using h

/-- The dressed primitive is the ordinary cumulative density integral,
not merely a separately assigned antiderivative. -/
theorem integral_Iic_dressedBareDensityFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (u : ℝ) :
    (∫ v in Iic u, dressedBareDensityFunction lam h0 hpi b L v)=dressedSourcePrimitiveFunction lam h0 hpi b L u := by
  have h := integral_Iic_of_hasDerivAt_of_tendsto' (a := u)
    (fun v _ => dressedSourcePrimitiveFunction_hasDerivAt lam h0 hpi b L v)
    (dressedBareDensityFunction_integrable lam h0 hpi b L).integrableOn
    (dressedSourcePrimitiveFunction_tendsto_atBot lam h0 hpi b L)
  simpa only [sub_zero] using h

end
end SixVertex
