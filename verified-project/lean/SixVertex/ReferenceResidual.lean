import SixVertex.ReferenceQuadrature
import SixVertex.FiniteIntervalMeanfield
import SixVertex.ResolventDerivative

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Uniform continuum/discrete counting error for actual reference
quantiles, with an explicit chain- and cutoff-independent constant. -/
theorem reference_counting_uniform_error {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (u : ℝ) :
    |countingXi lam (fun _ => 0) L Y u-
      ((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)| ≤ |1-2*lam/Real.pi|/2 := by
  have he := referenceQuantile_kernel_error lam h0 hhalf hpi Q R.interval_nonneg L R.chain_pos Y R.ordered
    R.mass R.location R.level (physicalCountingPhaseFunction lam) (physicalKernelFunction lam h0 hpi)
    (physicalCountingPhaseFunction_hasDerivAt lam h0 hpi) (kernelK_integrable lam h0 hpi) u
  simp_rw [physicalCountingPhaseFunction_apply] at he
  change |(∑ j : Fin n, countingTheta lam (u-Y j))-
    (L : ℝ)*(∫ v in Icc (-Q) Q, countingTheta lam (u-v)*finiteIntervalDensity lam h0 hpi Q v)| ≤
      kernelL1Mass (kernelK lam)/2 at he
  rw [kernelL1Mass,integral_abs_kernelK lam h0 hpi] at he
  have hm := finiteIntervalMeanfield_eq_cumulative lam h0 hpi Q R.interval_nonneg u
  unfold finiteIntervalMeanfield at hm
  rw [finiteIntervalPhaseIntegral_apply] at hm
  have hmL := congrArg (fun x : ℝ => (L : ℝ)*x) hm
  have hxi : countingXi lam (fun _ => 0) L Y u=
      (L : ℝ)*countingS lam u-∑ j : Fin n, countingTheta lam (u-Y j) := by
    simp only [countingXi,sub_zero,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have halg : countingXi lam (fun _ => 0) L Y u-
      ((L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u-(n : ℝ)/2)=
      -((∑ j : Fin n, countingTheta lam (u-Y j))-
        (L : ℝ)*(∫ v in Icc (-Q) Q, countingTheta lam (u-v)*finiteIntervalDensity lam h0 hpi Q v)) := by
    rw [hxi]
    nlinarith only [hmL,R.mass]
  rw [halg,abs_neg]
  exact he

/-- The actual counting density at the reference configuration equals
L*r_Q+O(1), uniformly on the entire line. This does not yet transfer the
estimate to the perturbed on-shell roots. -/
theorem reference_density_uniform_error {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) (u : ℝ) :
    |countingSlope lam (fun _ => 0) L Y u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u| ≤
      kernelL1Mass (kernelKPrime lam)/2 := by
  have he := referenceQuantile_kernel_error lam h0 hhalf hpi Q R.interval_nonneg L R.chain_pos Y R.ordered
    R.mass R.location R.level (physicalKernelFunction lam h0 hpi) (physicalKernelPrimeFunction lam h0 hpi)
    (fun v => hasDerivAt_kernelK lam v h0 hpi) (kernelKPrime_integrable lam h0 hpi) u
  change |(∑ j : Fin n, kernelK lam (u-Y j))-
    (L : ℝ)*(∫ v in Icc (-Q) Q, kernelK lam (u-v)*finiteIntervalDensity lam h0 hpi Q v)| ≤
      kernelL1Mass (kernelKPrime lam)/2 at he
  have hm := congrArg (fun x : ℝ => (L : ℝ)*x) (finiteIntervalDensity_equation lam h0 hpi Q u)
  have hrho : countingSlope lam (fun _ => 0) L Y u=
      (L : ℝ)*kernelS lam u-∑ j : Fin n, kernelK lam (u-Y j) := by
    simp only [countingSlope,sub_zero,Finset.sum_const,Finset.card_range,nsmul_eq_mul]
  have halg : countingSlope lam (fun _ => 0) L Y u-(L : ℝ)*finiteIntervalDensity lam h0 hpi Q u=
      -((∑ j : Fin n, kernelK lam (u-Y j))-
        (L : ℝ)*(∫ v in Icc (-Q) Q, kernelK lam (u-v)*finiteIntervalDensity lam h0 hpi Q v)) := by
    rw [hrho]
    nlinarith only [hm]
  rw [halg,abs_neg]
  exact he

/-- The residual of the actual finite Bethe counting system in the sup
norm is uniformly bounded at the reference mid-quantiles. -/
theorem reference_bethe_residual_norm {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) :
    ‖countingSystem lam (fun _ => 0) L Y-countingTarget n 0‖ ≤ |1-2*lam/Real.pi|/2 := by
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ |1-2*lam/Real.pi|/2)).mpr
  intro j
  change |countingXi lam (fun _ => 0) L Y (Y j)-countingTarget n 0 j| ≤ _
  have ht : countingTarget n 0 j=(L : ℝ)*finiteIntervalCumulative lam h0 hpi Q (Y j)-(n : ℝ)/2 := by
    rw [R.level j]
    unfold countingTarget
    ring
  rw [ht]
  exact reference_counting_uniform_error lam h0 hhalf hpi Q L Y R (Y j)

/-- At the free-fermion point the constructed continuum mid-quantiles
solve the exact finite Bethe equations. This checks their normalization. -/
theorem referenceQuantiles_freeFermion_on_shell {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (hlam : lam=Real.pi/2) (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ)
    (R : ReferenceQuantileData lam h0 hpi Q L Y) :
    ConsecutiveRoots lam (fun _ => 0) L Y 0 := by
  subst lam
  have he := reference_bethe_residual_norm (Real.pi/2) h0 le_rfl hpi Q L Y R
  have hp : 2*(Real.pi/2)/Real.pi=(1 : ℝ) := by field_simp [Real.pi_ne_zero] <;> ring
  rw [hp,sub_self,abs_zero,zero_div] at he
  exact ⟨R.ordered,sub_eq_zero.mp (norm_le_zero_iff.mp he)⟩

end
end SixVertex
