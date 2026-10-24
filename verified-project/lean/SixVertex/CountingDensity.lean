import SixVertex.CountingDiscrepancyKernel
import SixVertex.DensityRegularity
import SixVertex.ResolventDerivative

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def translateBoundedFunction (q : BoundedRealFunction) (c : ℝ) : BoundedRealFunction :=
  q.compContinuous ⟨fun u : ℝ => u-c,by fun_prop⟩

def bareDensityFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (b : ℕ → ℝ) (L : ℕ) : BoundedRealFunction :=
  ∑ a ∈ Finset.range L, translateBoundedFunction
    (physicalKernelFunction (lam/2) (by linarith) (by linarith [Real.pi_pos])) (b a)

def atomicKernelFunction {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Y : Fin n → ℝ) : BoundedRealFunction :=
  ∑ j : Fin n, translateBoundedFunction (physicalKernelFunction lam h0 hpi) (Y j)

def finiteCountingFunction {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) : BoundedRealFunction :=
  bareDensityFunction lam h0 hpi b L-atomicKernelFunction lam h0 hpi Y

theorem bareDensityFunction_apply (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (b : ℕ → ℝ) (L : ℕ) (u : ℝ) :
    bareDensityFunction lam h0 hpi b L u=∑ a ∈ Finset.range L, kernelS lam (u-b a) := by
  unfold bareDensityFunction
  rw [BoundedContinuousFunction.sum_apply]
  apply Finset.sum_congr rfl
  intro a _
  exact (kernelS_eq_phaseDensity lam (u-b a)).symm

theorem atomicKernelFunction_apply {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Y : Fin n → ℝ) (u : ℝ) :
    atomicKernelFunction lam h0 hpi Y u=∑ j : Fin n, kernelK lam (u-Y j) := by
  unfold atomicKernelFunction
  rw [BoundedContinuousFunction.sum_apply]
  rfl

theorem finiteCountingFunction_apply {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (u : ℝ) :
    finiteCountingFunction lam h0 hpi b L Y u=countingSlope lam b L Y u := by
  change bareDensityFunction lam h0 hpi b L u-atomicKernelFunction lam h0 hpi Y u=_
  rw [bareDensityFunction_apply,atomicKernelFunction_apply]
  rfl

/-- The dressed bare density is the actual full-line inverse of the
finite bare-source sum. Its definition follows the manuscript's primary
operator definition r=(I+K*)^{-1}s. -/
def dressedBareDensityFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) : BoundedRealFunction :=
  boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi) (bareDensityFunction lam h0 hpi b L)

/-- The source error is continuous by its exact finite/continuous
convolution expression, even though the counting primitive jumps. -/
def countingSourceError {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) : BoundedRealFunction :=
  atomicKernelFunction lam h0 hpi Y-
    boundedConvolution (kernelK lam) (kernelK_integrable lam h0 hpi)
      (finiteCountingFunction lam h0 hpi b L Y)


theorem countingSourceError_identity {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    countingSourceError lam (by linarith [Real.pi_pos]) hpi b L Y u=
      ∫ v : ℝ, kernelKPrime lam (u-v)*countingDiscrepancy lam b L Y v := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  change countingSourceError lam h0 hpi b L Y u=
    ∫ v : ℝ, physicalKernelPrimeFunction lam h0 hpi (u-v)*countingDiscrepancy lam b L Y v
  rw [countingDiscrepancy_kernel_identity lam b L hL hfill Y hhalf hpi
    (physicalKernelFunction lam h0 hpi) (physicalKernelPrimeFunction lam h0 hpi)
    (kernelK_integrable lam h0 hpi) (kernelKPrime_integrable lam h0 hpi)
    (fun v => hasDerivAt_kernelK lam v h0 hpi) u]
  change atomicKernelFunction lam h0 hpi Y u-
    (∫ t : ℝ, kernelK lam t*finiteCountingFunction lam h0 hpi b L Y (u-t))=_
  rw [atomicKernelFunction_apply,scalar_convolution_comm]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by
    change finiteCountingFunction lam h0 hpi b L Y v*kernelK lam (u-v)=kernelK lam (u-v)*countingSlope lam b L Y v
    rw [finiteCountingFunction_apply]
    ring)

theorem countingSourceError_norm_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0) :
    ‖countingSourceError lam (by linarith [Real.pi_pos]) hpi b L Y‖ ≤ kernelL1Mass (kernelKPrime lam)/2 := by
  apply (BoundedContinuousFunction.norm_le (by unfold kernelL1Mass; positivity)).mpr
  intro u
  rw [countingSourceError_identity lam b L hL hfill Y hhalf hpi u]
  exact countingDiscrepancy_kernel_bound lam b L hL hfill Y hhalf hpi hroots (kernelKPrime lam)
    (kernelKPrime_integrable lam (by linarith [Real.pi_pos]) hpi) u

theorem countingDensity_inverse_identity {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) :
    finiteCountingFunction lam h0 hpi b L Y-dressedBareDensityFunction lam h0 hpi b L=
      -boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
        (countingSourceError lam h0 hpi b L Y) := by
  let A := boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi)
  let B := boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
  let rho := finiteCountingFunction lam h0 hpi b L Y
  have he : rho+A rho=bareDensityFunction lam h0 hpi b L-countingSourceError lam h0 hpi b L Y := by
    change (bareDensityFunction lam h0 hpi b L-atomicKernelFunction lam h0 hpi Y)+A rho=
      bareDensityFunction lam h0 hpi b L-(atomicKernelFunction lam h0 hpi Y-A rho)
    abel
  have hi := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T rho)
    (boundedConvolutionInverse_left (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi))
  change B (rho+A rho)=rho at hi
  rw [he,map_sub] at hi
  change rho-B (bareDensityFunction lam h0 hpi b L)= -B (countingSourceError lam h0 hpi b L Y)
  rw [← hi]
  abel

/-- Uniform half-filled density discrepancy, for the actual inverse
dressing of the finite bare-source sum. -/
theorem countingDensity_discrepancy_norm_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0) :
    ‖finiteCountingFunction lam (by linarith [Real.pi_pos]) hpi b L Y-
      dressedBareDensityFunction lam (by linarith [Real.pi_pos]) hpi b L‖ ≤
      (1-kernelL1Mass (kernelK lam))⁻¹*(kernelL1Mass (kernelKPrime lam)/2) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  let B := boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
  rw [countingDensity_inverse_identity,norm_neg]
  apply (B.le_opNorm _).trans
  exact mul_le_mul (boundedConvolutionInverse_norm_bound (kernelK lam) (kernelK_integrable lam h0 hpi)
      (kernelK_L1_mass_lt_one lam h0 hpi))
    (countingSourceError_norm_bound lam b L hL hfill Y hhalf hpi hroots) (norm_nonneg _)
    (inv_nonneg.mpr (sub_pos.mpr (kernelK_L1_mass_lt_one lam h0 hpi)).le)


theorem boundedConvolution_translate (k : ℝ → ℝ) (hk : Integrable k) (f : BoundedRealFunction) (c : ℝ) :
    boundedConvolutionOperator k hk (translateBoundedFunction f c)=
      translateBoundedFunction (boundedConvolutionOperator k hk f) c := by
  ext u
  change (∫ t : ℝ, k t*f ((u-t)-c))=(∫ t : ℝ, k t*f ((u-c)-t))
  apply integral_congr_ae
  exact Eventually.of_forall (fun t => by
    change k t*f ((u-t)-c)=k t*f ((u-c)-t)
    rw [show (u-t)-c=(u-c)-t by ring])

theorem boundedConvolutionInverse_solution_unique (k : ℝ → ℝ) (hk : Integrable k)
    (hm : kernelL1Mass k < 1) (f g : BoundedRealFunction)
    (hsol : g+boundedConvolutionOperator k hk g=f) : boundedConvolutionInverse k hk f=g := by
  have hi := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T g)
    (boundedConvolutionInverse_left k hk hm)
  change boundedConvolutionInverse k hk (g+boundedConvolutionOperator k hk g)=g at hi
  rw [hsol] at hi
  exact hi

theorem boundedConvolutionInverse_translate (k : ℝ → ℝ) (hk : Integrable k)
    (hm : kernelL1Mass k < 1) (f : BoundedRealFunction) (c : ℝ) :
    boundedConvolutionInverse k hk (translateBoundedFunction f c)=
      translateBoundedFunction (boundedConvolutionInverse k hk f) c := by
  apply boundedConvolutionInverse_solution_unique k hk hm
  rw [boundedConvolution_translate]
  ext u
  exact congrArg (fun g : BoundedRealFunction => g (u-c)) (boundedConvolutionInverse_solves k hk hm f)

def fullLineDensityFunction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) : BoundedRealFunction :=
  boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi)
    (physicalKernelFunction (lam/2) (by linarith) (by linarith [Real.pi_pos]))

/-- Exact correspondence with the manuscript's p_L=sum_j r(u-b_j),
where r has its primary inverse-operator definition from Section 2. -/
theorem dressedBareDensityFunction_eq_sum (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (L : ℕ) :
    dressedBareDensityFunction lam h0 hpi b L=
      ∑ a ∈ Finset.range L, translateBoundedFunction (fullLineDensityFunction lam h0 hpi) (b a) := by
  unfold dressedBareDensityFunction bareDensityFunction fullLineDensityFunction
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact boundedConvolutionInverse_translate _ _ (kernelK_L1_mass_lt_one lam h0 hpi) _ _

theorem half_filled_density_uniform_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0) (u : ℝ) :
    |countingSlope lam b L Y u-
      (∑ a ∈ Finset.range L, fullLineDensityFunction lam (by linarith [Real.pi_pos]) hpi (u-b a))| ≤
      (1-kernelL1Mass (kernelK lam))⁻¹*(kernelL1Mass (kernelKPrime lam)/2) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hb := (finiteCountingFunction lam h0 hpi b L Y-dressedBareDensityFunction lam h0 hpi b L).norm_coe_le_norm u
  have hh := hb.trans (countingDensity_discrepancy_norm_bound lam b L hL hfill Y hhalf hpi hroots)
  rw [dressedBareDensityFunction_eq_sum] at hh
  simp only [BoundedContinuousFunction.sub_apply,BoundedContinuousFunction.sum_apply,
    finiteCountingFunction_apply,translateBoundedFunction,BoundedContinuousFunction.compContinuous_apply,
    Real.norm_eq_abs] at hh
  change |countingSlope lam b L Y u-(∑ a ∈ Finset.range L, fullLineDensityFunction lam h0 hpi (u-b a))| ≤ _ at hh
  exact hh

end
end SixVertex
