import SixVertex.CountingIntegration
import SixVertex.ResolventKernel

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem rootCountLe_measurable {n : ℕ} (Y : Fin n → ℝ) :
    Measurable (fun v => (rootCountLe Y v : ℝ)) := by
  have he : (fun v => (rootCountLe Y v : ℝ)) =
      fun v => ∑ j : Fin n, (Ici (Y j)).indicator (fun _ : ℝ => (1 : ℝ)) v :=
    funext (rootCountLe_eq_sum_indicators Y)
  rw [he]
  exact Finset.measurable_fun_sum Finset.univ (fun j _ => measurable_const.indicator measurableSet_Ici)

theorem rootCountLe_norm_bound {n : ℕ} (Y : Fin n → ℝ) (v : ℝ) :
    ‖(rootCountLe Y v : ℝ)‖ ≤ (n : ℝ) := by
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast rootCountLe_le Y v

/-- Integrability holds for a bounded measurable right factor, including
the discontinuous counting sawtooth. -/
theorem bounded_measurable_convolution_integrable (q F : ℝ → ℝ) (hq : Integrable q)
    (hF : AEStronglyMeasurable F) (C : ℝ) (hb : ∀ v, ‖F v‖ ≤ C) (u : ℝ) :
    Integrable (fun v : ℝ => q (u-v)*F v) :=
  (hq.comp_sub_left u).mul_bdd hF (Eventually.of_forall hb)

theorem bounded_measurable_convolution_bound (q F : ℝ → ℝ) (hq : Integrable q)
    (hF : AEStronglyMeasurable F) (C : ℝ) (hb : ∀ v, ‖F v‖ ≤ C) (u : ℝ) :
    ‖∫ v : ℝ, q (u-v)*F v‖ ≤ kernelL1Mass q*C := by
  calc
    _ ≤ ∫ v : ℝ, ‖q (u-v)*F v‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ v : ℝ, |q (u-v)| *C := by
      apply integral_mono_ae (bounded_measurable_convolution_integrable q F hq hF C hb u).norm
        ((hq.abs.comp_sub_left u).mul_const C)
      exact Eventually.of_forall (fun v => by
        change ‖q (u-v)*F v‖ ≤ |q (u-v)| *C
        rw [norm_mul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hb v) (abs_nonneg _))
    _ = _ := by
      rw [integral_mul_const]
      exact congrArg (fun x : ℝ => x*C) (integral_sub_left_eq_self (fun x : ℝ => |q x|) volume u)

def countingPrimitiveFunction {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) : BoundedRealFunction :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun u => countingXi lam b L Y u+(n : ℝ)/2)
    (continuous_iff_continuousAt.mpr (fun u =>
      (hasDerivAt_countingXi lam b L Y u (by linarith [Real.pi_pos]) hpi).continuousAt.add continuousAt_const))
    (n : ℝ) (fun u => by
      have hh := countingXi_half_bounds lam b L hL hfill Y hhalf hpi u
      change |countingXi lam b L Y u+(n : ℝ)/2| ≤ (n : ℝ)
      rw [abs_of_nonneg (by linarith [hh.1])]
      linarith [hh.2])

theorem countingDiscrepancy_aestronglyMeasurable {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    AEStronglyMeasurable (countingDiscrepancy lam b L Y) := by
  apply (rootCountLe_measurable Y).aestronglyMeasurable.sub
  apply Continuous.aestronglyMeasurable
  exact continuous_iff_continuousAt.mpr (fun u =>
    (hasDerivAt_countingXi lam b L Y u h0 hpi).continuousAt.add continuousAt_const)

/-- Exact discrete/smooth integration by parts for the actual counting
primitive. This identity does not assume the roots are on shell. -/
theorem countingDiscrepancy_kernel_identity {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (q q' : BoundedRealFunction) (hq : Integrable (fun x => q x)) (hq' : Integrable (fun x => q' x))
    (hdq : ∀ x, HasDerivAt (fun y => q y) (q' x) x) (u : ℝ) :
    (∫ v : ℝ, q' (u-v)*countingDiscrepancy lam b L Y v)=
      (∑ j : Fin n, q (u-Y j))-(∫ v : ℝ, q (u-v)*countingSlope lam b L Y v) := by
  let P := countingPrimitiveFunction lam b L hL hfill Y hhalf hpi
  have hp := countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi
  have hdP : ∀ x, HasDerivAt (fun y => P y) (countingSlope lam b L Y x) x := fun x =>
    (hasDerivAt_countingXi lam b L Y x (by linarith [Real.pi_pos]) hpi).add_const ((n : ℝ)/2)
  have hc := bounded_measurable_convolution_integrable (fun v => q' v)
    (fun v => (rootCountLe Y v : ℝ)) hq' (rootCountLe_measurable Y).aestronglyMeasurable (n : ℝ)
    (rootCountLe_norm_bound Y) u
  have hP := bounded_measurable_convolution_integrable (fun v => q' v)
    (fun v => P v) hq' P.continuous.aestronglyMeasurable ‖P‖ P.norm_coe_le_norm u
  change (∫ v : ℝ, q' (u-v)*((rootCountLe Y v : ℝ)-P v))=_
  simp_rw [mul_sub]
  rw [integral_sub hc hP,integral_derivative_kernel_rootCount Y q q' hq hq' hdq,
    ← convolution_primitive_integration_by_parts q q' P hq hq' _ hp hdq hdP u]

/-- The discrepancy kernel has a quantitative uniform bound independent
of the chain length and the real site array. -/
theorem countingDiscrepancy_kernel_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (hroots : ConsecutiveRoots lam b L Y 0)
    (q : ℝ → ℝ) (hq : Integrable q) (u : ℝ) :
    ‖∫ v : ℝ, q (u-v)*countingDiscrepancy lam b L Y v‖ ≤ kernelL1Mass q/2 := by
  have hb : ∀ v, ‖countingDiscrepancy lam b L Y v‖ ≤ (1/2 : ℝ) := fun v =>
    countingDiscrepancy_bound lam b L hL hfill Y hhalf hpi hroots v
  have h := bounded_measurable_convolution_bound q (countingDiscrepancy lam b L Y) hq
    (countingDiscrepancy_aestronglyMeasurable lam b L Y (by linarith [Real.pi_pos]) hpi) (1/2) hb u
  simpa only [div_eq_mul_inv,one_mul] using h

end
end SixVertex
