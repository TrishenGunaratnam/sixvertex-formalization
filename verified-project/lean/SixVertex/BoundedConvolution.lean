import SixVertex.KernelMass
import Mathlib.Analysis.Convolution
import Mathlib.Topology.ContinuousMap.Bounded.Normed
import Mathlib.Analysis.Normed.Ring.Units

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

abbrev BoundedRealFunction := BoundedContinuousFunction ℝ ℝ

def kernelL1Mass (k : ℝ → ℝ) : ℝ := ∫ t : ℝ, |k t|

theorem kernelL1Mass_nonneg (k : ℝ → ℝ) : 0 ≤ kernelL1Mass k :=
  integral_nonneg (fun t => abs_nonneg _)

def boundedConvolutionValue (k : ℝ → ℝ) (f : BoundedRealFunction) (x : ℝ) : ℝ :=
  ∫ t : ℝ, k t*f (x-t)

theorem boundedConvolution_integrand_integrable (k : ℝ → ℝ) (hk : Integrable k)
    (f : BoundedRealFunction) (x : ℝ) : Integrable (fun t : ℝ => k t*f (x-t)) := by
  apply hk.mul_bdd ((f.continuous.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
  exact Eventually.of_forall (fun t => f.norm_coe_le_norm (x-t))

theorem boundedConvolution_value_bound (k : ℝ → ℝ) (hk : Integrable k)
    (f : BoundedRealFunction) (x : ℝ) :
    ‖boundedConvolutionValue k f x‖ ≤ kernelL1Mass k*‖f‖ := by
  calc
    _ ≤ ∫ t : ℝ, ‖k t*f (x-t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, |k t| *‖f‖ := by
      apply integral_mono_ae (boundedConvolution_integrand_integrable k hk f x).norm
        (hk.abs.mul_const ‖f‖)
      apply Eventually.of_forall
      intro t
      change ‖k t*f (x-t)‖ ≤ |k t| * ‖f‖
      rw [norm_mul,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm (x-t)) (abs_nonneg _)
    _ = _ := by rw [integral_mul_const]; rfl

theorem continuous_boundedConvolutionValue (k : ℝ → ℝ) (hk : Integrable k)
    (f : BoundedRealFunction) : Continuous (boundedConvolutionValue k f) := by
  have hb : BddAbove (range (fun x : ℝ => ‖f x‖)) := by
    refine ⟨‖f‖,?_⟩
    rintro y ⟨x,rfl⟩
    exact f.norm_coe_le_norm x
  exact hb.continuous_convolution_right_of_integrable (ContinuousLinearMap.mul ℝ ℝ) hk f.continuous

def boundedConvolution (k : ℝ → ℝ) (hk : Integrable k) (f : BoundedRealFunction) : BoundedRealFunction :=
  BoundedContinuousFunction.ofNormedAddCommGroup (boundedConvolutionValue k f)
    (continuous_boundedConvolutionValue k hk f) (kernelL1Mass k*‖f‖)
    (boundedConvolution_value_bound k hk f)

theorem boundedConvolution_norm_bound (k : ℝ → ℝ) (hk : Integrable k) (f : BoundedRealFunction) :
    ‖boundedConvolution k hk f‖ ≤ kernelL1Mass k*‖f‖ := by
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (kernelL1Mass_nonneg k) (norm_nonneg f))).mpr
  exact boundedConvolution_value_bound k hk f

def boundedConvolutionLinear (k : ℝ → ℝ) (hk : Integrable k) : BoundedRealFunction →ₗ[ℝ] BoundedRealFunction where
  toFun := boundedConvolution k hk
  map_add' := by
    intro f g
    ext x
    change (∫ t : ℝ, k t*(f (x-t)+g (x-t)))=(∫ t : ℝ,k t*f (x-t))+(∫ t : ℝ,k t*g (x-t))
    simp_rw [mul_add]
    exact integral_add (boundedConvolution_integrand_integrable k hk f x)
      (boundedConvolution_integrand_integrable k hk g x)
  map_smul' := by
    intro c f
    ext x
    change (∫ t : ℝ, k t*(c*f (x-t)))=c*(∫ t : ℝ,k t*f (x-t))
    rw [← integral_const_mul]
    congr 1
    funext t
    ring

def boundedConvolutionOperator (k : ℝ → ℝ) (hk : Integrable k) : BoundedRealFunction →L[ℝ] BoundedRealFunction :=
  (boundedConvolutionLinear k hk).mkContinuous (kernelL1Mass k) (boundedConvolution_norm_bound k hk)

theorem boundedConvolutionOperator_apply (k : ℝ → ℝ) (hk : Integrable k) (f : BoundedRealFunction) (x : ℝ) :
    boundedConvolutionOperator k hk f x=∫ t : ℝ,k t*f (x-t) := rfl

theorem boundedConvolutionOperator_norm_bound (k : ℝ → ℝ) (hk : Integrable k) :
    ‖boundedConvolutionOperator k hk‖ ≤ kernelL1Mass k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (kernelL1Mass_nonneg k)
  exact boundedConvolution_norm_bound k hk

/-- The inverse is constructed by its operator-norm convergent Neumann
series. Its domain here is the actual Banach space of bounded continuous
functions; no claim about a resolvent convolution kernel is hidden in it. -/
def boundedConvolutionInverse (k : ℝ → ℝ) (hk : Integrable k) : BoundedRealFunction →L[ℝ] BoundedRealFunction :=
  ∑' m : ℕ, (-(boundedConvolutionOperator k hk))^m

theorem operator_neumann_left (A : BoundedRealFunction →L[ℝ] BoundedRealFunction) (hA : ‖A‖ < 1) :
    (∑' m : ℕ, (-A)^m)*(1+A)=1 := by
  have hn : ‖-A‖ < 1 := (norm_neg A).trans_lt hA
  exact (congrArg (fun T => (∑' m : ℕ, (-A)^m)*T) (sub_neg_eq_add (1 : BoundedRealFunction →L[ℝ] BoundedRealFunction) A)).symm.trans (geom_series_mul_neg (-A) hn)

theorem operator_neumann_right (A : BoundedRealFunction →L[ℝ] BoundedRealFunction) (hA : ‖A‖ < 1) :
    (1+A)*(∑' m : ℕ, (-A)^m)=1 := by
  have hn : ‖-A‖ < 1 := (norm_neg A).trans_lt hA
  exact (congrArg (fun T => T*(∑' m : ℕ, (-A)^m)) (sub_neg_eq_add (1 : BoundedRealFunction →L[ℝ] BoundedRealFunction) A)).symm.trans (mul_neg_geom_series (-A) hn)

theorem operator_neumann_norm_bound (A : BoundedRealFunction →L[ℝ] BoundedRealFunction) (hA : ‖A‖ < 1) :
    ‖∑' m : ℕ, (-A)^m‖ ≤ (1-‖A‖)⁻¹ := by
  have hn : ‖-A‖ < 1 := (norm_neg A).trans_lt hA
  have h := tsum_geometric_le_of_norm_lt_one (-A) hn
  have hn1 : ‖(1 : BoundedRealFunction →L[ℝ] BoundedRealFunction)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
  have hnA := norm_neg A
  rw [hnA] at h
  linarith

theorem boundedConvolutionInverse_left (k : ℝ → ℝ) (hk : Integrable k) (hm : kernelL1Mass k < 1) :
    boundedConvolutionInverse k hk*(1+boundedConvolutionOperator k hk)=1 :=
  operator_neumann_left _ ((boundedConvolutionOperator_norm_bound k hk).trans_lt hm)

theorem boundedConvolutionInverse_right (k : ℝ → ℝ) (hk : Integrable k) (hm : kernelL1Mass k < 1) :
    (1+boundedConvolutionOperator k hk)*boundedConvolutionInverse k hk=1 :=
  operator_neumann_right _ ((boundedConvolutionOperator_norm_bound k hk).trans_lt hm)

theorem boundedConvolutionInverse_norm_bound (k : ℝ → ℝ) (hk : Integrable k) (hm : kernelL1Mass k < 1) :
    ‖boundedConvolutionInverse k hk‖ ≤ (1-kernelL1Mass k)⁻¹ := by
  have hnorm:=boundedConvolutionOperator_norm_bound k hk
  apply (operator_neumann_norm_bound _ (hnorm.trans_lt hm)).trans
  simpa only [one_div] using one_div_le_one_div_of_le (sub_pos.mpr hm) (sub_le_sub_left hnorm 1)

theorem boundedConvolutionInverse_solves (k : ℝ → ℝ) (hk : Integrable k) (hm : kernelL1Mass k < 1)
    (f : BoundedRealFunction) :
    boundedConvolutionInverse k hk f+boundedConvolutionOperator k hk (boundedConvolutionInverse k hk f)=f := by
  have h:=congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T f)
    (boundedConvolutionInverse_right k hk hm)
  exact h

/-- The manuscript's physical kernel has a genuine bounded inverse on
bounded continuous functions for every 0 < lambda < pi. -/
theorem physical_kernel_bounded_inverse (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ B : BoundedRealFunction →L[ℝ] BoundedRealFunction,
      B*(1+boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))=1 ∧
      (1+boundedConvolutionOperator (kernelK lam) (kernelK_integrable lam h0 hpi))*B=1 ∧
      ‖B‖ ≤ (1-|1-2*lam/Real.pi|)⁻¹ := by
  have hm : kernelL1Mass (kernelK lam) < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  refine ⟨boundedConvolutionInverse (kernelK lam) (kernelK_integrable lam h0 hpi),
    boundedConvolutionInverse_left _ _ hm,boundedConvolutionInverse_right _ _ hm,?_⟩
  have hb:=boundedConvolutionInverse_norm_bound (kernelK lam) (kernelK_integrable lam h0 hpi) hm
  simpa only [kernelL1Mass,integral_abs_kernelK lam h0 hpi] using hb

end
end SixVertex
