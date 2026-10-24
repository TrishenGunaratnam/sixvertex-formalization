import SixVertex.BoundedConvolution
import SixVertex.WeightedKernel

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Conjugation by the two-sided weight exp(a*abs x). -/
def absoluteWeightedValue (k : ℝ → ℝ) (a : ℝ) (f : BoundedRealFunction) (x : ℝ) : ℝ :=
  ∫ t : ℝ, k t*Real.exp (a*(|x|-|x-t|))*f (x-t)

theorem absoluteWeight_ratio_bound (a : ℝ) (ha : 0 ≤ a) (x t : ℝ) :
    Real.exp (a*(|x|-|x-t|)) ≤ Real.exp (a*|t|) := by
  apply Real.exp_le_exp.mpr
  apply mul_le_mul_of_nonneg_left _ ha
  have h := abs_add_le (x-t) t
  rw [sub_add_cancel] at h
  linarith

theorem absoluteWeighted_integrand_bound (k : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (f : BoundedRealFunction) (x t : ℝ) :
    ‖k t*Real.exp (a*(|x|-|x-t|))*f (x-t)‖ ≤
      (Real.exp (a*|t|)*|k t|)*‖f‖ := by
  rw [norm_mul,norm_mul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ (|k t| *Real.exp (a*|t|))*‖f‖ :=
      mul_le_mul (mul_le_mul_of_nonneg_left (absoluteWeight_ratio_bound a ha x t) (abs_nonneg _))
        (f.norm_coe_le_norm (x-t)) (norm_nonneg _) (by positivity)
    _ = _ := by ring

theorem absoluteWeighted_integrand_integrable (k : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hk : AEStronglyMeasurable k) (hw : Integrable (fun t : ℝ => Real.exp (a*|t|)*|k t|))
    (f : BoundedRealFunction) (x : ℝ) :
    Integrable (fun t : ℝ => k t*Real.exp (a*(|x|-|x-t|))*f (x-t)) := by
  apply (hw.mul_const ‖f‖).mono' (hk.mul (by fun_prop) |>.mul (by fun_prop))
  exact Eventually.of_forall (absoluteWeighted_integrand_bound k a ha f x)

theorem absoluteWeightedValue_bound (k : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hk : AEStronglyMeasurable k) (hw : Integrable (fun t : ℝ => Real.exp (a*|t|)*|k t|))
    (f : BoundedRealFunction) (x : ℝ) :
    ‖absoluteWeightedValue k a f x‖ ≤ (∫ t : ℝ, Real.exp (a*|t|)*|k t|)*‖f‖ := by
  calc
    _ ≤ ∫ t : ℝ, ‖k t*Real.exp (a*(|x|-|x-t|))*f (x-t)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ, (Real.exp (a*|t|)*|k t|)*‖f‖ := by
      apply integral_mono_ae (absoluteWeighted_integrand_integrable k a ha hk hw f x).norm
        (hw.mul_const ‖f‖)
      exact Eventually.of_forall (absoluteWeighted_integrand_bound k a ha f x)
    _ = _ := integral_mul_const _ _

theorem absoluteWeightedValue_continuous (k : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hk : AEStronglyMeasurable k) (hw : Integrable (fun t : ℝ => Real.exp (a*|t|)*|k t|))
    (f : BoundedRealFunction) : Continuous (absoluteWeightedValue k a f) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun t : ℝ => (Real.exp (a*|t|)*|k t|)*‖f‖)
  · exact Eventually.of_forall (fun y => hk.mul (by fun_prop) |>.mul (by fun_prop))
  · exact Eventually.of_forall (fun y => Eventually.of_forall (absoluteWeighted_integrand_bound k a ha f y))
  · exact hw.mul_const ‖f‖
  · exact Eventually.of_forall (fun t => by fun_prop)

def absoluteWeightedConvolution (k : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hk : AEStronglyMeasurable k) (hw : Integrable (fun t : ℝ => Real.exp (a*|t|)*|k t|))
    (f : BoundedRealFunction) : BoundedRealFunction :=
  BoundedContinuousFunction.ofNormedAddCommGroup (absoluteWeightedValue k a f)
    (absoluteWeightedValue_continuous k a ha hk hw f) _ (absoluteWeightedValue_bound k a ha hk hw f)

def absoluteWeightedLinear (k : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hk : AEStronglyMeasurable k) (hw : Integrable (fun t : ℝ => Real.exp (a*|t|)*|k t|)) :
    BoundedRealFunction →ₗ[ℝ] BoundedRealFunction where
  toFun := absoluteWeightedConvolution k a ha hk hw
  map_add' := by
    intro f g
    ext x
    change (∫ t : ℝ, k t*Real.exp (a*(|x|-|x-t|))*(f (x-t)+g (x-t)))=_
    simp_rw [mul_add]
    exact integral_add (absoluteWeighted_integrand_integrable k a ha hk hw f x)
      (absoluteWeighted_integrand_integrable k a ha hk hw g x)
  map_smul' := by
    intro c f
    ext x
    change (∫ t : ℝ,k t*Real.exp (a*(|x|-|x-t|))*(c*f (x-t)))=c*(∫ t : ℝ,k t*Real.exp (a*(|x|-|x-t|))*f (x-t))
    rw [← integral_const_mul]
    congr 1
    funext t
    ring

def absoluteWeightedOperator (k : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hk : AEStronglyMeasurable k) (hw : Integrable (fun t : ℝ => Real.exp (a*|t|)*|k t|)) :
    BoundedRealFunction →L[ℝ] BoundedRealFunction :=
  (absoluteWeightedLinear k a ha hk hw).mkContinuous (∫ t : ℝ, Real.exp (a*|t|)*|k t|) (by
    intro f
    apply (BoundedContinuousFunction.norm_le (mul_nonneg (integral_nonneg (by intro t; positivity)) (norm_nonneg f))).mpr
    exact absoluteWeightedValue_bound k a ha hk hw f)

theorem absoluteWeightedOperator_norm_bound (k : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hk : AEStronglyMeasurable k) (hw : Integrable (fun t : ℝ => Real.exp (a*|t|)*|k t|)) :
    ‖absoluteWeightedOperator k a ha hk hw‖ ≤ ∫ t : ℝ, Real.exp (a*|t|)*|k t| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (integral_nonneg (by intro t; positivity))
  intro f
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (integral_nonneg (by intro t; positivity)) (norm_nonneg f))).mpr
  exact absoluteWeightedValue_bound k a ha hk hw f


theorem integrable_exp_neg_mul_abs (a : ℝ) (ha : 0 < a) :
    Integrable (fun x : ℝ => Real.exp (-a*|x|)) := by
  have hl : IntegrableOn (fun x : ℝ => Real.exp (-a*|x|)) (Iic 0) :=
    (integrableOn_exp_mul_Iic ha 0).congr_fun (fun x hx => by
      simp only [abs_of_nonpos (show x ≤ 0 from hx), neg_mul, mul_neg, neg_neg]) measurableSet_Iic
  have hr : IntegrableOn (fun x : ℝ => Real.exp (-a*|x|)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos ha) 0).congr_fun (fun x hx => by
      rw [abs_of_pos hx]) measurableSet_Ioi
  rw [← integrableOn_univ,← Iic_union_Ioi (a := (0 : ℝ)),integrableOn_union]
  exact ⟨hl,hr⟩

def unweightValue (a : ℝ) (f : BoundedRealFunction) (x : ℝ) : ℝ := Real.exp (-a*|x|)*f x

theorem unweightValue_bound (a : ℝ) (f : BoundedRealFunction) (x : ℝ) :
    |unweightValue a f x| ≤ ‖f‖*Real.exp (-a*|x|) := by
  unfold unweightValue
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  exact (mul_le_mul_of_nonneg_left (f.norm_coe_le_norm x) (Real.exp_pos _).le).trans_eq (mul_comm _ _)

theorem unweightValue_integrable (a : ℝ) (ha : 0 < a) (f : BoundedRealFunction) :
    Integrable (unweightValue a f) := by
  apply ((integrable_exp_neg_mul_abs a ha).const_mul ‖f‖).mono' (by unfold unweightValue; fun_prop)
  exact Eventually.of_forall (unweightValue_bound a f)

theorem unweight_absoluteWeightedValue (k : ℝ → ℝ) (a : ℝ)
    (f : BoundedRealFunction) (x : ℝ) :
    Real.exp (-a*|x|)*absoluteWeightedValue k a f x =
      ∫ t : ℝ, k t*unweightValue a f (x-t) := by
  unfold absoluteWeightedValue
  rw [← integral_const_mul]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro t
  have he : Real.exp (-a*|x|)*Real.exp (a*(|x|-|x-t|)) = Real.exp (-a*|x-t|) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold unweightValue
  calc
    _ = k t*(Real.exp (-a*|x|)*Real.exp (a*(|x|-|x-t|)))*f (x-t) := by ring
    _ = _ := by rw [he]; ring

def weightedDecayFunction (k : ℝ → ℝ) (hk : Continuous k) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ x, |k x| ≤ C*Real.exp (-2*|x|)) (a : ℝ) (ha : a ≤ 1) : BoundedRealFunction :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun x : ℝ => Real.exp (a*|x|)*k x)
    (by fun_prop) C (by
      intro x
      apply (exponential_weight_majorant k C hC hdecay a ha x).trans
      apply mul_le_of_le_one_right hC
      exact Real.exp_le_one_iff.mpr (by linarith [abs_nonneg x]))

theorem unweight_weightedDecayFunction (k : ℝ → ℝ) (hk : Continuous k) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ x, |k x| ≤ C*Real.exp (-2*|x|)) (a : ℝ) (ha : a ≤ 1) (x : ℝ) :
    unweightValue a (weightedDecayFunction k hk C hC hdecay a ha) x=k x := by
  change Real.exp (-a*|x|)*(Real.exp (a*|x|)*k x)=k x
  rw [← mul_assoc,← Real.exp_add,show -a*|x|+a*|x|=0 by ring,Real.exp_zero,one_mul]

/-- A genuine continuous, integrable full-line resolvent kernel with
exponential decay, constructed from the two-sided weighted Neumann series. -/
theorem exists_exponentially_decaying_kernel_resolvent (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ a C : ℝ, 0 < a ∧ 0 ≤ C ∧ ∃ R : ℝ → ℝ,
      Continuous R ∧ Integrable R ∧
      (∀ x, |R x| ≤ C*Real.exp (-a*|x|)) ∧
      ∀ x, R x+(∫ t : ℝ, kernelK lam t*R (x-t))=kernelK lam x := by
  obtain ⟨a,ha0,ha1,hi,hm⟩ := exists_positive_weight_kernel_contraction lam h0 hpi
  have hk : Continuous (kernelK lam) := continuous_phaseDensity lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  let A := absoluteWeightedOperator (kernelK lam) a ha0.le hk.aestronglyMeasurable hi
  have hA : ‖A‖ < 1 := (absoluteWeightedOperator_norm_bound _ _ ha0.le hk.aestronglyMeasurable hi).trans_lt hm
  let f := weightedDecayFunction (kernelK lam) hk (2/(Real.pi*(Real.sin lam)^2)) (by positivity)
    (fun x => kernelK_exponential_bound lam x h0 hpi) a ha1.le
  let B : BoundedRealFunction →L[ℝ] BoundedRealFunction := ∑' m : ℕ, (-A)^m
  let g := B f
  have hs : g+A g=f := congrArg (fun T : BoundedRealFunction →L[ℝ] BoundedRealFunction => T f)
    (operator_neumann_right A hA)
  refine ⟨a,‖g‖,ha0,norm_nonneg _,unweightValue a g,by unfold unweightValue; fun_prop,
    unweightValue_integrable a ha0 g,unweightValue_bound a g,?_⟩
  intro x
  have hx := congrArg (fun v : BoundedRealFunction => Real.exp (-a*|x|)*v x) hs
  change Real.exp (-a*|x|)*(g x+absoluteWeightedValue (kernelK lam) a g x)=Real.exp (-a*|x|)*f x at hx
  rw [mul_add,unweight_absoluteWeightedValue] at hx
  change unweightValue a g x+(∫ t : ℝ, kernelK lam t*unweightValue a g (x-t))=unweightValue a f x at hx
  rw [unweight_weightedDecayFunction] at hx
  exact hx

end
end SixVertex
