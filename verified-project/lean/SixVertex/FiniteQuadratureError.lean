import SixVertex.FiniteCountingIntegration

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Local finite quadrature for actual C1 tests, without a boundedness or
integrability requirement away from the reference interval. -/
theorem finite_counting_local_quadrature_error {n : ℕ} (Y : Fin n → ℝ)
    (f f' : ℝ → ℝ) (hfcont : Continuous f') (hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x)
    (P p : ℝ → ℝ) (hP : Continuous P) (hp : Continuous p)
    (hdP : ∀ x, HasDerivAt P (p x) x)
    (a b : ℝ) (hab : a ≤ b) (hY : ∀ j, Y j ∈ Icc a b)
    (ha : P a=0) (hb : P b=(n : ℝ))
    (hF : ∀ x ∈ Icc a b, |(rootCountLe Y x : ℝ)-P x| ≤ 1/2) :
    |(∑ j : Fin n, f (Y j))-(∫ x in Icc a b, f x*p x)| ≤ (∫ x in Icc a b, |f' x|)/2 := by
  rw [finite_counting_integration_by_parts Y f f' hfcont hd P p hP hp hdP a b hab hY ha hb,abs_neg,← Real.norm_eq_abs]
  have hc : IntegrableOn (fun x : ℝ => f' x*(rootCountLe Y x : ℝ)) (Icc a b) :=
    (hfcont.integrableOn_Icc (μ := volume)).mul_bdd
      (rootCountLe_measurable Y).aestronglyMeasurable (Eventually.of_forall (rootCountLe_norm_bound Y))
  have hcp : IntegrableOn (fun x : ℝ => f' x*P x) (Icc a b) :=
    (hfcont.mul hP).integrableOn_Icc
  have hFint : IntegrableOn (fun x : ℝ => f' x*((rootCountLe Y x : ℝ)-P x)) (Icc a b) := by
    simpa only [mul_sub,Pi.sub_apply] using! hc.sub hcp
  calc
    _ ≤ ∫ x in Icc a b, ‖f' x*((rootCountLe Y x : ℝ)-P x)‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ x in Icc a b, |f' x| *(1/2) := by
      apply integral_mono_ae hFint.norm ((hfcont.abs.integrableOn_Icc (μ := volume)).mul_const (1/2 : ℝ))
      apply (ae_restrict_iff' measurableSet_Icc).mpr
      exact Eventually.of_forall (fun x hx => by
        simp only [norm_mul,Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hF x hx) (abs_nonneg _))
    _ = (∫ x in Icc a b, |f' x|)*(1/2) := integral_mul_const _ _
    _ = _ := by ring

/-- Whole-line derivative L1 bound, including bounded nonintegrable phases. -/
theorem finite_counting_quadrature_error {n : ℕ} (Y : Fin n → ℝ)
    (f f' : BoundedRealFunction) (hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x)
    (hf' : Integrable (fun x => f' x))
    (P p : ℝ → ℝ) (hP : Continuous P) (hp : Continuous p)
    (hdP : ∀ x, HasDerivAt P (p x) x)
    (a b : ℝ) (hab : a ≤ b) (hY : ∀ j, Y j ∈ Icc a b)
    (ha : P a=0) (hb : P b=(n : ℝ))
    (hF : ∀ x ∈ Icc a b, |(rootCountLe Y x : ℝ)-P x| ≤ 1/2) :
    |(∑ j : Fin n, f (Y j))-(∫ x in Icc a b, f x*p x)| ≤ kernelL1Mass (fun x => f' x)/2 := by
  apply (finite_counting_local_quadrature_error Y f f' f'.continuous hd P p hP hp hdP a b hab hY ha hb hF).trans
  exact div_le_div_of_nonneg_right
    (setIntegral_le_integral hf'.abs (Eventually.of_forall (fun x => abs_nonneg (f' x)))) (by norm_num)

end
end SixVertex
