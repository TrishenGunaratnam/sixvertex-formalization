import SixVertex.CountingIntegration
import SixVertex.CountingDiscrepancyKernel

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem integral_derivative_Icc (f f' : ℝ → ℝ) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x) (a b : ℝ) (hab : a ≤ b) :
    (∫ x in Icc a b, f' x)=f b-f a := by
  rw [integral_Icc_eq_integral_Ioc,← intervalIntegral.integral_of_le hab]
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
    (hf'.intervalIntegrable (μ := volume) (a := a) (b := b))

/-- A counting jump inside a finite interval, including its endpoint term. -/
theorem integral_derivative_counting_jump_Icc (f f' : ℝ → ℝ) (hf' : Continuous f')
    (hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x) (a b y : ℝ) (hy : y ∈ Icc a b) :
    (∫ x in Icc a b, f' x*(Ici y).indicator (fun _ : ℝ => (1 : ℝ)) x)=f b-f y := by
  simp_rw [← Set.indicator_mul_right (Ici y) (fun x => f' x) (fun _ : ℝ => (1 : ℝ))]
  rw [integral_indicator measurableSet_Ici,Measure.restrict_restrict measurableSet_Ici]
  have he : Ici y ∩ Icc a b=Icc y b := by
    ext x
    simp only [mem_inter_iff,mem_Ici,mem_Icc]
    constructor
    · rintro ⟨hyx,hax,hxb⟩; exact ⟨hyx,hxb⟩
    · rintro ⟨hyx,hxb⟩; exact ⟨hyx,hy.1.trans hyx,hxb⟩
  rw [he]
  simp only [mul_one]
  exact integral_derivative_Icc f f' hf' hd y b hy.2

theorem integral_derivative_rootCount_Icc {n : ℕ} (Y : Fin n → ℝ)
    (f f' : ℝ → ℝ) (hf' : Continuous f') (hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x)
    (a b : ℝ) (hY : ∀ j, Y j ∈ Icc a b) :
    (∫ x in Icc a b, f' x*(rootCountLe Y x : ℝ))=(n : ℝ)*f b-∑ j : Fin n, f (Y j) := by
  simp_rw [rootCountLe_eq_sum_indicators,Finset.mul_sum]
  rw [integral_finsetSum]
  · simp_rw [integral_derivative_counting_jump_Icc f f' hf' hd a b _ (hY _)]
    simp only [Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  · intro j _
    simp_rw [← Set.indicator_mul_right (Ici (Y j)) (fun x => f' x) (fun _ : ℝ => (1 : ℝ))]
    exact ((hf'.integrableOn_Icc (μ := volume) (a := a) (b := b)).mul_const 1).indicator measurableSet_Ici

/-- Finite discrete/smooth integration by parts. Boundary terms cancel
because the actual primitive has the same total mass as the root list.
The test function itself need not be integrable on the whole line. -/
theorem finite_counting_integration_by_parts {n : ℕ} (Y : Fin n → ℝ)
    (f f' : ℝ → ℝ) (hf' : Continuous f') (hd : ∀ x, HasDerivAt (fun y => f y) (f' x) x)
    (P p : ℝ → ℝ) (hP : Continuous P) (hp : Continuous p)
    (hdP : ∀ x, HasDerivAt P (p x) x)
    (a b : ℝ) (hab : a ≤ b) (hY : ∀ j, Y j ∈ Icc a b)
    (ha : P a=0) (hb : P b=(n : ℝ)) :
    (∑ j : Fin n, f (Y j))-(∫ x in Icc a b, f x*p x)=
      -(∫ x in Icc a b, f' x*((rootCountLe Y x : ℝ)-P x)) := by
  have hs := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (a := a) (b := b) (fun x _ => hd x) (fun x _ => hdP x)
    (hf'.intervalIntegrable (μ := volume) a b) (hp.intervalIntegrable (μ := volume) a b)
  simp only [intervalIntegral.integral_of_le hab,← integral_Icc_eq_integral_Ioc] at hs
  rw [ha,hb,mul_zero,sub_zero] at hs
  have hc : IntegrableOn (fun x : ℝ => f' x*(rootCountLe Y x : ℝ)) (Icc a b) :=
    (hf'.integrableOn_Icc (μ := volume)).mul_bdd
      (rootCountLe_measurable Y).aestronglyMeasurable (Eventually.of_forall (rootCountLe_norm_bound Y))
  have hcp : IntegrableOn (fun x : ℝ => f' x*P x) (Icc a b) :=
    (hf'.mul hP).integrableOn_Icc
  simp_rw [mul_sub]
  rw [integral_sub hc hcp,integral_derivative_rootCount_Icc Y f f' hf' hd a b hY]
  linarith

end
end SixVertex
