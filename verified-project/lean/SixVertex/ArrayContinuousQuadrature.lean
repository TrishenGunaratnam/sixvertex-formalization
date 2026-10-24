import SixVertex.CompactQuadratureError
import SixVertex.UnitLipschitzRescaling

namespace SixVertex
noncomputable section
open Set MeasureTheory Filter Topology
open scoped NNReal

/-- The manuscript's moving-center, width-first array limit holds for
every compactly supported continuous real test, without a Lipschitz premise. -/
theorem array_bulk_continuous_quadrature_limit (lam : ℝ) (hhalf : Real.pi/2 < lam)
    (hpi : lam < Real.pi) (A : ℝ) (hA : 0 ≤ A) (gamma : ℝ) (hg : 0 < gamma) (hg1 : gamma < 1)
    (phi : BoundedRealFunction) (hs : ∀ x, x ∉ Icc (-A) A → phi x=0) :
    ∀ eps : ℝ, 0 < eps → ∃ d₀ B₀ : ℝ, 0 < d₀ ∧ 0 < B₀ ∧
      ∀ d : ℝ, 0 < d → d < d₀ → ∀ n L : ℕ, 0 < L → L=2*n →
      B₀ ≤ (L : ℝ)*d/2 → ∀ (Z : Fin n → ℝ), ConsecutiveRoots lam (arraySite L d) L Z 0 →
      ∀ a : ℝ, |a| ≤ (1-gamma)*((L : ℝ)*d/2)/2 →
      |(∫ x, phi (x-a) ∂rootQuadratureMeasure lam (arraySite L d) L Z)-(∫ x : ℝ, phi x)| ≤ eps := by
  intro eps heps
  let B : ℝ := A+1
  let M : ℝ := (Real.exp (kernelLogConstant lam*(2*B)))^2*(2*B)+
    Real.exp (kernelLogConstant lam*(2*B))/(-kernelK lam 0)+2*B
  have hB : 0 < B := by dsimp [B]; linarith
  have hk : 0 < -kernelK lam 0 := neg_pos.mpr (kernelK_strict_neg lam 0 hhalf hpi)
  have hM : 0 ≤ M := by dsimp [M]; positivity
  let delta : ℝ := eps/(4*(M+1))
  have hd : 0 < delta := div_pos heps (by positivity)
  obtain ⟨psi,K,hLip,hps,hnear⟩ := exists_compact_lipschitz_test_approximation phi A hA hs delta hd
  obtain ⟨D,tau,hD,htLip,htNorm,hscale,hzero⟩ := exists_unit_lipschitz_rescaling psi K hLip
  have hts : ∀ x, x ∉ Icc (-B) B → tau x=0 := fun x hx => hzero x (hps x hx)
  obtain ⟨d₀,B₀,hd₀,hB₀,hbound⟩ := array_bulk_quadrature_limit lam hhalf.le hpi B hB gamma hg hg1
    (eps/(2*D)) (div_pos heps (by positivity))
  refine ⟨d₀,B₀,hd₀,hB₀,?_⟩
  intro d hdp hdd n L hL hfill hwidth Z hZ a ha
  have ht := hbound d hdp hdd n L hL hfill hwidth Z hZ a ha tau htLip htNorm hts
  let phia := translateBoundedFunction phi a
  let psia := translateBoundedFunction psi a
  have hpS : ∀ x, x ∉ Icc (a-B) (a+B) → phia x=0 := by
    intro x hx
    change phi (x-a)=0
    apply hs
    intro hh
    apply hx
    exact ⟨by dsimp [B]; linarith [hh.1],by dsimp [B]; linarith [hh.2]⟩
  have hpsS : ∀ x, x ∉ Icc (a-B) (a+B) → psia x=0 := by
    intro x hx
    change psi (x-a)=0
    apply hps
    intro hh
    apply hx
    exact ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hnorm : ‖phia-psia‖ ≤ delta := by
    apply (BoundedContinuousFunction.norm_le hd.le).mpr
    intro x
    have hh := (phi-psi).norm_coe_le_norm (x-a)
    change ‖phi (x-a)-psi (x-a)‖ ≤ ‖phi-psi‖ at hh
    exact hh.trans hnear
  have hInt (f : BoundedRealFunction) : (∫ x : ℝ, f (x-a))=∫ x : ℝ, f x :=
    integral_sub_right_eq_self (fun x => f x) a
  have hi (mu : Measure ℝ) : (∫ x, psi (x-a) ∂mu)=D*(∫ x, tau (x-a) ∂mu) := by
    calc
      _ = ∫ x, D*tau (x-a) ∂mu := integral_congr_ae (Eventually.of_forall (fun x => hscale (x-a)))
      _ = _ := integral_const_mul _ _
  have hrate : |(∫ x, psia x ∂rootQuadratureMeasure lam (arraySite L d) L Z)-(∫ x : ℝ, psia x)| ≤ eps/2 := by
    change |(∫ x, psi (x-a) ∂rootQuadratureMeasure lam (arraySite L d) L Z)-(∫ x : ℝ, psi (x-a))| ≤ eps/2
    rw [hi,hi,← mul_sub,abs_mul,abs_of_pos hD,hInt]
    have hh := mul_le_mul_of_nonneg_left ht hD.le
    have heq : D*(eps/(2*D))=eps/2 := by field_simp
    exact hh.trans_eq heq
  have herr := compact_quadrature_error_transfer lam (arraySite L d) L hL Z hhalf hpi hZ
    phia psia (a-B) (a+B) delta (by linarith) hd.le hpS hpsS hnorm
  have hlen : (a+B)-(a-B)=2*B := by ring
  rw [hlen] at herr
  change |(∫ x, phi (x-a) ∂rootQuadratureMeasure lam (arraySite L d) L Z)-(∫ x : ℝ, phi (x-a))| ≤
    |(∫ x, psia x ∂rootQuadratureMeasure lam (arraySite L d) L Z)-(∫ x : ℝ, psia x)|+delta*M at herr
  rw [hInt] at herr
  have hdm : delta*M < eps/2 := by
    have hh : delta*(4*(M+1))=eps := by dsimp [delta]; field_simp
    nlinarith [mul_nonneg hd.le hM]
  linarith

end
end SixVertex
