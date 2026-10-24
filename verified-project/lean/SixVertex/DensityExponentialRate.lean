import SixVertex.ExplicitDensityIdentification
import SixVertex.BoundaryMassDeficit

namespace SixVertex
noncomputable section

/-- The actual full-line density has the exact exponential scale in the
paper, with explicit positive constants, throughout the physical range. -/
theorem fullLineDensityFunction_exponential_bounds (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q) :
    Real.exp (-Q/(lam/Real.pi))/(2*lam) ≤ fullLineDensityFunction lam h0 hpi Q ∧
      fullLineDensityFunction lam h0 hpi Q ≤ Real.exp (-Q/(lam/Real.pi))/lam := by
  rw [fullLineDensityFunction_eq_explicitDensityProfile lam h0 hpi Q]
  let t : ℝ := Q/(lam/Real.pi)
  have ht : 0 ≤ t := div_nonneg hQ (div_pos h0 Real.pi_pos).le
  have hc : Real.cosh t ≤ Real.exp t := by
    rw [Real.cosh_eq]
    have he := Real.exp_le_exp.mpr (show -t ≤ t by linarith)
    linarith
  have hc' : Real.exp t ≤ 2*Real.cosh t := by
    rw [Real.cosh_eq]
    linarith [Real.exp_pos (-t)]
  have he : Real.exp (-Q/(lam/Real.pi))=1/Real.exp t := by
    rw [neg_div]
    simpa only [one_div] using Real.exp_neg t
  rw [he]
  change (1/Real.exp t)/(2*lam) ≤ 1/(2*lam*Real.cosh t) ∧
    1/(2*lam*Real.cosh t) ≤ (1/Real.exp t)/lam
  constructor
  · calc
      _ = 1/(2*lam*Real.exp t) := by ring
      _ ≤ _ := one_div_le_one_div_of_le
        (mul_pos (mul_pos (by norm_num) h0) (Real.cosh_pos t))
        (mul_le_mul_of_nonneg_left hc (by positivity))
  · calc
      _ ≤ 1/(lam*Real.exp t) := one_div_le_one_div_of_le
        (mul_pos h0 (Real.exp_pos t)) (by nlinarith only [mul_le_mul_of_nonneg_left hc' h0.le])
      _ = _ := by ring

/-- The actual finite-window filling deficit has the manuscript's exact
exponential rate in the strict negative-kernel regime. -/
theorem exists_finiteIntervalMass_deficit_exponential_comparison (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Q : ℝ, 0 ≤ Q →
      c*Real.exp (-Q/(lam/Real.pi)) ≤ 1/2-finiteIntervalMass lam h0 hpi Q ∧
      1/2-finiteIntervalMass lam h0 hpi Q ≤ C*Real.exp (-Q/(lam/Real.pi)) := by
  obtain ⟨c,C,hc,hC,hbound⟩ := exists_finiteIntervalMass_deficit_boundary_comparison lam h0 hhalf hpi
  refine ⟨c/(2*lam),C/lam,div_pos hc (mul_pos (by norm_num) h0),div_pos hC h0,?_⟩
  intro Q hQ
  have he := fullLineDensityFunction_exponential_bounds lam h0 hpi Q hQ
  have hb := hbound Q hQ
  constructor
  · calc
      _ = c*(Real.exp (-Q/(lam/Real.pi))/(2*lam)) := by ring
      _ ≤ c*fullLineDensityFunction lam h0 hpi Q := mul_le_mul_of_nonneg_left he.1 hc.le
      _ ≤ _ := hb.1
  · calc
      _ ≤ C*fullLineDensityFunction lam h0 hpi Q := hb.2
      _ ≤ C*(Real.exp (-Q/(lam/Real.pi))/lam) := mul_le_mul_of_nonneg_left he.2 hC.le
      _ = _ := by ring

end
end SixVertex
