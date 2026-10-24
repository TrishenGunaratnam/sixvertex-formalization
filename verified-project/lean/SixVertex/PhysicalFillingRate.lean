import SixVertex.PhysicalDensityExteriorRate
import SixVertex.PositiveWindowMass

namespace SixVertex
noncomputable section

/-- The exact exponential filling-deficit clause of Lemma 3.1, with
constants fixed before every cutoff, for all physical lambda including
the free point. -/
theorem exists_finiteIntervalMass_deficit_exponential_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) :
    ∃ c C : ℝ,0 < c ∧ 0 < C ∧ ∀ Q : ℝ,0 ≤ Q →
      c*Real.exp (-Q/(lam/Real.pi)) ≤ 1/2-finiteIntervalMass lam h0 hpi Q ∧
      1/2-finiteIntervalMass lam h0 hpi Q ≤ C*Real.exp (-Q/(lam/Real.pi)) := by
  let d : ℝ := 2*(1-lam/Real.pi)
  have hd : 0 < d := mul_pos (by norm_num) (sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hpi))
  by_cases hh : Real.pi/2 ≤ lam
  · refine ⟨1/Real.pi,2/(Real.pi*d),one_div_pos.mpr Real.pi_pos,
      div_pos (by norm_num) (mul_pos Real.pi_pos hd),?_⟩
    intro Q hQ
    have he := fullLineDensityExteriorMass_exponential_bounds lam h0 hpi Q hQ
    have hb := finiteIntervalMass_deficit_bounds lam h0 hh hpi Q
    constructor
    · calc
        _ = Real.exp (-Q/(lam/Real.pi))/Real.pi := by ring
        _ ≤ fullLineDensityExteriorMass lam h0 hpi Q := he.1
        _ ≤ _ := hb.1
    · calc
        _ ≤ fullLineDensityExteriorMass lam h0 hpi Q/d := hb.2
        _ ≤ (2*Real.exp (-Q/(lam/Real.pi))/Real.pi)/d := div_le_div_of_nonneg_right he.2 hd.le
        _ = _ := by field_simp [Real.pi_ne_zero,hd.ne']
  · have hp : lam < Real.pi/2 := lt_of_not_ge hh
    refine ⟨1/(Real.pi*d),2/Real.pi,one_div_pos.mpr (mul_pos Real.pi_pos hd),
      div_pos (by norm_num) Real.pi_pos,?_⟩
    intro Q hQ
    have he := fullLineDensityExteriorMass_exponential_bounds lam h0 hpi Q hQ
    have hb := finiteIntervalMass_deficit_bounds_positiveK lam h0 hp Q
    constructor
    · calc
        _ = (Real.exp (-Q/(lam/Real.pi))/Real.pi)/d := by field_simp [Real.pi_ne_zero,hd.ne']
        _ ≤ fullLineDensityExteriorMass lam h0 hpi Q/d := div_le_div_of_nonneg_right he.1 hd.le
        _ ≤ _ := hb.1
    · calc
        _ ≤ fullLineDensityExteriorMass lam h0 hpi Q := hb.2
        _ ≤ 2*Real.exp (-Q/(lam/Real.pi))/Real.pi := he.2
        _ = _ := by ring

end
end SixVertex
