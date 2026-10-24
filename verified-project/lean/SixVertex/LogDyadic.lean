import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal

/-- The infinite diagonal singularity is retained explicitly. -/
def logSingularity (d : ℝ) : ℝ≥0∞ :=
  if d=0 then ⊤ else ENNReal.ofReal (max (-Real.log d) 0)

def dyadicProximity (d : ℝ) : ℝ≥0∞ :=
  ∑' j : ℕ, if d ≤ ((2 : ℝ)^j)⁻¹ then 1 else 0

theorem dyadic_threshold_log (d : ℝ) (hd : 0 < d) (j : ℕ) :
    d ≤ ((2 : ℝ)^j)⁻¹ ↔ (j : ℝ) ≤ -Real.log d/Real.log 2 := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [← Real.log_le_log_iff hd (by positivity),Real.log_inv,Real.log_pow]
  rw [le_div_iff₀ h2]
  constructor <;> intro h <;> linarith

theorem dyadicProximity_positive_formula (d : ℝ) (hd : 0 < d)
    (hq : 0 ≤ -Real.log d/Real.log 2) :
    dyadicProximity d=(⌊-Real.log d/Real.log 2⌋₊+1 : ℕ) := by
  unfold dyadicProximity
  have hcond : ∀ j : ℕ, d ≤ ((2 : ℝ)^j)⁻¹ ↔ j < ⌊-Real.log d/Real.log 2⌋₊+1 := by
    intro j
    rw [dyadic_threshold_log d hd j,← Nat.le_floor_iff hq]
    omega
  simp_rw [hcond]
  rw [tsum_eq_sum (s := Finset.range (⌊-Real.log d/Real.log 2⌋₊+1))]
  · calc
      _ = ∑ j ∈ Finset.range (⌊-Real.log d/Real.log 2⌋₊+1), (1 : ℝ≥0∞) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [if_pos (Finset.mem_range.mp hj)]
      _ = _ := by simp
  · intro j hj
    simp only [Finset.mem_range,not_lt] at hj
    simp [not_lt.mpr hj]

theorem dyadicProximity_negative_formula (d : ℝ) (hd : 0 < d)
    (hq : -Real.log d/Real.log 2 < 0) : dyadicProximity d=0 := by
  unfold dyadicProximity
  have hz : ∀ j : ℕ, (if d ≤ ((2 : ℝ)^j)⁻¹ then 1 else 0 : ℝ≥0∞)=0 := by
    intro j
    apply if_neg
    rw [dyadic_threshold_log d hd j]
    exact not_le.mpr (hq.trans_le (Nat.cast_nonneg j))
  simp_rw [hz]
  simp

theorem dyadicProximity_upper (d : ℝ) (hd : 0 < d) :
    dyadicProximity d ≤ ENNReal.ofReal (1+max (-Real.log d) 0/Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hq : 0 ≤ -Real.log d/Real.log 2
  · rw [dyadicProximity_positive_formula d hd hq]
    have hlog : 0 ≤ -Real.log d := by
      by_contra hh
      have hn := div_neg_of_neg_of_pos (lt_of_not_ge hh) h2
      linarith
    rw [max_eq_left hlog]
    have hf := Nat.floor_le hq
    have hc : ((⌊-Real.log d/Real.log 2⌋₊+1 : ℕ) : ℝ) ≤
        1+-Real.log d/Real.log 2 := by push_cast; linarith
    exact_mod_cast (ENNReal.ofReal_le_ofReal hc)
  · rw [dyadicProximity_negative_formula d hd (lt_of_not_ge hq)]
    exact bot_le

theorem logSingularity_le_dyadic (d : ℝ) (hd : 0 < d) :
    logSingularity d ≤ ENNReal.ofReal (Real.log 2)*(1+dyadicProximity d) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [logSingularity,if_neg (ne_of_gt hd)]
  by_cases hlog : 0 ≤ -Real.log d
  · rw [max_eq_left hlog,dyadicProximity_positive_formula d hd (div_nonneg hlog h2.le)]
    have hf := Nat.lt_floor_add_one (-Real.log d/Real.log 2)
    have hc : -Real.log d ≤ Real.log 2 *
        (1+((⌊-Real.log d/Real.log 2⌋₊+1 : ℕ) : ℝ)) := by
      have hh := (div_lt_iff₀ h2).mp hf
      push_cast at hh ⊢
      nlinarith
    calc
      _ ≤ ENNReal.ofReal (Real.log 2 *
          (1+((⌊-Real.log d/Real.log 2⌋₊+1 : ℕ) : ℝ))) := ENNReal.ofReal_le_ofReal hc
      _ = _ := by
        rw [ENNReal.ofReal_mul h2.le, ENNReal.ofReal_add (by norm_num) (by positivity)]
        rw [Nat.cast_add, Nat.cast_one, ENNReal.ofReal_add (by positivity) (by norm_num)]
        simp
  · rw [max_eq_right (le_of_not_ge hlog)]
    simp


theorem dyadicProximity_zero : dyadicProximity 0=⊤ := by
  unfold dyadicProximity
  simp only [ite_eq_left_iff,inv_nonneg,pow_nonneg (by norm_num : (0 : ℝ) ≤ 2),ite_true]
  exact ENNReal.tsum_const_eq_top_of_ne_zero (by norm_num)

theorem logSingularity_measurable : Measurable logSingularity := by
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  exact ENNReal.measurable_ofReal.comp ((Real.measurable_log.neg).max measurable_const)

theorem dyadicProximity_measurable : Measurable dyadicProximity := by
  exact Measurable.ennreal_tsum (fun j =>
    Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const measurable_const)

theorem dyadicProximity_le_logSingularity (d : ℝ) (hd : 0 ≤ d) :
    dyadicProximity d ≤ 1+ENNReal.ofReal (1/Real.log 2)*logSingularity d := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  by_cases hz : d=0
  · subst d
    have hc : ENNReal.ofReal (1/Real.log 2) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (div_pos (by norm_num) h2)
    rw [dyadicProximity_zero,show logSingularity 0=(⊤ : ℝ≥0∞) from by simp [logSingularity],ENNReal.mul_top hc]
    simp
  · have hdpos := lt_of_le_of_ne hd (Ne.symm hz)
    calc
      _ ≤ ENNReal.ofReal (1+max (-Real.log d) 0/Real.log 2) := dyadicProximity_upper d hdpos
      _ = _ := by
        rw [logSingularity,if_neg hz,ENNReal.ofReal_add (by norm_num) (by positivity)]
        rw [show max (-Real.log d) 0/Real.log 2=(1/Real.log 2)*max (-Real.log d) 0 by ring]
        rw [ENNReal.ofReal_mul (by positivity)]
        simp

theorem logSingularity_le_dyadicProximity (d : ℝ) (hd : 0 ≤ d) :
    logSingularity d ≤ ENNReal.ofReal (Real.log 2)*(1+dyadicProximity d) := by
  by_cases hz : d=0
  · subst d
    simp [dyadicProximity_zero,logSingularity,Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  · exact logSingularity_le_dyadic d (lt_of_le_of_ne hd (Ne.symm hz))

end
end SixVertex
