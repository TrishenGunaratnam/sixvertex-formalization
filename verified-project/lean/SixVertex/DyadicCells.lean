import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace SixVertex
noncomputable section
open MeasureTheory Set
open scoped ENNReal

abbrev PlaneCellIndex := ℤ × ℤ

def planeDyadicIndex (j : ℕ) (z : ℂ) : PlaneCellIndex :=
  (⌊(2 : ℝ)^j*z.re⌋,⌊(2 : ℝ)^j*z.im⌋)

def planeDyadicCell (j : ℕ) (k : PlaneCellIndex) : Set ℂ :=
  {z | planeDyadicIndex j z=k}

theorem planeDyadicIndex_measurable (j : ℕ) : Measurable (planeDyadicIndex j) := by
  exact ((measurable_const.mul Complex.measurable_re).floor).prodMk
    ((measurable_const.mul Complex.measurable_im).floor)

theorem planeDyadicCell_measurable (j : ℕ) (k : PlaneCellIndex) :
    MeasurableSet (planeDyadicCell j k) :=
  (planeDyadicIndex_measurable j) (measurableSet_singleton k)

theorem planeDyadicCell_disjoint (j : ℕ) : Pairwise (fun k t => Disjoint (planeDyadicCell j k) (planeDyadicCell j t)) := by
  intro k t hkt
  apply disjoint_left.mpr
  intro z hz ht
  exact hkt (hz.symm.trans ht)

theorem planeDyadicCell_union (j : ℕ) : (⋃ k, planeDyadicCell j k)=univ := by
  ext z
  simp only [mem_iUnion,mem_univ,iff_true]
  exact ⟨planeDyadicIndex j z,rfl⟩

theorem planeDyadicCell_distance (j : ℕ) (z w : ℂ)
    (h : planeDyadicIndex j z=planeDyadicIndex j w) :
    dist z w < 2*((2 : ℝ)^j)⁻¹ := by
  have hp : 0 < (2 : ℝ)^j := by positivity
  have hr := Int.abs_sub_lt_one_of_floor_eq_floor (congrArg Prod.fst h)
  have hi := Int.abs_sub_lt_one_of_floor_eq_floor (congrArg Prod.snd h)
  change |(2 : ℝ)^j*z.re-(2 : ℝ)^j*w.re| < 1 at hr
  change |(2 : ℝ)^j*z.im-(2 : ℝ)^j*w.im| < 1 at hi
  rw [← mul_sub,abs_mul,abs_of_pos hp] at hr hi
  have hnorm := Complex.norm_le_abs_re_add_abs_im (z-w)
  simp only [Complex.sub_re,Complex.sub_im] at hnorm
  rw [dist_eq_norm]
  apply (lt_div_iff₀ hp).mpr
  nlinarith

/-- Close points belong to one of nine neighboring dyadic squares.
The offsets include the boundary cases of the half-open cells. -/
theorem planeDyadicIndex_near (j : ℕ) (z w : ℂ)
    (h : dist z w ≤ ((2 : ℝ)^j)⁻¹) :
    |(planeDyadicIndex j z).1-(planeDyadicIndex j w).1| ≤ 1 ∧
    |(planeDyadicIndex j z).2-(planeDyadicIndex j w).2| ≤ 1 := by
  have hp : 0 < (2 : ℝ)^j := by positivity
  have hr : |z.re-w.re| ≤ ((2 : ℝ)^j)⁻¹ := by
    exact (Complex.abs_re_le_norm (z-w)).trans (by simpa only [dist_eq_norm] using h)
  have hi : |z.im-w.im| ≤ ((2 : ℝ)^j)⁻¹ := by
    exact (Complex.abs_im_le_norm (z-w)).trans (by simpa only [dist_eq_norm] using h)
  have hf : ∀ a b : ℝ, |a-b| ≤ ((2 : ℝ)^j)⁻¹ →
      |⌊(2 : ℝ)^j*a⌋-⌊(2 : ℝ)^j*b⌋| ≤ 1 := by
    intro a b hab
    have hs : |(2 : ℝ)^j*a-(2 : ℝ)^j*b| ≤ 1 := by
      rw [← mul_sub,abs_mul,abs_of_pos hp]
      have hx : |a-b| *(2 : ℝ)^j ≤ 1 := (le_div_iff₀ hp).mp (by simpa only [one_div] using hab)
      nlinarith
    have hfa := Int.floor_le ((2 : ℝ)^j*a)
    have hfb := Int.floor_le ((2 : ℝ)^j*b)
    have hga := Int.lt_floor_add_one ((2 : ℝ)^j*a)
    have hgb := Int.lt_floor_add_one ((2 : ℝ)^j*b)
    have ha : ((⌊(2 : ℝ)^j*a⌋-⌊(2 : ℝ)^j*b⌋ : ℤ) : ℝ) < 2 := by
      push_cast
      linarith [(abs_le.mp hs).2]
    have hb : (-2 : ℝ) < ((⌊(2 : ℝ)^j*a⌋-⌊(2 : ℝ)^j*b⌋ : ℤ) : ℝ) := by
      push_cast
      linarith [(abs_le.mp hs).1]
    have ha' : ⌊(2 : ℝ)^j*a⌋-⌊(2 : ℝ)^j*b⌋ < 2 := by exact_mod_cast ha
    have hb' : -2 < ⌊(2 : ℝ)^j*a⌋-⌊(2 : ℝ)^j*b⌋ := by exact_mod_cast hb
    exact abs_le.mpr ⟨by omega,by omega⟩
  exact ⟨hf _ _ hr,hf _ _ hi⟩

end
end SixVertex
