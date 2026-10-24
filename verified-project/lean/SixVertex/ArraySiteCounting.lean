import SixVertex.LocalCountingWindow

namespace SixVertex
noncomputable section
open Set

def arraySite (L : ℕ) (d : ℝ) (j : ℕ) : ℝ :=
  ((j : ℝ)-((L : ℝ)-1)/2)*(d/2)

/-- An actual equally spaced site array has at least order1/d sites
in every unit-radius window within its finite counting range. -/
theorem arraySite_unit_window_count (L : ℕ) (d : ℝ) (hd : 0 < d) (hd1 : d ≤ 1)
    (u : ℝ) (hspan : |u|+1 ≤ (L : ℝ)*d/4) :
    1/d ≤ (rootCountLe (fun j : Fin L => arraySite L d j.val) (u+1) : ℝ)-
      (rootCountLe (fun j : Fin L => arraySite L d j.val) (u-1) : ℝ) := by
  let Y : Fin L → ℝ := fun j => arraySite L d j.val
  let xi : ℝ → ℝ := fun x => 2*x/d
  have hY : Monotone Y := by
    intro i j hij
    dsimp [Y,arraySite]
    exact mul_le_mul_of_nonneg_right (sub_le_sub_right (Nat.cast_le.mpr hij) _) (div_pos hd (by norm_num)).le
  have hxi : Monotone xi := by
    intro x y hxy
    exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hxy (by norm_num)) hd.le
  have hlev (j : Fin L) : xi (Y j)=(j.val : ℝ)+1/2-(L : ℝ)/2 := by
    dsimp [xi,Y,arraySite]
    field_simp [hd.ne'] <;> ring
  have hwindow (x : ℝ) (hx : |x-u| ≤ 1) : -(L : ℝ)/2 ≤ xi x ∧ xi x ≤ (L : ℝ)/2 := by
    have hxb := abs_le.mp hx
    have hu1 := le_abs_self u
    have hu2 := neg_abs_le u
    constructor
    · apply (le_div_iff₀ hd).mpr
      nlinarith
    · apply (div_le_iff₀ hd).mpr
      nlinarith
  have ha := hwindow (u-1) (by rw [show u-1-u=-(1 : ℝ) by ring]; norm_num)
  have hz := hwindow (u+1) (by rw [add_sub_cancel_left]; norm_num)
  have hca := abs_le.mp (ordered_count_sawtooth_local Y hY xi hxi hlev (u-1) ha.1 ha.2)
  have hcz := abs_le.mp (ordered_count_sawtooth_local Y hY xi hxi hlev (u+1) hz.1 hz.2)
  have hslope : xi (u+1)-xi (u-1)=4/d := by dsimp [xi]; ring
  have hdiff : 4/d-1 ≤ (rootCountLe Y (u+1) : ℝ)-(rootCountLe Y (u-1) : ℝ) := by linarith
  have hlo : 1/d ≤ 4/d-1 := by
    calc
      _ ≤ (4-d)/d := div_le_div_of_nonneg_right (by linarith) hd.le
      _ = _ := by field_simp [hd.ne']
  exact hlo.trans hdiff

end
end SixVertex
