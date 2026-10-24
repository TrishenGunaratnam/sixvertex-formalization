import SixVertex.CountingSawtooth
import Mathlib.Data.Finset.Max

namespace SixVertex
noncomputable section
open Set

def rootsInInterval {n : ℕ} (Y : Fin n → ℝ) (a b : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => a ≤ Y j ∧ Y j ≤ b)

/-- A local counting estimate from the actual consecutive levels.
Unlike the global half-filled sawtooth, it applies at every filling. -/
theorem consecutive_levels_interval_count {n : ℕ} (Y : Fin n → ℝ) (xi : ℝ → ℝ)
    (hxi : Monotone xi) (c : ℝ) (hlevels : ∀ j : Fin n, xi (Y j)=(j.val : ℝ)+c)
    (a b : ℝ) (hab : a ≤ b) :
    ((rootsInInterval Y a b).card : ℝ) ≤ xi b-xi a+1 := by
  classical
  let s := rootsInInterval Y a b
  by_cases hs : s.Nonempty
  · let i := s.min' hs
    let j := s.max' hs
    have hi : i ∈ s := Finset.min'_mem s hs
    have hj : j ∈ s := Finset.max'_mem s hs
    have hij : i ≤ j := Finset.min'_le_max' s hs
    have hsub : s ⊆ Finset.Icc i j := by
      intro k hk
      exact Finset.mem_Icc.mpr ⟨Finset.min'_le s k hk,Finset.le_max' s k hk⟩
    have hcard := Finset.card_le_card hsub
    rw [Fin.card_Icc] at hcard
    have hreal : (s.card : ℝ) ≤ (j.val : ℝ)+1-(i.val : ℝ) := by
      have hnat : i.val ≤ j.val+1 := by have hh : i.val ≤ j.val := hij; omega
      have hh : (s.card : ℝ) ≤ ((j.val+1-i.val : ℕ) : ℝ) := by exact_mod_cast hcard
      simpa only [Nat.cast_sub hnat,Nat.cast_add,Nat.cast_one] using hh
    have hai : a ≤ Y i := (Finset.mem_filter.mp hi).2.1
    have hjb : Y j ≤ b := (Finset.mem_filter.mp hj).2.2
    have hleft := hxi hai
    have hright := hxi hjb
    rw [hlevels i] at hleft
    rw [hlevels j] at hright
    linarith
  · have he : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    change (s.card : ℝ) ≤ _
    rw [he,Finset.card_empty,Nat.cast_zero]
    linarith [hxi hab]

theorem consecutive_roots_interval_count {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0) (a z : ℝ) (haz : a ≤ z) :
    ((rootsInInterval Y a z).card : ℝ) ≤ countingXi lam b L Y z-countingXi lam b L Y a+1 := by
  apply consecutive_levels_interval_count Y (countingXi lam b L Y)
    (countingXi_strictMono_nonpositiveK lam b L hL Y hhalf hpi).monotone (1/2-(n : ℝ)/2) _ a z haz
  intro j
  have hh : countingXi lam b L Y (Y j)=countingTarget n 0 j := congrFun hroots.2 j
  rw [hh]
  unfold countingTarget
  simp only [zero_div]
  ring

end
end SixVertex
