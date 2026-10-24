import SixVertex.SingleEntryActions

namespace SixVertex

noncomputable def twistedStandardRow (t : ℂ) (b : ℕ → ℂ) (L : ℕ)
    (twist : ℝ) (x : ℂ) : Matrix (RowSpins L) (RowSpins L) ℂ :=
  Complex.exp (Complex.I*twist) • betheA t b L x +
    Complex.exp (-Complex.I*twist) • betheL t b L x

noncomputable def abaEigenvalue (t : ℂ) (b : ℕ → ℂ) (L : ℕ)
    (twist : ℝ) (U : Finset ℂ) (x : ℂ) : ℂ :=
  Complex.exp (Complex.I*twist) * vacuumA t b x L * (∏ p ∈ U, betheF t (p-x)) +
    Complex.exp (-Complex.I*twist) * vacuumL t b x L * ∏ p ∈ U, betheF t (x-p)

def BalancedRoots (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (twist : ℝ) (U : Finset ℂ) : Prop :=
  ∀ p ∈ U, Complex.exp (Complex.I*twist) * vacuumA t b p L *
      (∏ u ∈ U.erase p, betheF t (u-p)) =
    Complex.exp (-Complex.I*twist) * vacuumL t b p L * ∏ u ∈ U.erase p, betheF t (p-u)

theorem bethe_A_action_separated (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (U : Finset ℂ) (v : ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    betheA t b n v * betheState t ht b n U =
      (vacuumA t b v n * ∏ u ∈ U, betheF t (u-v)) • betheState t ht b n U +
      ∑ p ∈ U, (vacuumA t b p n * betheG t (v-p) *
        ∏ u ∈ U.erase p, betheF t (u-p)) •
        (betheB t b n v * betheState t ht b n (U.erase p)) := by
  classical
  rw [bethe_A_action t ht b n U v hv hreg, Finset.sum_insert hv, Finset.erase_insert hv]
  simp only [sub_self, betheBeta_zero t ht, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpv : p ≠ v := fun he => hv (he ▸ hp)
  have hvErase : v ∉ U.erase p := fun he => hv (Finset.mem_of_mem_erase he)
  rw [Finset.erase_insert_of_ne hpv.symm, Finset.prod_insert hvErase,
    ← bethe_B_action t ht b n (U.erase p) v hvErase]
  congr 1
  have hh := betheBeta_mul_f t (v-p)
    (hreg.2 v (Finset.mem_insert_self _ _) p (Finset.mem_insert_of_mem hp))
  linear_combination (vacuumA t b p n * ∏ u ∈ U.erase p, betheF t (u-p)) * hh

/-- All unwanted root replacements cancel under the on-shell balance equations. -/
theorem balancedRoots_eigenvector (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (L : ℕ) (twist : ℝ) (U : Finset ℂ)
    (hU : BalancedRoots t b L twist U) (x : ℂ) (hx : x ∉ U)
    (hreg : BetheRegular t (insert x U)) :
    twistedStandardRow t b L twist x * betheState t ht b L U =
      abaEigenvalue t b L twist U x • betheState t ht b L U := by
  classical
  rw [twistedStandardRow, add_mul, smul_mul_assoc, smul_mul_assoc,
    bethe_A_action_separated t ht b L U x hx hreg,
    bethe_L_action_separated t ht b L U x hx hreg]
  simp only [smul_add, Finset.smul_sum, smul_smul]
  have hz : (∑ p ∈ U,
      (Complex.exp (Complex.I*twist) *
        (vacuumA t b p L * betheG t (x-p) * ∏ u ∈ U.erase p, betheF t (u-p))) •
        (betheB t b L x * betheState t ht b L (U.erase p))) +
      (∑ p ∈ U, (Complex.exp (-Complex.I*twist) *
        (vacuumL t b p L * betheG t (p-x) * ∏ u ∈ U.erase p, betheF t (p-u))) •
        (betheB t b L x * betheState t ht b L (U.erase p))) = 0 := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p hp
    rw [← add_smul]
    have hn : betheG t (p-x) = -betheG t (x-p) := by
      rw [show p-x = -(x-p) by ring, betheG_neg]
    rw [hn]
    have hc : Complex.exp (Complex.I*twist) *
        (vacuumA t b p L * betheG t (x-p) * ∏ u ∈ U.erase p, betheF t (u-p)) +
        Complex.exp (-Complex.I*twist) *
        (vacuumL t b p L * -betheG t (x-p) * ∏ u ∈ U.erase p, betheF t (p-u)) = 0 := by
      linear_combination (betheG t (x-p)) * hU p hp
    rw [hc, zero_smul]
  calc
    _ = (Complex.exp (Complex.I*twist) * (vacuumA t b x L * ∏ u ∈ U, betheF t (u-x))) •
        betheState t ht b L U +
        (Complex.exp (-Complex.I*twist) * (vacuumL t b x L * ∏ u ∈ U, betheF t (x-u))) •
        betheState t ht b L U := by rw [← add_add_add_comm, hz, add_zero]
    _ = _ := by rw [← add_smul]; congr 1; unfold abaEigenvalue; ring

end SixVertex
