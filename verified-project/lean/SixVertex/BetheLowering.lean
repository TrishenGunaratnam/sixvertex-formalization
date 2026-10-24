import SixVertex.BetheExtraSite

namespace SixVertex

noncomputable def upperRemoval (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (v : ℂ) (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) :
    Matrix (RowSpins n) (RowSpins n) ℂ :=
  ∑ p ∈ U, (vacuumA t b p n * vacuumL t b v n * betheG t (v-p) *
    (∏ x ∈ U.erase p, betheF t (x-p)) *
    ∏ x ∈ U.erase p, betheF t (v-x)) • betheState t ht b n (U.erase p)

/-- The right hand side of the extended-chain A action, on the extra
spin's off-diagonal block. -/
theorem extra_A_action_rhs (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    rowSlice (∑ p ∈ insert v U,
      (vacuumA t (extraInhom t v b) p (n+1) * betheBeta t (v-p) *
        ∏ x ∈ (insert v U).erase p, betheF t (x-p)) •
      betheState t ht (extraInhom t v b) (n+1) ((insert v U).erase p)) 1 0 =
      (∏ x ∈ U, extraUpper t v x) • upperRemoval t ht v b n U := by
  classical
  rw [rowSlice_sum, Finset.sum_insert hv]
  simp only [rowSlice_smul (n := n), extra_vacuumA]
  simp only [extraUpper, sub_self, Complex.sinh_zero, zero_div, zero_mul,
    zero_smul, zero_add]
  -- Restore the upper-weight notation only in the remaining terms.
  change (∑ p ∈ U,
    (extraUpper t v p * vacuumA t b p n * betheBeta t (v-p) *
      ∏ x ∈ (insert v U).erase p, betheF t (x-p)) •
      rowSlice (betheState t ht (extraInhom t v b) (n+1) ((insert v U).erase p)) 1 0) =
      (∏ x ∈ U, extraUpper t v x) • upperRemoval t ht v b n U
  simp only [upperRemoval, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpv : p ≠ v := fun he => hv (he ▸ hp)
  have hvErase : v ∉ U.erase p := fun he => hv (Finset.mem_of_mem_erase he)
  rw [Finset.erase_insert_of_ne hpv.symm, Finset.prod_insert hvErase,
    extra_state10_insert t v ht b n (U.erase p) hvErase
      (hreg.mono (Finset.insert_subset_insert v (Finset.erase_subset p U))), smul_smul]
  rw [← Finset.mul_prod_erase U (fun x => extraUpper t v x) hp]
  congr 1
  have hh := betheBeta_mul_f t (v-p)
    (hreg.2 v (Finset.mem_insert_self _ _) p (Finset.mem_insert_of_mem hp))
  linear_combination (extraUpper t v p * vacuumA t b p n * vacuumL t b v n *
    (∏ x ∈ U.erase p, extraUpper t v x) *
    (∏ x ∈ U.erase p, betheF t (x-p)) * ∏ x ∈ U.erase p, betheF t (v-x)) * hh

/-- Reduction of the lowering-entry action to the two diagonal formulas.
This follows from an actual extra-site matrix block, without assuming a
C-action formula or dividing by a(p) or l(q). -/
theorem bethe_C_action_reduced (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    betheC t b n v * betheState t ht b n U =
      upperRemoval t ht v b n U + betheA t b n v * lowerWeightedRemoval t ht v b n U := by
  classical
  have hA := congrArg (fun M => rowSlice M 1 0)
    (bethe_A_action t ht (extraInhom t v b) (n+1) U v hv hreg)
  rw [rowSlice_mul, extra_A10, extra_A11 t v ht, extra_state00,
    extra_state10_normalized t v ht b n U hv hreg,
    extra_A_action_rhs t v ht b n U hv hreg] at hA
  have heq : (∏ x ∈ U, extraUpper t v x) •
      (betheC t b n v * betheState t ht b n U -
        betheA t b n v * lowerWeightedRemoval t ht v b n U) =
      (∏ x ∈ U, extraUpper t v x) • upperRemoval t ht v b n U := by
    simpa only [mul_smul_comm, neg_mul, sub_eq_add_neg, smul_add, smul_neg] using hA
  have hcancel : betheC t b n v * betheState t ht b n U -
      betheA t b n v * lowerWeightedRemoval t ht v b n U =
      upperRemoval t ht v b n U := by
    ext q r
    have hh := congrArg (fun M : Matrix (RowSpins n) (RowSpins n) ℂ => M q r) heq
    simp only [Matrix.smul_apply, smul_eq_mul] at hh
    exact mul_left_cancel₀ (extra_product_ne_zero t v ht U hv hreg) hh
  exact sub_eq_iff_eq_add.mp hcancel

end SixVertex
