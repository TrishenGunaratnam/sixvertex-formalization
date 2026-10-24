import SixVertex.BetheLowering

namespace SixVertex

noncomputable def cActionWeight (t : ℂ) (b : ℕ → ℂ) (n : ℕ)
    (E : Finset ℂ) (v p q : ℂ) : ℂ :=
  vacuumA t b p n * vacuumL t b q n * betheBeta t (v-p) * betheBeta t (q-v) *
    betheF t (q-p) * ∏ x ∈ (E.erase p).erase q, betheF t (x-p) * betheF t (q-x)

theorem c_action_new_lower (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    (∑ p ∈ U, cActionWeight t b n (insert v U) v p v •
      betheState t ht b n (((insert v U).erase p).erase v)) =
      upperRemoval t ht v b n U := by
  classical
  unfold upperRemoval
  apply Finset.sum_congr rfl
  intro p hp
  have he : ((insert v U).erase p).erase v = U.erase p := by
    rw [Finset.erase_right_comm, Finset.erase_insert hv]
  unfold cActionWeight
  rw [he]
  simp only [sub_self, betheBeta_zero t ht, mul_one, Finset.prod_mul_distrib]
  congr 1
  have hh := betheBeta_mul_f t (v-p)
    (hreg.2 v (Finset.mem_insert_self _ _) p (Finset.mem_insert_of_mem hp))
  linear_combination (vacuumA t b p n * vacuumL t b v n *
    (∏ x ∈ U.erase p, betheF t (x-p)) * ∏ x ∈ U.erase p, betheF t (v-x)) * hh

theorem c_action_old_lower (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) (q : ℂ) (hq : q ∈ U) :
    (∑ p ∈ (insert v U).erase q, cActionWeight t b n (insert v U) v p q •
      betheState t ht b n (((insert v U).erase p).erase q)) =
      (vacuumL t b q n * betheG t (q-v) *
        ∏ x ∈ U.erase q, betheF t (q-x)) •
        (betheA t b n v * betheState t ht b n (U.erase q)) := by
  classical
  have hqv : q ≠ v := fun he => hv (he ▸ hq)
  have hvErase : v ∉ U.erase q := fun he => hv (Finset.mem_of_mem_erase he)
  have hE : (insert v U).erase q = insert v (U.erase q) :=
    Finset.erase_insert_of_ne hqv.symm
  rw [bethe_A_action t ht b n (U.erase q) v hvErase
    (hreg.mono (Finset.insert_subset_insert v (Finset.erase_subset q U)))]
  simp only [Finset.smul_sum, smul_smul]
  rw [← hE]
  apply Finset.sum_congr rfl
  intro p hp
  have hprod := Finset.mul_prod_erase ((insert v U).erase q)
    (fun x => betheF t (q-x)) hp
  rw [hE, Finset.prod_insert hvErase] at hprod
  have hh := betheBeta_mul_f t (q-v)
    (hreg.2 q (Finset.mem_insert_of_mem hq) v (Finset.mem_insert_self _ _))
  have hk : betheBeta t (q-v) * betheF t (q-p) *
      (∏ x ∈ ((insert v U).erase q).erase p, betheF t (q-x)) =
      betheG t (q-v) * ∏ x ∈ U.erase q, betheF t (q-x) := by
    rw [← hE] at hprod
    linear_combination (betheBeta t (q-v)) * hprod +
      (∏ x ∈ U.erase q, betheF t (q-x)) * hh
  unfold cActionWeight
  rw [Finset.erase_right_comm]
  simp only [Finset.prod_mul_distrib]
  congr 1
  linear_combination (vacuumA t b p n * vacuumL t b q n * betheBeta t (v-p) *
    ∏ x ∈ ((insert v U).erase q).erase p, betheF t (x-p)) * hk

/-- Reindexing the ordered removals changes the summation order only. -/
theorem ordered_erase_sum_comm {I R : Type*} [DecidableEq I] [AddCommMonoid R]
    (E : Finset I) (F : I → I → R) :
    (∑ p ∈ E, ∑ q ∈ E.erase p, F p q) =
      ∑ q ∈ E, ∑ p ∈ E.erase q, F p q := by
  have he : ∀ (p : I) (f : I → R), (∑ q ∈ E.erase p, f q) =
      ∑ q ∈ E, if q = p then 0 else f q := by
    intro p f
    rw [← Finset.sum_erase E (f := fun q => if q = p then 0 else f q) (a := p) (by simp)]
    apply Finset.sum_congr rfl
    intro q hq
    simp [(Finset.mem_erase.mp hq).1]
  simp_rw [he]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p = q
  · subst p
    simp
  · simp [h, Ne.symm h]

/-- The complete two-removal C formula, with the upper removal p first
and the lower removal q second, exactly as in the manuscript. -/
theorem bethe_C_action (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (U : Finset ℂ) (v : ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    betheC t b n v * betheState t ht b n U =
      ∑ p ∈ insert v U, ∑ q ∈ (insert v U).erase p,
        cActionWeight t b n (insert v U) v p q •
          betheState t ht b n (((insert v U).erase p).erase q) := by
  classical
  rw [ordered_erase_sum_comm, Finset.sum_insert hv, Finset.erase_insert hv,
    c_action_new_lower t v ht b n U hv hreg]
  have hsum :
      (∑ q ∈ U, ∑ p ∈ (insert v U).erase q,
        cActionWeight t b n (insert v U) v p q •
          betheState t ht b n (((insert v U).erase p).erase q)) =
      betheA t b n v * lowerWeightedRemoval t ht v b n U := by
    simp only [lowerWeightedRemoval, Finset.mul_sum, mul_smul_comm]
    apply Finset.sum_congr rfl
    intro q hq
    exact c_action_old_lower t v ht b n U hv hreg q hq
  rw [hsum]
  exact bethe_C_action_reduced t v ht b n U hv hreg

end SixVertex
