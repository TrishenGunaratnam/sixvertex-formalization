import SixVertex.BetheVacuum
import SixVertex.BetheProducts

namespace SixVertex

/-- Off-shell Bethe state as a matrix with only its vacuum column nonzero.
Evaluating that column yields the usual vector in the row spin space. -/
noncomputable def betheState (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (U : Finset ℂ) : Matrix (RowSpins n) (RowSpins n) ℂ :=
  creationProduct (betheB t b n) (bethe_BB t ht b n) U * vacuumProjector n

theorem bethe_B_action (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (U : Finset ℂ) (v : ℂ) (hv : v ∉ U) :
    betheB t b n v * betheState t ht b n U = betheState t ht b n (insert v U) := by
  classical
  simp only [betheState, creationProduct_insert _ _ _ _ hv, mul_assoc]

theorem bethe_A_action (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (U : Finset ℂ) (v : ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    betheA t b n v * betheState t ht b n U =
      ∑ p ∈ insert v U,
        (vacuumA t b p n * betheBeta t (v-p) *
          ∏ u ∈ (insert v U).erase p, betheF t (u-p)) •
        betheState t ht b n ((insert v U).erase p) := by
  classical
  let S := insert v U
  have hN := diagonal_normal_order (fun p u => betheF t (u-p))
    (fun p u => betheG t (p-u)) (betheA t b n) (betheB t b n)
    (bethe_BB t ht b n) S
    (fun p hp u hu hn => bethe_AB t ht b n p u (hreg.1 p hp u hu hn))
    (fun p hp u hu k hk hpu hpk huk =>
      bethe_diagonal_cocycle t p u k
        (hreg.1 p hp u hu hpu) (hreg.1 p hp k hk hpk) (hreg.1 u hu k hk huk))
    U (Finset.subset_insert v U) v (Finset.mem_insert_self _ _) hv
  exact diagonal_action (fun p u => betheF t (u-p)) (fun p u => betheG t (p-u))
    (fun p u => betheBeta t (p-u)) (betheA t b n) (betheB t b n)
    (bethe_BB t ht b n) (fun p => vacuumA t b p n) (vacuumProjector n) U v hv hN
    (fun p _ => bethe_A_vacuum t b n p)
    (by simpa using betheBeta_zero t ht)
    (fun p hp => betheBeta_mul_f t (v-p)
      (hreg.2 v (Finset.mem_insert_self _ _) p (Finset.mem_insert_of_mem hp)))

theorem bethe_L_action (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (U : Finset ℂ) (v : ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    betheL t b n v * betheState t ht b n U =
      ∑ p ∈ insert v U,
        (vacuumL t b p n * betheBeta t (p-v) *
          ∏ u ∈ (insert v U).erase p, betheF t (p-u)) •
        betheState t ht b n ((insert v U).erase p) := by
  classical
  let S := insert v U
  have hN := diagonal_normal_order (fun p u => betheF t (p-u))
    (fun p u => betheG t (u-p)) (betheL t b n) (betheB t b n)
    (bethe_BB t ht b n) S
    (fun p hp u hu hn => bethe_LB t ht b n p u (hreg.1 p hp u hu hn))
    (fun p hp u hu k hk hpu hpk huk =>
      bethe_lower_cocycle t p u k
        (hreg.1 u hu p hp hpu.symm) (hreg.1 k hk p hp hpk.symm)
        (hreg.1 k hk u hu huk.symm))
    U (Finset.subset_insert v U) v (Finset.mem_insert_self _ _) hv
  exact diagonal_action (fun p u => betheF t (p-u)) (fun p u => betheG t (u-p))
    (fun p u => betheBeta t (u-p)) (betheL t b n) (betheB t b n)
    (bethe_BB t ht b n) (fun p => vacuumL t b p n) (vacuumProjector n) U v hv hN
    (fun p _ => bethe_L_vacuum t b n p)
    (by simpa using betheBeta_zero t ht)
    (fun p hp => betheBeta_mul_f t (p-v)
      (hreg.2 p (Finset.mem_insert_of_mem hp) v (Finset.mem_insert_self _ _)))

/-- The L action with the unchanged term separated, for the extra-site proof. -/
theorem bethe_L_action_separated (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (U : Finset ℂ) (v : ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    betheL t b n v * betheState t ht b n U =
      (vacuumL t b v n * ∏ u ∈ U, betheF t (v-u)) • betheState t ht b n U +
      ∑ p ∈ U, (vacuumL t b p n * betheG t (p-v) *
        ∏ u ∈ U.erase p, betheF t (p-u)) •
        (betheB t b n v * betheState t ht b n (U.erase p)) := by
  classical
  rw [bethe_L_action t ht b n U v hv hreg, Finset.sum_insert hv, Finset.erase_insert hv]
  simp only [sub_self, betheBeta_zero t ht, mul_one]
  congr 1
  apply Finset.sum_congr rfl
  intro p hp
  have hpv : p ≠ v := fun he => hv (he ▸ hp)
  have hvErase : v ∉ U.erase p := fun he => hv (Finset.mem_of_mem_erase he)
  rw [Finset.erase_insert_of_ne hpv.symm, Finset.prod_insert hvErase,
    ← bethe_B_action t ht b n (U.erase p) v hvErase]
  congr 1
  have hh := betheBeta_mul_f t (p-v)
    (hreg.2 p (Finset.mem_insert_of_mem hp) v (Finset.mem_insert_self _ _))
  linear_combination (vacuumL t b p n * ∏ u ∈ U.erase p, betheF t (p-u)) * hh

end SixVertex
