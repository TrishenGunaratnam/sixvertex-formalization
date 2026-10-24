import SixVertex.BetheActions

/-! An extra quantum site proves the C action from the already proved
A and L actions. All block calculations below are for actual finite-row
matrices, rather than an assumed abstract representation. -/
namespace SixVertex

noncomputable def extraInhom (t v : ℂ) (b : ℕ → ℂ) : ℕ → ℂ
  | 0 => v+t/2
  | j+1 => b j

noncomputable def extraUpper (t v x : ℂ) : ℂ := Complex.sinh (x-v) / Complex.sinh t
noncomputable def extraLower (t v x : ℂ) : ℂ := Complex.sinh (x-v-t) / Complex.sinh t

noncomputable def rowSlice {n : ℕ}
    (M : Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ) (i j : Fin 2) :
    Matrix (RowSpins n) (RowSpins n) ℂ := Matrix.of (fun q r => M (i,q) (j,r))

@[simp] theorem rowSlice_add {n : ℕ}
    (M N : Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ) (i j : Fin 2) :
    rowSlice (M+N) i j = rowSlice M i j + rowSlice N i j := rfl

@[simp] theorem rowSlice_smul {n : ℕ} (a : ℂ)
    (M : Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ) (i j : Fin 2) :
    rowSlice (a • M) i j = a • rowSlice M i j := rfl

@[simp] theorem rowSlice_zero {n : ℕ} (i j : Fin 2) :
    rowSlice (0 : Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ) i j = 0 := rfl

@[simp] theorem rowSlice_sum {n : ℕ} {I : Type*} (U : Finset I)
    (M : I → Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ) (i j : Fin 2) :
    rowSlice (∑ x ∈ U, M x) i j = ∑ x ∈ U, rowSlice (M x) i j := by
  ext q r
  simp only [rowSlice, Matrix.of_apply, Matrix.sum_apply]

theorem rowSlice_mul {n : ℕ}
    (M N : Matrix (RowSpins (n+1)) (RowSpins (n+1)) ℂ) (i j : Fin 2) :
    rowSlice (M*N) i j =
      rowSlice M i 0 * rowSlice N 0 j + rowSlice M i 1 * rowSlice N 1 j := by
  ext q r
  simp [rowSlice, Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two]

theorem rowSlice_betheBlock (t v : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ)
    (a c i j : Fin 2) :
    rowSlice (betheBlock t (extraInhom t v b) (n+1) x a c) i j =
      hyperbolicR t (x-v-t) (a,i) (0,j) • betheBlock t b n x 0 c +
      hyperbolicR t (x-v-t) (a,i) (1,j) • betheBlock t b n x 1 c := by
  ext q r
  simp only [rowSlice, Matrix.of_apply, betheBlock, rowBlock, Fin.sum_univ_two,
    Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, extraInhom]
  rw [show x-(v+t/2)-t/2 = x-v-t by ring]

theorem extra_B00 (t v : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) :
    rowSlice (betheB t (extraInhom t v b) (n+1) x) 0 0 =
      extraUpper t v x • betheB t b n x := by
  rw [betheB, rowSlice_betheBlock]
  simp [hyperbolicR, sixMatrix, extraUpper, show x-v-t+t = x-v by ring]

theorem extra_B01 (t v : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) :
    rowSlice (betheB t (extraInhom t v b) (n+1) x) 0 1 = 0 := by
  rw [betheB, rowSlice_betheBlock]
  simp [hyperbolicR, sixMatrix]

theorem extra_B10 (t v : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) :
    rowSlice (betheB t (extraInhom t v b) (n+1) x) 1 0 = betheL t b n x := by
  rw [betheB, rowSlice_betheBlock]
  simp [hyperbolicR, sixMatrix]

theorem extra_B11 (t v : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) :
    rowSlice (betheB t (extraInhom t v b) (n+1) x) 1 1 =
      extraLower t v x • betheB t b n x := by
  rw [betheB, rowSlice_betheBlock]
  simp [hyperbolicR, sixMatrix, extraLower]

theorem extra_A10 (t v : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    rowSlice (betheA t (extraInhom t v b) (n+1) v) 1 0 = betheC t b n v := by
  rw [betheA, rowSlice_betheBlock]
  simp [hyperbolicR, sixMatrix]

theorem extra_A11 (t v : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ) (n : ℕ) :
    rowSlice (betheA t (extraInhom t v b) (n+1) v) 1 1 = -betheA t b n v := by
  rw [betheA, rowSlice_betheBlock]
  simp [hyperbolicR, sixMatrix, Complex.sinh_neg, ht]

@[simp] theorem extra_vacuum00 (n : ℕ) :
    rowSlice (vacuumProjector (n+1)) 0 0 = vacuumProjector n := by
  ext q r
  simp [rowSlice, vacuumProjector, plusSpins]

@[simp] theorem extra_vacuum10 (n : ℕ) :
    rowSlice (vacuumProjector (n+1)) 1 0 = 0 := by
  ext q r
  simp [rowSlice, vacuumProjector, plusSpins]

theorem extra_vacuumA (t v x : ℂ) (b : ℕ → ℂ) (n : ℕ) :
    vacuumA t (extraInhom t v b) x (n+1) = extraUpper t v x * vacuumA t b x n := by
  simp only [vacuumA, extraInhom, extraUpper]
  rw [show x-(v+t/2)+t/2 = x-v by ring]

/-- The local scalar exchange identity used in the one-down-spin component. -/
theorem extra_scalar (t v u q : ℂ) (ht : Complex.sinh t ≠ 0)
    (hqu : Complex.sinh (q-u) ≠ 0) :
    extraUpper t v q * betheG t (q-u) + extraLower t v u =
      extraUpper t v u * betheF t (q-u) := by
  have h := sinh_determinant (u-v) (-t) (q-u)
  have e1 : -t+(u-v) = u-v-t := by ring
  have e2 : (q-u)+(u-v) = q-v := by ring
  have e3 : (q-u)-(-t) = q-u+t := by ring
  rw [e1, e2, e3, Complex.sinh_neg] at h
  unfold extraUpper extraLower betheG betheF
  field_simp [ht, hqu]
  linear_combination h

@[simp] theorem betheState_empty (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) : betheState t ht b n ∅ = vacuumProjector n := by
  simp [betheState]

theorem extra_state00 (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) :
    rowSlice (betheState t ht (extraInhom t v b) (n+1) U) 0 0 =
      (∏ x ∈ U, extraUpper t v x) • betheState t ht b n U := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert u U hu ih =>
    rw [← bethe_B_action t ht (extraInhom t v b) (n+1) U u hu,
      rowSlice_mul, extra_B00, extra_B01, zero_mul, add_zero, ih,
      Finset.prod_insert hu]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    rw [bethe_B_action t ht b n U u hu]
    congr 1
    exact mul_comm _ _

/-- The one-down-spin component of an off-shell state on the extra site. -/
theorem extra_state10 (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) (hreg : BetheRegular t U) :
    rowSlice (betheState t ht (extraInhom t v b) (n+1) U) 1 0 =
      ∑ p ∈ U, (vacuumL t b p n * (∏ x ∈ U.erase p, extraUpper t v x) *
        ∏ x ∈ U.erase p, betheF t (p-x)) • betheState t ht b n (U.erase p) := by
  classical
  induction U using Finset.induction_on with
  | empty => simp
  | @insert u U hu ih =>
    have hUreg := hreg.mono (Finset.subset_insert u U)
    rw [← bethe_B_action t ht (extraInhom t v b) (n+1) U u hu,
      rowSlice_mul, extra_B10, extra_B11, extra_state00, ih hUreg,
      mul_smul_comm, bethe_L_action_separated t ht b n U u hu hreg]
    simp only [smul_add, smul_smul, Finset.smul_sum, Finset.mul_sum,
      mul_smul_comm, smul_mul_assoc]
    rw [Finset.sum_insert hu, Finset.erase_insert hu]
    have hrhs :
        (∑ p ∈ U, (vacuumL t b p n *
          (∏ x ∈ (insert u U).erase p, extraUpper t v x) *
          ∏ x ∈ (insert u U).erase p, betheF t (p-x)) •
            betheState t ht b n ((insert u U).erase p)) =
        ∑ p ∈ U, (vacuumL t b p n *
          (extraUpper t v u * ∏ x ∈ U.erase p, extraUpper t v x) *
          (betheF t (p-u) * ∏ x ∈ U.erase p, betheF t (p-x))) •
            (betheB t b n u * betheState t ht b n (U.erase p)) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hpu : p ≠ u := fun he => hu (he ▸ hp)
      have huErase : u ∉ U.erase p := fun he => hu (Finset.mem_of_mem_erase he)
      rw [Finset.erase_insert_of_ne hpu.symm, Finset.prod_insert huErase,
        Finset.prod_insert huErase, ← bethe_B_action t ht b n (U.erase p) u huErase]
    rw [hrhs]
    have hsum :
        (∑ p ∈ U, ((∏ x ∈ U, extraUpper t v x) *
          (vacuumL t b p n * betheG t (p-u) * ∏ x ∈ U.erase p, betheF t (p-x))) •
          (betheB t b n u * betheState t ht b n (U.erase p))) +
        (∑ p ∈ U, (extraLower t v u *
          (vacuumL t b p n * (∏ x ∈ U.erase p, extraUpper t v x) *
          ∏ x ∈ U.erase p, betheF t (p-x))) •
          (betheB t b n u * betheState t ht b n (U.erase p))) =
        ∑ p ∈ U, (vacuumL t b p n *
          (extraUpper t v u * ∏ x ∈ U.erase p, extraUpper t v x) *
          (betheF t (p-u) * ∏ x ∈ U.erase p, betheF t (p-x))) •
          (betheB t b n u * betheState t ht b n (U.erase p)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro p hp
      rw [← add_smul]
      congr 1
      rw [← Finset.mul_prod_erase U (fun x => extraUpper t v x) hp]
      have hpu : p ≠ u := fun he => hu (he ▸ hp)
      have hh := extra_scalar t v u p ht
        (hreg.1 p (Finset.mem_insert_of_mem hp) u (Finset.mem_insert_self _ _) hpu)
      linear_combination (vacuumL t b p n *
        (∏ x ∈ U.erase p, extraUpper t v x) * ∏ x ∈ U.erase p, betheF t (p-x)) * hh
    rw [← hsum]
    have hmain : (∏ x ∈ U, extraUpper t v x) *
        (vacuumL t b u n * ∏ x ∈ U, betheF t (u-x)) =
        vacuumL t b u n * (∏ x ∈ U, extraUpper t v x) *
          ∏ x ∈ U, betheF t (u-x) := by ring
    rw [hmain]
    simp only [mul_comm, add_assoc]

/-- If the extra-site parameter itself is present, only its removal
survives in the one-down-spin component. -/
theorem extra_state10_insert (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    rowSlice (betheState t ht (extraInhom t v b) (n+1) (insert v U)) 1 0 =
      (vacuumL t b v n * (∏ x ∈ U, extraUpper t v x) *
        ∏ x ∈ U, betheF t (v-x)) • betheState t ht b n U := by
  classical
  rw [extra_state10 t v ht b n _ hreg, Finset.sum_insert hv, Finset.erase_insert hv]
  have hz : ∀ p ∈ U, (∏ x ∈ (insert v U).erase p, extraUpper t v x) = 0 := by
    intro p hp
    have hpv : v ≠ p := fun he => hv (he ▸ hp)
    exact Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hpv, Finset.mem_insert_self _ _⟩)
      (by simp [extraUpper])
  have hs : (∑ p ∈ U, (vacuumL t b p n *
      (∏ x ∈ (insert v U).erase p, extraUpper t v x) *
      ∏ x ∈ (insert v U).erase p, betheF t (p-x)) •
      betheState t ht b n ((insert v U).erase p)) = 0 := by
    apply Finset.sum_eq_zero
    intro p hp
    rw [hz p hp]
    simp
  rw [hs, add_zero]

noncomputable def lowerWeightedRemoval (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (v : ℂ) (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) :
    Matrix (RowSpins n) (RowSpins n) ℂ :=
  ∑ p ∈ U, (vacuumL t b p n * betheG t (p-v) *
    ∏ x ∈ U.erase p, betheF t (p-x)) • betheState t ht b n (U.erase p)

theorem extra_upper_mul_g (t v p : ℂ) (ht : Complex.sinh t ≠ 0)
    (hpv : Complex.sinh (p-v) ≠ 0) :
    extraUpper t v p * betheG t (p-v) = 1 := by
  unfold extraUpper betheG
  field_simp

/-- Extract the common extra-site product without dividing any vacuum value. -/
theorem extra_state10_normalized (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) (hv : v ∉ U)
    (hreg : BetheRegular t (insert v U)) :
    rowSlice (betheState t ht (extraInhom t v b) (n+1) U) 1 0 =
      (∏ x ∈ U, extraUpper t v x) • lowerWeightedRemoval t ht v b n U := by
  classical
  rw [extra_state10 t v ht b n U (hreg.mono (Finset.subset_insert v U))]
  simp only [lowerWeightedRemoval, Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro p hp
  have hpv : p ≠ v := fun he => hv (he ▸ hp)
  have hh := extra_upper_mul_g t v p ht
    (hreg.1 p (Finset.mem_insert_of_mem hp) v (Finset.mem_insert_self _ _) hpv)
  rw [← Finset.mul_prod_erase U (fun x => extraUpper t v x) hp]
  congr 1
  linear_combination -(vacuumL t b p n * (∏ x ∈ U.erase p, extraUpper t v x) *
    ∏ x ∈ U.erase p, betheF t (p-x)) * hh

theorem extra_product_ne_zero (t v : ℂ) (ht : Complex.sinh t ≠ 0)
    (U : Finset ℂ) (hv : v ∉ U) (hreg : BetheRegular t (insert v U)) :
    (∏ x ∈ U, extraUpper t v x) ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  have hpv : p ≠ v := fun he => hv (he ▸ hp)
  exact div_ne_zero (hreg.1 p (Finset.mem_insert_of_mem hp) v
    (Finset.mem_insert_self _ _) hpv) ht

end SixVertex
