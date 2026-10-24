import SixVertex.PhaseAsymptotics

namespace SixVertex
open Filter Topology

/-- Internal interactions cancel exactly when summing an escaping cluster. -/
theorem antisymmetric_finset_sum_zero {I : Type*} (H : Finset I) (f : I → I → ℝ)
    (hf : ∀ i j, f i j = -f j i) : (∑ i ∈ H, ∑ j ∈ H, f i j) = 0 := by
  have he : (∑ i ∈ H, ∑ j ∈ H, f i j) = -(∑ i ∈ H, ∑ j ∈ H, f i j) := by
    calc
      _ = ∑ j ∈ H, ∑ i ∈ H, f i j := Finset.sum_comm
      _ = ∑ j ∈ H, ∑ i ∈ H, -f j i := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Finset.sum_congr rfl (fun i hi => hf i j)
      _ = _ := by simp only [Finset.sum_neg_distrib]
  linarith

noncomputable def countingOrderSign {n : ℕ} (i j : Fin n) : ℝ :=
  if j < i then 1 else if i < j then -1 else 0

theorem countingOrderSign_antisymm {n : ℕ} (i j : Fin n) :
    countingOrderSign i j = -countingOrderSign j i := by
  rcases lt_trichotomy i j with h | rfl | h
  · simp [countingOrderSign,h,not_lt_of_ge (le_of_lt h)]
  · simp [countingOrderSign]
  · simp [countingOrderSign,h,not_lt_of_ge (le_of_lt h)]

theorem countingOrderSign_le_one {n : ℕ} (i j : Fin n) : countingOrderSign i j ≤ 1 := by
  unfold countingOrderSign
  split_ifs <;> norm_num

theorem countingOrderSign_sum (n : ℕ) (i : Fin n) :
    (∑ j, countingOrderSign i j) = 2*(i.val : ℝ)+1-n := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · have hz : countingOrderSign (0 : Fin (n+1)) 0 = 0 := by simp [countingOrderSign]
      have hs (j : Fin n) : countingOrderSign (0 : Fin (n+1)) j.succ = -1 := by simp [countingOrderSign]
      rw [Fin.sum_univ_succ,hz]
      simp_rw [hs]
      simp
    · have hz : countingOrderSign i.succ (0 : Fin (n+1)) = 1 := by simp [countingOrderSign]
      have hs (j : Fin n) : countingOrderSign i.succ j.succ = countingOrderSign i j := by simp [countingOrderSign]
      rw [Fin.sum_univ_succ,hz]
      simp_rw [hs]
      rw [ih i]
      simp only [Fin.val_succ,Nat.cast_add,Nat.cast_one]
      ring

theorem countingTarget_orderSign (n : ℕ) (i : Fin n) :
    countingTarget n 0 i = (∑ j, countingOrderSign i j)/2 := by
  rw [countingOrderSign_sum]
  unfold countingTarget
  ring

/-- The sum of ANY k consecutive counting levels is bounded by the sum
of the largest k levels. This proof uses pair cancellation, not a sorting axiom. -/
theorem countingTarget_cluster_bound (n : ℕ) (H : Finset (Fin n)) :
    (∑ i ∈ H, countingTarget n 0 i) ≤ (H.card : ℝ)*(n-H.card)/2 := by
  classical
  let C := Finset.univ \ H
  have hcard : C.card = n-H.card := by simp [C,Finset.card_sdiff]
  have hle : H.card ≤ n := by simpa using H.card_le_univ
  have hsplit (i : Fin n) : (∑ j, countingOrderSign i j) =
      (∑ j ∈ H, countingOrderSign i j)+(∑ j ∈ C, countingOrderSign i j) := by
    simpa only [Finset.univ_inter,C] using
      (Finset.sum_inter_add_sum_sdiff Finset.univ H (countingOrderSign i)).symm
  have hinternal := antisymmetric_finset_sum_zero H countingOrderSign countingOrderSign_antisymm
  have hsum : (∑ i ∈ H, countingTarget n 0 i) = (∑ i ∈ H, ∑ j ∈ C, countingOrderSign i j)/2 := by
    simp only [countingTarget_orderSign,div_eq_mul_inv]
    rw [← Finset.sum_mul]
    simp_rw [hsplit]
    rw [Finset.sum_add_distrib,hinternal,zero_add]
  have hcross : (∑ i ∈ H, ∑ j ∈ C, countingOrderSign i j) ≤ (H.card : ℝ)*C.card := by
    calc
      _ ≤ ∑ i ∈ H, ∑ j ∈ C, (1 : ℝ) := by
        exact Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => countingOrderSign_le_one i j))
      _ = _ := by simp
  rw [hcard,Nat.cast_sub hle] at hcross
  rw [hsum]
  linarith

theorem countingSystem_cluster_sum {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (H : Finset (Fin n)) :
    (∑ i ∈ H, countingSystem lam b L Y i) =
      (∑ i ∈ H, ∑ a ∈ Finset.range L, countingS lam (Y i-b a)) -
      ∑ i ∈ H, ∑ j ∈ Finset.univ \ H, countingTheta lam (Y i-Y j) := by
  classical
  have hanti (i j : Fin n) : countingTheta lam (Y i-Y j) = -countingTheta lam (Y j-Y i) := by
    rw [show Y i-Y j = -(Y j-Y i) by ring]
    exact barePhase_neg lam _
  have hz := antisymmetric_finset_sum_zero H _ hanti
  have hsplit (i : Fin n) : (∑ j, countingTheta lam (Y i-Y j)) =
      (∑ j ∈ H, countingTheta lam (Y i-Y j)) +
      (∑ j ∈ Finset.univ \ H, countingTheta lam (Y i-Y j)) := by
    simpa only [Finset.univ_inter] using
      (Finset.sum_inter_add_sum_sdiff Finset.univ H (fun j => countingTheta lam (Y i-Y j))).symm
  simp only [countingSystem,countingXi,hsplit,Finset.sum_sub_distrib,Finset.sum_add_distrib,hz,zero_add]

theorem counting_cluster_atTop {A : Type*} (l : Filter A) (n : ℕ) (lam : A → ℝ) (lam0 : ℝ)
    (b : ℕ → ℝ) (L : ℕ) (Y : A → Fin n → ℝ) (H : Finset (Fin n))
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam l (𝓝 lam0))
    (hY : ∀ i ∈ H, Tendsto (fun a => Y a i) l atTop)
    (hcross : ∀ i ∈ H, ∀ j ∈ Finset.univ \ H, Tendsto (fun a => Y a i-Y a j) l atTop) :
    Tendsto (fun a => ∑ i ∈ H, countingSystem (lam a) b L (Y a) i) l
      (𝓝 ((H.card : ℝ)*((L : ℝ)*phaseEnd (lam0/2)-(n-H.card)*phaseEnd lam0))) := by
  have hshift (i : Fin n) (hi : i ∈ H) (j : ℕ) : Tendsto (fun a => Y a i-b j) l atTop := by
    apply tendsto_atTop.mpr
    intro c
    filter_upwards [(hY i hi).eventually (eventually_ge_atTop (c+b j))] with a ha
    linarith
  have hs := tendsto_finsetSum H (fun i hi => tendsto_finsetSum (Finset.range L) (fun j hj =>
    countingS_tendsto_atTop l lam _ lam0 h0 hpi hLam (hshift i hi j)))
  have hk := tendsto_finsetSum H (fun i hi => tendsto_finsetSum (Finset.univ \ H) (fun j hj =>
    countingTheta_tendsto_atTop l lam _ lam0 h0 hpi hLam (hcross i hi j hj)))
  have ht := hs.sub hk
  have hle : H.card ≤ n := by simpa using H.card_le_univ
  have he : (∑ i ∈ H, ∑ j ∈ Finset.range L, phaseEnd (lam0/2)) -
      (∑ i ∈ H, ∑ j ∈ Finset.univ \ H, phaseEnd lam0) =
      (H.card : ℝ)*((L : ℝ)*phaseEnd (lam0/2)-(n-H.card)*phaseEnd lam0) := by
    simp only [Finset.sum_const,Finset.card_range,Finset.card_sdiff,Finset.subset_univ,
      Finset.card_univ,Fintype.card_fin,Finset.inter_univ,Nat.cast_sub hle,nsmul_eq_mul]
    ring
  rw [he] at ht
  exact ht.congr (fun a => (countingSystem_cluster_sum (lam a) b L (Y a) H).symm)

/-- No nonempty separated cluster of consecutive half-filled roots can
escape to +infinity while lambda stays at an interior physical value. -/
theorem no_upper_escaping_cluster {A : Type*} (l : Filter A) [l.NeBot] (n : ℕ)
    (lam : A → ℝ) (lam0 : ℝ) (b : ℕ → ℝ) (L : ℕ) (hfill : 2*n ≤ L)
    (Y : A → Fin n → ℝ) (H : Finset (Fin n)) (hH : H.Nonempty)
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam l (𝓝 lam0))
    (hY : ∀ i ∈ H, Tendsto (fun a => Y a i) l atTop)
    (hcross : ∀ i ∈ H, ∀ j ∈ Finset.univ \ H, Tendsto (fun a => Y a i-Y a j) l atTop)
    (hsolutions : ∀ᶠ a in l, countingSystem (lam a) b L (Y a) = countingTarget n 0) : False := by
  have ht := counting_cluster_atTop l n lam lam0 b L Y H h0 hpi hLam hY hcross
  have hc : Tendsto (fun a => ∑ i ∈ H, countingSystem (lam a) b L (Y a) i) l
      (𝓝 (∑ i ∈ H, countingTarget n 0 i)) := by
    apply tendsto_const_nhds.congr'
    exact hsolutions.mono (fun a ha => by
      change (∑ i ∈ H, countingTarget n 0 i) = ∑ i ∈ H, countingSystem (lam a) b L (Y a) i
      rw [ha])
  have he := tendsto_nhds_unique ht hc
  have hk : (0 : ℝ) < H.card := by exact_mod_cast Finset.card_pos.mpr hH
  have hf : (2 : ℝ)*n ≤ L := by exact_mod_cast hfill
  have hp : 0 < 1-lam0/Real.pi := sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hpi)
  have hg : 0 < (L : ℝ)/2-n+H.card := by linarith
  have hpos := mul_pos (mul_pos hk hp) hg
  have hid : (H.card : ℝ)*((L : ℝ)*phaseEnd (lam0/2)-(n-H.card)*phaseEnd lam0) -
      (H.card : ℝ)*(n-H.card)/2 = (H.card : ℝ)*(1-lam0/Real.pi)*((L : ℝ)/2-n+H.card) := by
    unfold phaseEnd
    ring
  have hb := countingTarget_cluster_bound n H
  rw [he] at hid
  linarith

end SixVertex
