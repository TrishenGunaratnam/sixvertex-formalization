import SixVertex.RootEscape

namespace SixVertex
open Filter Topology

theorem countingTarget_total_zero (n : ℕ) : (∑ i : Fin n, countingTarget n 0 i) = 0 := by
  simp only [countingTarget_orderSign,div_eq_mul_inv]
  rw [← Finset.sum_mul,antisymmetric_finset_sum_zero Finset.univ countingOrderSign countingOrderSign_antisymm]
  simp

theorem countingTarget_cluster_lower_bound (n : ℕ) (H : Finset (Fin n)) :
    -(H.card : ℝ)*(n-H.card)/2 ≤ (∑ i ∈ H, countingTarget n 0 i) := by
  classical
  let C := Finset.univ \ H
  have hsplit : (∑ i ∈ H, countingTarget n 0 i)+(∑ i ∈ C, countingTarget n 0 i) = 0 := by
    simpa only [Finset.univ_inter,C,countingTarget_total_zero] using
      Finset.sum_inter_add_sum_sdiff Finset.univ H (countingTarget n 0)
  have hc : C.card = n-H.card := by simp [C,Finset.card_sdiff]
  have hle : H.card ≤ n := by simpa using H.card_le_univ
  have hb := countingTarget_cluster_bound n C
  rw [hc,Nat.cast_sub hle] at hb
  nlinarith

theorem countingSystem_negate {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) :
    countingSystem lam (fun a => -b a) L (fun i => -Y i) = -countingSystem lam b L Y := by
  funext i
  simp only [countingSystem,countingXi,neg_sub_neg,Pi.neg_apply]
  have hs (a : ℕ) : countingS lam (b a-Y i) = -countingS lam (Y i-b a) := by
    rw [show b a-Y i = -(Y i-b a) by ring]
    exact barePhase_neg (lam/2) _
  have hk (j : Fin n) : countingTheta lam (Y j-Y i) = -countingTheta lam (Y i-Y j) := by
    rw [show Y j-Y i = -(Y i-Y j) by ring]
    exact barePhase_neg lam _
  simp only [hs,hk,Finset.sum_neg_distrib]
  ring

theorem counting_cluster_atBot {A : Type*} (l : Filter A) (n : ℕ) (lam : A → ℝ) (lam0 : ℝ)
    (b : ℕ → ℝ) (L : ℕ) (Y : A → Fin n → ℝ) (H : Finset (Fin n))
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam l (𝓝 lam0))
    (hY : ∀ i ∈ H, Tendsto (fun a => Y a i) l atBot)
    (hcross : ∀ i ∈ H, ∀ j ∈ Finset.univ \ H, Tendsto (fun a => Y a i-Y a j) l atBot) :
    Tendsto (fun a => ∑ i ∈ H, countingSystem (lam a) b L (Y a) i) l
      (𝓝 (-(H.card : ℝ)*((L : ℝ)*phaseEnd (lam0/2)-(n-H.card)*phaseEnd lam0))) := by
  have hYn : ∀ i ∈ H, Tendsto (fun a => -Y a i) l atTop :=
    fun i hi => tendsto_neg_atBot_atTop.comp (hY i hi)
  have hcn : ∀ i ∈ H, ∀ j ∈ Finset.univ \ H, Tendsto (fun a => -Y a i-(-Y a j)) l atTop := by
    intro i hi j hj
    have ht := tendsto_neg_atBot_atTop.comp (hcross i hi j hj)
    exact ht.congr (fun a => by change -(Y a i-Y a j) = _; ring)
  have ht := (counting_cluster_atTop l n lam lam0 (fun a => -b a) L (fun a i => -Y a i)
    H h0 hpi hLam hYn hcn).neg
  have he (a : A) : -(∑ i ∈ H, countingSystem (lam a) (fun j => -b j) L (fun j => -Y a j) i) =
      ∑ i ∈ H, countingSystem (lam a) b L (Y a) i := by
    rw [countingSystem_negate]
    simp
  simpa only [neg_mul] using ht.congr he

/-- The opposite escape direction is also excluded, including variation of
lambda within the physical interval. -/
theorem no_lower_escaping_cluster {A : Type*} (l : Filter A) [l.NeBot] (n : ℕ)
    (lam : A → ℝ) (lam0 : ℝ) (b : ℕ → ℝ) (L : ℕ) (hfill : 2*n ≤ L)
    (Y : A → Fin n → ℝ) (H : Finset (Fin n)) (hH : H.Nonempty)
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam l (𝓝 lam0))
    (hY : ∀ i ∈ H, Tendsto (fun a => Y a i) l atBot)
    (hcross : ∀ i ∈ H, ∀ j ∈ Finset.univ \ H, Tendsto (fun a => Y a i-Y a j) l atBot)
    (hsolutions : ∀ᶠ a in l, countingSystem (lam a) b L (Y a) = countingTarget n 0) : False := by
  have ht := counting_cluster_atBot l n lam lam0 b L Y H h0 hpi hLam hY hcross
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
  have hb := countingTarget_cluster_lower_bound n H
  linarith

/-- Bounded complementary coordinates imply the cross-cluster separation
used in the positive escape obstruction. -/
theorem no_upper_escape_bounded_complement {A : Type*} (l : Filter A) [l.NeBot] (n : ℕ)
    (lam : A → ℝ) (lam0 : ℝ) (b : ℕ → ℝ) (L : ℕ) (hfill : 2*n ≤ L)
    (Y : A → Fin n → ℝ) (H : Finset (Fin n)) (hH : H.Nonempty)
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam l (𝓝 lam0))
    (hY : ∀ i ∈ H, Tendsto (fun a => Y a i) l atTop)
    (hbounded : ∀ j ∈ Finset.univ \ H, ∃ C : ℝ, ∀ᶠ a in l, Y a j ≤ C)
    (hsolutions : ∀ᶠ a in l, countingSystem (lam a) b L (Y a) = countingTarget n 0) : False := by
  apply no_upper_escaping_cluster l n lam lam0 b L hfill Y H hH h0 hpi hLam hY _ hsolutions
  intro i hi j hj
  obtain ⟨C,hC⟩ := hbounded j hj
  apply tendsto_atTop.mpr
  intro c
  filter_upwards [hC,(hY i hi).eventually (eventually_ge_atTop (c+C))] with a ha hb
  linarith

end SixVertex
