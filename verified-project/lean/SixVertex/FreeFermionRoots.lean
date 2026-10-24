import SixVertex.RootMonotonicity

namespace SixVertex
open Filter Topology

@[simp] theorem countingTheta_freeFermion (u : ℝ) : countingTheta (Real.pi/2) u = 0 := by
  simp [countingTheta,barePhase,Real.cos_pi_div_two]

@[simp] theorem kernelK_freeFermion (u : ℝ) : kernelK (Real.pi/2) u = 0 := by
  simp [kernelK,phaseDensity,show 2*(Real.pi/2) = Real.pi by ring]

theorem countingS_freeFermion (u : ℝ) :
    countingS (Real.pi/2) u = Real.arctan (Real.tanh u)/Real.pi := by
  have hs : Real.sin (Real.pi/4) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).ne'
  have he : Real.cos (Real.pi/4) = Real.sin (Real.pi/4) := by
    rw [Real.cos_pi_div_four,Real.sin_pi_div_four]
  simp only [countingS,barePhase,show Real.pi/2/2 = Real.pi/4 by ring,he,
    div_self hs,one_mul,Real.tanh_eq_sinh_div_cosh]

/-- A nonsingular exponential form suited to the real end limits. -/
theorem tanh_negative_exponential (u : ℝ) :
    Real.tanh u = (1-Real.exp (-2*u))/(1+Real.exp (-2*u)) := by
  rw [Real.tanh_eq]
  have h1 : Real.exp u + Real.exp (-u) ≠ 0 := (add_pos (Real.exp_pos _) (Real.exp_pos _)).ne'
  have h2 : 1+Real.exp (-2*u) ≠ 0 := by positivity
  have he : Real.exp (-2*u)*Real.exp u = Real.exp (-u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  apply (div_eq_div_iff h1 h2).mpr
  nlinarith [he]

theorem tanh_tendsto_atTop : Tendsto Real.tanh atTop (𝓝 (1 : ℝ)) := by
  have hm : Tendsto (fun u : ℝ => 2*u) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr tendsto_id
  have he : Tendsto (fun u : ℝ => Real.exp (-2*u)) atTop (𝓝 0) := by
    convert Real.tendsto_exp_neg_atTop_nhds_zero.comp hm using 1
    funext u
    congr 1
    ring
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have ht := (hone.sub he).div (hone.add he) (by norm_num : (1 : ℝ)+0 ≠ 0)
  simp only [sub_zero,add_zero,div_one] at ht
  exact ht.congr (fun u => (tanh_negative_exponential u).symm)

theorem tanh_tendsto_atBot : Tendsto Real.tanh atBot (𝓝 (-1 : ℝ)) := by
  have ht := (tanh_tendsto_atTop.comp tendsto_neg_atBot_atTop).neg
  simpa only [Function.comp_def,Real.tanh_neg,neg_neg] using ht

theorem countingS_freeFermion_atTop : Tendsto (countingS (Real.pi/2)) atTop (𝓝 (1/4 : ℝ)) := by
  have ht := ((Real.continuous_arctan.tendsto 1).comp tanh_tendsto_atTop).div_const Real.pi
  have hc : Real.arctan (1 : ℝ)/Real.pi = 1/4 := by rw [Real.arctan_one]; field_simp
  rw [hc] at ht
  exact ht.congr (fun u => (countingS_freeFermion u).symm)

theorem countingS_freeFermion_atBot : Tendsto (countingS (Real.pi/2)) atBot (𝓝 (-1/4 : ℝ)) := by
  have ht := countingS_freeFermion_atTop.comp tendsto_neg_atBot_atTop
  have hn := ht.neg
  change Tendsto (barePhase (Real.pi/2/2)) atBot (𝓝 (-1/4 : ℝ))
  simpa only [Function.comp_def,countingS,barePhase_neg,neg_neg,neg_div] using hn

noncomputable def freeFermionCounting (b : ℕ → ℝ) (L : ℕ) (u : ℝ) : ℝ :=
  ∑ a ∈ Finset.range L, countingS (Real.pi/2) (u-b a)

theorem countingXi_freeFermion {n : ℕ} (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (u : ℝ) :
    countingXi (Real.pi/2) b L Y u = freeFermionCounting b L u := by
  simp [countingXi,freeFermionCounting]

theorem freeFermionCounting_atTop (b : ℕ → ℝ) (L : ℕ) :
    Tendsto (freeFermionCounting b L) atTop (𝓝 ((L : ℝ)/4)) := by
  have ht (a : ℕ) : Tendsto (fun u : ℝ => u-b a) atTop atTop := by
    apply tendsto_atTop.mpr
    intro c
    filter_upwards [eventually_ge_atTop (c+b a)] with u hu
    linarith
  have h := tendsto_finsetSum (Finset.range L) (fun a ha => countingS_freeFermion_atTop.comp (ht a))
  have hs : (∑ a ∈ Finset.range L, (1/4 : ℝ)) = (L : ℝ)/4 := by simp [div_eq_mul_inv]
  rw [hs] at h
  exact h

theorem freeFermionCounting_atBot (b : ℕ → ℝ) (L : ℕ) :
    Tendsto (freeFermionCounting b L) atBot (𝓝 (-(L : ℝ)/4)) := by
  have ht (a : ℕ) : Tendsto (fun u : ℝ => u-b a) atBot atBot := by
    apply tendsto_atBot.mpr
    intro c
    filter_upwards [eventually_le_atBot (c+b a)] with u hu
    linarith
  have h := tendsto_finsetSum (Finset.range L) (fun a ha => countingS_freeFermion_atBot.comp (ht a))
  have hs : (∑ a ∈ Finset.range L, (-1/4 : ℝ)) = -(L : ℝ)/4 := by
    simp [div_eq_mul_inv]
  rw [hs] at h
  exact h

theorem freeFermionCounting_strictMono (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L) :
    StrictMono (freeFermionCounting b L) := by
  have h := countingXi_strictMono_nonpositiveK (Real.pi/2) b L hL (fun j : Fin 0 => j.elim0)
    (le_refl _) (by linarith [Real.pi_pos])
  have he : countingXi (Real.pi/2) b L (fun j : Fin 0 => j.elim0) = freeFermionCounting b L :=
    funext (countingXi_freeFermion b L _)
  rw [he] at h
  exact h

theorem freeFermionCounting_continuous (b : ℕ → ℝ) (L : ℕ) : Continuous (freeFermionCounting b L) := by
  apply continuous_iff_continuousAt.mpr
  intro u
  have h := (hasDerivAt_countingXi (Real.pi/2) b L (fun j : Fin 0 => j.elim0) u
    (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).continuousAt
  have he : countingXi (Real.pi/2) b L (fun j : Fin 0 => j.elim0) = freeFermionCounting b L :=
    funext (countingXi_freeFermion b L _)
  rw [he] at h
  exact h

/-- Every allowed free-fermion counting level has a unique real preimage,
for an arbitrary finite real array of site parameters. -/
theorem freeFermionCounting_exists_unique (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (c : ℝ) (hc : -(L : ℝ)/4 < c ∧ c < (L : ℝ)/4) :
    ∃! u, freeFermionCounting b L u = c := by
  have hlo : ∃ u, freeFermionCounting b L u ≤ c := by
    obtain ⟨u,hu⟩ := ((freeFermionCounting_atBot b L).eventually (gt_mem_nhds hc.1)).exists
    exact ⟨u,hu.le⟩
  have hhi : ∃ u, c ≤ freeFermionCounting b L u := by
    obtain ⟨u,hu⟩ := ((freeFermionCounting_atTop b L).eventually (lt_mem_nhds hc.2)).exists
    exact ⟨u,hu.le⟩
  obtain ⟨u,hu⟩ := mem_range_of_exists_le_of_exists_ge (freeFermionCounting_continuous b L) hlo hhi
  refine ⟨u,hu,?_⟩
  intro v hv
  exact (freeFermionCounting_strictMono b L hL).injective (hv.trans hu.symm)

/-- The actual starting roots for Lemma 3.1's continuation construction.
This is finite root existence, including real arrays, not just conditional data. -/
theorem exists_unique_freeFermion_roots (b : ℕ → ℝ) (L : ℕ) (hL : 0 < L)
    (n : ℕ) (hfill : 2*n ≤ L) :
    ∃! Y : Fin n → ℝ, ConsecutiveRoots (Real.pi/2) b L Y 0 := by
  classical
  have hlevels (j : Fin n) : -(L : ℝ)/4 < countingTarget n 0 j ∧ countingTarget n 0 j < (L : ℝ)/4 := by
    have hj0 : (0 : ℝ) ≤ j.val := Nat.cast_nonneg _
    have hjn : (j.val : ℝ)+1 ≤ n := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
    have hf : (2 : ℝ)*n ≤ L := by exact_mod_cast hfill
    unfold countingTarget
    norm_num
    constructor <;> linarith
  choose Y hY using (fun j : Fin n => (freeFermionCounting_exists_unique b L hL (countingTarget n 0 j) (hlevels j)).exists)
  have hm : StrictMono Y := by
    intro i j hij
    apply (freeFermionCounting_strictMono b L hL).lt_iff_lt.mp
    rw [hY i,hY j]
    unfold countingTarget
    have hv : (i.val : ℝ) < j.val := by exact_mod_cast hij
    linarith
  have hs : ConsecutiveRoots (Real.pi/2) b L Y 0 := by
    refine ⟨hm,funext (fun j => ?_)⟩
    change countingXi (Real.pi/2) b L Y (Y j) = _
    rw [countingXi_freeFermion,hY j]
  refine ⟨Y,hs,?_⟩
  intro Z hZ
  exact consecutiveRoots_unique_nonpositiveK (Real.pi/2) b L hL (le_refl _)
    (by linarith [Real.pi_pos]) 0 Z Y hZ hs

end SixVertex
