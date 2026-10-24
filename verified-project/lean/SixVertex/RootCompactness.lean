import SixVertex.LowerRootEscape
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.MetricSpace.ProperSpace.Real
import Mathlib.Topology.Sequences

namespace SixVertex
open Filter Topology Set

/-- An extended-real limit away from +infinity supplies an eventual upper bound. -/
theorem ereal_limit_bounded_above {A : Type*} (l : Filter A) (u : A → ℝ) (z : EReal)
    (hz : z ≠ ⊤) (hu : Tendsto (fun a => (u a : EReal)) l (𝓝 z)) :
    ∃ C : ℝ, ∀ᶠ a in l, u a ≤ C := by
  obtain ⟨C,hC,hCt⟩ := EReal.exists_between_coe_real (lt_top_iff_ne_top.mpr hz)
  refine ⟨C,?_⟩
  exact (hu.eventually (gt_mem_nhds hC)).mono (fun a ha => (EReal.coe_lt_coe_iff.mp ha).le)

theorem ereal_limit_bounded_below {A : Type*} (l : Filter A) (u : A → ℝ) (z : EReal)
    (hz : z ≠ ⊥) (hu : Tendsto (fun a => (u a : EReal)) l (𝓝 z)) :
    ∃ C : ℝ, ∀ᶠ a in l, C ≤ u a := by
  obtain ⟨C,hCb,hC⟩ := EReal.exists_between_coe_real (bot_lt_iff_ne_bot.mpr hz)
  refine ⟨C,?_⟩
  exact (hu.eventually (lt_mem_nhds hC)).mono (fun a ha => (EReal.coe_lt_coe_iff.mp ha).le)

/-- A finite extended-real limit of a root family cannot contain either
infinite endpoint. This packages both no-escape directions without assuming
a real-valued subsequential limit. -/
theorem finite_root_ereal_limits {A : Type*} (l : Filter A) [l.NeBot] (n : ℕ)
    (lam : A → ℝ) (lam0 : ℝ) (b : ℕ → ℝ) (L : ℕ) (hfill : 2*n ≤ L)
    (Y : A → Fin n → ℝ) (Z : Fin n → EReal)
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam l (𝓝 lam0))
    (hZ : ∀ j, Tendsto (fun a => (Y a j : EReal)) l (𝓝 (Z j)))
    (hsolutions : ∀ᶠ a in l, countingSystem (lam a) b L (Y a) = countingTarget n 0) :
    ∀ j, Z j ≠ ⊤ ∧ Z j ≠ ⊥ := by
  classical
  have htop : ∀ j, Z j ≠ ⊤ := by
    intro j hj
    let H : Finset (Fin n) := Finset.univ.filter (fun i => Z i = ⊤)
    have hH : H.Nonempty := ⟨j,by simp [H,hj]⟩
    have hi : ∀ i ∈ H, Tendsto (fun a => Y a i) l atTop := by
      intro i hi
      have he : Z i = ⊤ := (Finset.mem_filter.mp hi).2
      exact EReal.tendsto_coe_nhds_top_iff.mp (he ▸ hZ i)
    have hb : ∀ i ∈ Finset.univ \ H, ∃ C : ℝ, ∀ᶠ a in l, Y a i ≤ C := by
      intro i hi
      have hn : Z i ≠ ⊤ := by simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using (Finset.mem_sdiff.mp hi).2
      exact ereal_limit_bounded_above l (fun a => Y a i) (Z i) hn (hZ i)
    exact no_upper_escape_bounded_complement l n lam lam0 b L hfill Y H hH h0 hpi hLam hi hb hsolutions
  have hbot : ∀ j, Z j ≠ ⊥ := by
    intro j hj
    let H : Finset (Fin n) := Finset.univ.filter (fun i => Z i = ⊥)
    have hH : H.Nonempty := ⟨j,by simp [H,hj]⟩
    have hDown : ∀ i ∈ H, Tendsto (fun a => Y a i) l atBot := by
      intro i hi
      have he : Z i = ⊥ := (Finset.mem_filter.mp hi).2
      exact EReal.tendsto_coe_nhds_bot_iff.mp (he ▸ hZ i)
    have hb : ∀ i ∈ Finset.univ \ H, ∃ C : ℝ, ∀ᶠ a in l, C ≤ Y a i := by
      intro i hi
      have hn : Z i ≠ ⊥ := by simpa only [H,Finset.mem_filter,Finset.mem_univ,true_and] using (Finset.mem_sdiff.mp hi).2
      exact ereal_limit_bounded_below l (fun a => Y a i) (Z i) hn (hZ i)
    apply no_lower_escaping_cluster l n lam lam0 b L hfill Y H hH h0 hpi hLam hDown _ hsolutions
    intro i hi j hj
    obtain ⟨C,hC⟩ := hb j hj
    apply tendsto_atBot.mpr
    intro c
    filter_upwards [hC,(hDown i hi).eventually (eventually_le_atBot (c+C))] with a ha hya
    linarith
  exact fun j => ⟨htop j,hbot j⟩

/-- Every finite-root family with an interior limiting parameter has a real
convergent subsequence. No root-coordinate boundedness is assumed. -/
theorem finite_roots_subsequence_compact (n : ℕ) (lam : ℕ → ℝ) (lam0 : ℝ)
    (b : ℕ → ℝ) (L : ℕ) (hfill : 2*n ≤ L) (Y : ℕ → Fin n → ℝ)
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam atTop (𝓝 lam0))
    (hsolutions : ∀ a, countingSystem (lam a) b L (Y a) = countingTarget n 0) :
    ∃ (Z : Fin n → ℝ) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (Y ∘ φ) atTop (𝓝 Z) := by
  obtain ⟨Z,φ,hφ,hconv⟩ := CompactSpace.tendsto_subseq (fun a i => (Y a i : EReal))
  have hLam' := hLam.comp hφ.tendsto_atTop
  have hc (j : Fin n) : Tendsto (fun a => (Y (φ a) j : EReal)) atTop (𝓝 (Z j)) :=
    (continuous_apply j).continuousAt.tendsto.comp hconv
  have hfin := finite_root_ereal_limits atTop n (lam ∘ φ) lam0 b L hfill (Y ∘ φ) Z h0 hpi hLam' hc
    (Eventually.of_forall (fun a => hsolutions (φ a)))
  refine ⟨fun j => (Z j).toReal,φ,hφ,?_⟩
  apply tendsto_pi_nhds.mpr
  intro j
  have ht := (EReal.tendsto_toReal (hfin j).1 (hfin j).2).comp (hc j)
  simpa only [Function.comp_def,EReal.toReal_coe] using ht

end SixVertex
