import SixVertex.KernelMass
import SixVertex.GlobalRootFamily

namespace SixVertex
open Filter Topology Set MeasureTheory

theorem real_shift_tendsto_atTop (c : ℝ) : Tendsto (fun u : ℝ => u-c) atTop atTop := by
  apply tendsto_atTop.mpr
  intro M
  filter_upwards [eventually_ge_atTop (M+c)] with u hu
  linarith

theorem real_shift_tendsto_atBot (c : ℝ) : Tendsto (fun u : ℝ => u-c) atBot atBot := by
  apply tendsto_atBot.mpr
  intro M
  filter_upwards [eventually_le_atBot (M+c)] with u hu
  linarith

noncomputable def countingEnd (lam : ℝ) (L n : ℕ) : ℝ :=
  (L : ℝ)*phaseEnd (lam/2)-(n : ℝ)*phaseEnd lam

theorem countingXi_tendsto_atTop {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Tendsto (countingXi lam b L Y) atTop (𝓝 (countingEnd lam L n)) := by
  change Tendsto (fun u => (∑ a ∈ Finset.range L, countingS lam (u-b a))-
    ∑ j : Fin n, countingTheta lam (u-Y j)) atTop (𝓝 _)
  have hs := tendsto_finsetSum (Finset.range L) (fun a ha =>
    countingS_tendsto_atTop atTop (fun _ : ℝ => lam) (fun u => u-b a) lam h0 hpi
      tendsto_const_nhds (real_shift_tendsto_atTop (b a)))
  have hk := tendsto_finsetSum Finset.univ (fun j (hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    countingTheta_tendsto_atTop atTop (fun _ : ℝ => lam) (fun u => u-Y j) lam h0 hpi
      tendsto_const_nhds (real_shift_tendsto_atTop (Y j)))
  simpa only [countingXi,countingEnd,Finset.sum_const,Finset.card_range,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using hs.sub hk

theorem countingXi_tendsto_atBot {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Tendsto (countingXi lam b L Y) atBot (𝓝 (-countingEnd lam L n)) := by
  change Tendsto (fun u => (∑ a ∈ Finset.range L, countingS lam (u-b a))-
    ∑ j : Fin n, countingTheta lam (u-Y j)) atBot (𝓝 _)
  have hs := tendsto_finsetSum (Finset.range L) (fun a ha =>
    barePhase_tendsto_atBot atBot (fun _ : ℝ => lam/2) (fun u => u-b a) (lam/2)
      (by linarith) (by linarith [Real.pi_pos]) tendsto_const_nhds
      (real_shift_tendsto_atBot (b a)))
  have hk := tendsto_finsetSum Finset.univ (fun j (hj : j ∈ (Finset.univ : Finset (Fin n))) =>
    barePhase_tendsto_atBot atBot (fun _ : ℝ => lam) (fun u => u-Y j) lam h0 hpi
      tendsto_const_nhds (real_shift_tendsto_atBot (Y j)))
  have he : (∑ a ∈ Finset.range L, -phaseEnd (lam/2)) -
      (∑ _j : Fin n, -phaseEnd lam) = -countingEnd lam L n := by
    simp only [Finset.sum_const,Finset.card_range,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,countingEnd]
    ring
  have ht := hs.sub hk
  rw [he] at ht
  simpa only [countingXi,countingS,countingTheta] using ht

theorem countingEnd_half (lam : ℝ) (n : ℕ) : countingEnd lam (2*n) n=(n : ℝ)/2 := by
  unfold countingEnd phaseEnd
  push_cast
  ring

theorem countingSlope_integrable_nonpositiveK {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (Y : Fin n → ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    Integrable (countingSlope lam b L Y) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  exact integrable_nonnegative_derivative_limits (countingXi lam b L Y)
    (countingSlope lam b L Y) (-countingEnd lam L n) (countingEnd lam L n)
    (fun u => hasDerivAt_countingXi lam b L Y u h0 hpi)
    (fun u => (countingSlope_pos_nonpositiveK lam b L hL Y u hhalf hpi).le)
    (countingXi_tendsto_atBot lam b L Y h0 hpi)
    (countingXi_tendsto_atTop lam b L Y h0 hpi)

/-- The counting-density mass at exact half filling is exactly the
number of roots, for every finite real root list and real site array. -/
theorem integral_countingSlope_half {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    (∫ u : ℝ, countingSlope lam b L Y u)=(n : ℝ) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  rw [integral_of_hasDerivAt_of_tendsto
    (fun u => hasDerivAt_countingXi lam b L Y u h0 hpi)
    (countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi)
    (countingXi_tendsto_atBot lam b L Y h0 hpi)
    (countingXi_tendsto_atTop lam b L Y h0 hpi)]
  rw [hfill,countingEnd_half]
  ring

/-- The actual half-line integral, rather than an independently assigned
primitive. This identifies the discrepancy used in the paper. -/
theorem integral_Iic_countingSlope_half {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    (∫ v in Iic u, countingSlope lam b L Y v)=countingXi lam b L Y u+(n : ℝ)/2 := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  rw [integral_Iic_of_hasDerivAt_of_tendsto'
    (fun v hv => hasDerivAt_countingXi lam b L Y v h0 hpi)
    (countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi).integrableOn
    (countingXi_tendsto_atBot lam b L Y h0 hpi)]
  rw [hfill,countingEnd_half,sub_neg_eq_add]

theorem integral_Ioi_countingSlope_half {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    (∫ v in Ioi u, countingSlope lam b L Y v)=(n : ℝ)/2-countingXi lam b L Y u := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  rw [integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun v hv => hasDerivAt_countingXi lam b L Y v h0 hpi)
    (countingSlope_integrable_nonpositiveK lam b L hL Y hhalf hpi).integrableOn
    (countingXi_tendsto_atTop lam b L Y h0 hpi)]
  rw [hfill,countingEnd_half]

end SixVertex
