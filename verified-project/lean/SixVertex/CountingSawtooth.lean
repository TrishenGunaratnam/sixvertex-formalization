import SixVertex.CountingMass
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.MeasureTheory.Measure.Sum

namespace SixVertex
noncomputable section
open Filter Topology Set MeasureTheory
open scoped ENNReal

/-- Counts labelled roots with multiplicity, including a root at u. -/
def rootsAtMost {n : ℕ} (Y : Fin n → ℝ) (u : ℝ) : Finset (Fin n) :=
  Finset.univ.filter (fun j => Y j ≤ u)

def rootCountLe {n : ℕ} (Y : Fin n → ℝ) (u : ℝ) : ℕ := (rootsAtMost Y u).card

def rootEmpiricalMeasure {n : ℕ} (Y : Fin n → ℝ) : Measure ℝ :=
  Measure.sum (fun j : Fin n => Measure.dirac (Y j))

def countingDiscrepancy {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (u : ℝ) : ℝ :=
  (rootCountLe Y u : ℝ)-(countingXi lam b L Y u+(n : ℝ)/2)

theorem rootCountLe_le {n : ℕ} (Y : Fin n → ℝ) (u : ℝ) : rootCountLe Y u ≤ n := by
  simpa only [rootCountLe,Finset.card_univ,Fintype.card_fin] using (rootsAtMost Y u).card_le_univ

theorem rootCountLe_ge_index {n : ℕ} (Y : Fin n → ℝ) (hY : Monotone Y)
    (u : ℝ) (j : Fin n) (hj : Y j ≤ u) : j.val+1 ≤ rootCountLe Y u := by
  have hs : Finset.Iic j ⊆ rootsAtMost Y u := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(hY (Finset.mem_Iic.mp hi)).trans hj⟩
  simpa only [Fin.card_Iic,rootCountLe] using Finset.card_le_card hs

theorem rootCountLe_le_index {n : ℕ} (Y : Fin n → ℝ) (hY : Monotone Y)
    (u : ℝ) (j : Fin n) (hj : u < Y j) : rootCountLe Y u ≤ j.val := by
  have hs : rootsAtMost Y u ⊆ Finset.Iio j := by
    intro i hi
    apply Finset.mem_Iio.mpr
    by_contra hn
    have hh := (hY (le_of_not_gt hn)).trans (Finset.mem_filter.mp hi).2
    exact (not_le_of_gt hj) hh
  simpa only [Fin.card_Iio,rootCountLe] using Finset.card_le_card hs

theorem rootCountLe_at_root {n : ℕ} (Y : Fin n → ℝ) (hY : StrictMono Y) (j : Fin n) :
    rootCountLe Y (Y j)=j.val+1 := by
  have hs : rootsAtMost Y (Y j)=Finset.Iic j := by
    ext i
    simp only [rootsAtMost,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic]
    exact hY.le_iff_le
  rw [rootCountLe,hs,Fin.card_Iic]

/-- Pure counting-cell geometry. No analytic density bound is assumed. -/
theorem ordered_count_sawtooth {n : ℕ} (Y : Fin n → ℝ) (hY : Monotone Y)
    (xi : ℝ → ℝ) (hxi : Monotone xi)
    (hlevels : ∀ j : Fin n, xi (Y j)=(j.val : ℝ)+1/2-(n : ℝ)/2)
    (hlo : ∀ u, -(n : ℝ)/2 ≤ xi u) (hhi : ∀ u, xi u ≤ (n : ℝ)/2) (u : ℝ) :
    |(rootCountLe Y u : ℝ)-(xi u+(n : ℝ)/2)| ≤ 1/2 := by
  let m:=rootCountLe Y u
  have hmn : m ≤ n := rootCountLe_le Y u
  apply abs_le.mpr
  constructor
  · by_cases hm : m < n
    · let j : Fin n := ⟨m,hm⟩
      have hy : u < Y j := by
        by_contra hn
        have hh:=rootCountLe_ge_index Y hY u j (le_of_not_gt hn)
        change m+1 ≤ m at hh
        omega
      have hh:xi u ≤ (m : ℝ)+1/2-(n : ℝ)/2 := by
        simpa only [j] using (hxi hy.le).trans_eq (hlevels j)
      change -(1/2 : ℝ) ≤ (m : ℝ)-(xi u+(n : ℝ)/2)
      linarith
    · have hm':m=n:=by omega
      change -(1/2 : ℝ) ≤ (m : ℝ)-(xi u+(n : ℝ)/2)
      rw [hm']
      linarith [hhi u]
  · by_cases hm : m=0
    · change (m : ℝ)-(xi u+(n : ℝ)/2) ≤ 1/2
      rw [hm]
      simp only [Nat.cast_zero]
      linarith [hlo u]
    · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
      let j : Fin n := ⟨m-1,by omega⟩
      have hy : Y j ≤ u := by
        by_contra hn
        have hh:=rootCountLe_le_index Y hY u j (lt_of_not_ge hn)
        change m ≤ m-1 at hh
        omega
      have hh:= (hlevels j).symm.trans_le (hxi hy)
      change ((m-1 : ℕ) : ℝ)+1/2-(n : ℝ)/2 ≤ xi u at hh
      rw [Nat.cast_sub (by omega : 1 ≤ m),Nat.cast_one] at hh
      change (m : ℝ)-(xi u+(n : ℝ)/2) ≤ 1/2
      linarith

theorem countingXi_half_bounds {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    -(n : ℝ)/2 ≤ countingXi lam b L Y u ∧ countingXi lam b L Y u ≤ (n : ℝ)/2 := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  have hm := (countingXi_strictMono_nonpositiveK lam b L hL Y hhalf hpi).monotone
  have hb:=countingXi_tendsto_atBot lam b L Y h0 hpi
  have ht:=countingXi_tendsto_atTop lam b L Y h0 hpi
  have he : countingEnd lam L n=(n : ℝ)/2 := by rw [hfill,countingEnd_half]
  rw [he,← neg_div] at hb
  rw [he] at ht
  constructor
  · exact le_of_tendsto hb ((eventually_le_atBot u).mono (fun v hv => hm hv))
  · exact ge_of_tendsto ht ((eventually_ge_atTop u).mono (fun v hv => hm hv))

/-- The half-unit bound is uniform in L, in the real site array, and in
u on the whole real line, for the actual consecutive-root equations. -/
theorem countingDiscrepancy_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hroots : ConsecutiveRoots lam b L Y 0) (u : ℝ) :
    |countingDiscrepancy lam b L Y u| ≤ 1/2 := by
  apply ordered_count_sawtooth Y hroots.1.monotone (countingXi lam b L Y)
    (countingXi_strictMono_nonpositiveK lam b L hL Y hhalf hpi).monotone
  · intro j
    calc
      _ = countingTarget n 0 j := congrFun hroots.2 j
      _ = _ := by unfold countingTarget; ring
  · intro v
    exact (countingXi_half_bounds lam b L hL hfill Y hhalf hpi v).1
  · intro v
    exact (countingXi_half_bounds lam b L hL hfill Y hhalf hpi v).2

theorem rootEmpiricalMeasure_Iic {n : ℕ} (Y : Fin n → ℝ) (u : ℝ) :
    rootEmpiricalMeasure Y (Iic u)=(rootCountLe Y u : ℝ≥0∞) := by
  rw [rootEmpiricalMeasure,Measure.sum_apply_of_countable,tsum_fintype]
  simp only [Measure.dirac_apply' _ measurableSet_Iic,Set.indicator,Set.mem_Iic,Pi.one_apply]
  exact Finset.sum_boole _ _

theorem rootEmpiricalMeasure_real_Iic {n : ℕ} (Y : Fin n → ℝ) (u : ℝ) :
    (rootEmpiricalMeasure Y).real (Iic u)=(rootCountLe Y u : ℝ) := by
  rw [Measure.real,rootEmpiricalMeasure_Iic]
  simp

theorem rootEmpiricalMeasure_mass {n : ℕ} (Y : Fin n → ℝ) :
    rootEmpiricalMeasure Y univ=(n : ℝ≥0∞) := by
  simp [rootEmpiricalMeasure,Measure.sum_apply_of_countable,tsum_fintype]

/-- This equality ties the uniform sawtooth estimate to the actual
atomic counting measure minus the actual cumulative density integral. -/
theorem countingDiscrepancy_eq_primitive {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hL : 0 < L) (hfill : L=2*n) (Y : Fin n → ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (u : ℝ) :
    countingDiscrepancy lam b L Y u=(rootEmpiricalMeasure Y).real (Iic u)-
      ∫ v in Iic u, countingSlope lam b L Y v := by
  rw [rootEmpiricalMeasure_real_Iic,integral_Iic_countingSlope_half lam b L hL hfill Y hhalf hpi]
  rfl

theorem countingDiscrepancy_at_root {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hroots : ConsecutiveRoots lam b L Y 0) (j : Fin n) :
    countingDiscrepancy lam b L Y (Y j)=1/2 := by
  unfold countingDiscrepancy
  rw [rootCountLe_at_root Y hroots.1]
  have he : countingXi lam b L Y (Y j)=countingTarget n 0 j := congrFun hroots.2 j
  rw [he]
  unfold countingTarget
  push_cast
  ring

theorem rootCountLe_eventually_atTop {n : ℕ} (Y : Fin n → ℝ) :
    ∀ᶠ u in atTop, rootCountLe Y u=n := by
  have ht : ∀ᶠ u : ℝ in atTop, ∀ j : Fin n, Y j ≤ u :=
    eventually_all.mpr (fun j => eventually_ge_atTop (Y j))
  filter_upwards [ht] with u hu
  have hs : rootsAtMost Y u=Finset.univ := by
    apply Finset.filter_eq_self.mpr
    exact fun j hj => hu j
  simp only [rootCountLe,hs,Finset.card_univ,Fintype.card_fin]

theorem rootCountLe_eventually_atBot {n : ℕ} (Y : Fin n → ℝ) :
    ∀ᶠ u in atBot, rootCountLe Y u=0 := by
  have ht : ∀ᶠ u : ℝ in atBot, ∀ j : Fin n, u ≤ Y j-1 :=
    eventually_all.mpr (fun j => eventually_le_atBot (Y j-1))
  filter_upwards [ht] with u hu
  have hs : rootsAtMost Y u=∅ := by
    apply Finset.filter_eq_empty_iff.mpr
    intro j hj hn
    linarith [hu j]
  simp only [rootCountLe,hs,Finset.card_empty]

theorem countingDiscrepancy_tendsto_atTop {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hfill : L=2*n) (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Tendsto (countingDiscrepancy lam b L Y) atTop (𝓝 0) := by
  have hc : Tendsto (fun u => (rootCountLe Y u : ℝ)) atTop (𝓝 (n : ℝ)) := by
    apply tendsto_const_nhds.congr'
    exact (rootCountLe_eventually_atTop Y).mono (fun u hu => by change (n : ℝ)=(rootCountLe Y u : ℝ); rw [hu])
  have hxi:=countingXi_tendsto_atTop lam b L Y h0 hpi
  have he : countingEnd lam L n=(n : ℝ)/2 := by rw [hfill,countingEnd_half]
  rw [he] at hxi
  have ht:=hc.sub (hxi.add_const ((n : ℝ)/2))
  have hh : (n : ℝ)-(n/2+n/2)=0 := by ring
  rw [hh] at ht
  change Tendsto (fun u => (rootCountLe Y u : ℝ)-(countingXi lam b L Y u+(n : ℝ)/2)) atTop (𝓝 0)
  exact ht

theorem countingDiscrepancy_tendsto_atBot {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (hfill : L=2*n) (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    Tendsto (countingDiscrepancy lam b L Y) atBot (𝓝 0) := by
  have hc : Tendsto (fun u => (rootCountLe Y u : ℝ)) atBot (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    exact (rootCountLe_eventually_atBot Y).mono (fun u hu => by change (0 : ℝ)=(rootCountLe Y u : ℝ); rw [hu]; norm_num)
  have hxi:=countingXi_tendsto_atBot lam b L Y h0 hpi
  have he : countingEnd lam L n=(n : ℝ)/2 := by rw [hfill,countingEnd_half]
  rw [he] at hxi
  have ht:=hc.sub (hxi.add_const ((n : ℝ)/2))
  simp only [neg_add_cancel,sub_zero] at ht
  change Tendsto (fun u => (rootCountLe Y u : ℝ)-(countingXi lam b L Y u+(n : ℝ)/2)) atBot (𝓝 0)
  exact ht

end
end SixVertex
