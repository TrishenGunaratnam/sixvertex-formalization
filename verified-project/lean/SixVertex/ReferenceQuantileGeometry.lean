import SixVertex.ReferenceQuantiles
import SixVertex.LocalCountingWindow

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

def referenceQuantileDiscrepancy {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) (u : ℝ) : ℝ :=
  (rootCountLe Y u : ℝ)-(L : ℝ)*finiteIntervalCumulative lam h0 hpi Q u

/-- Actual quantile levels give the half-unit counting error on their
occupied reference interval. -/
theorem referenceQuantileDiscrepancy_bound {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (L : ℕ) (hL : 0 < L) (Y : Fin n → ℝ) (hY : StrictMono Y)
    (hmass : (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ))
    (hlevels : ∀ j, (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q (Y j)=(j.val : ℝ)+1/2)
    (u : ℝ) (hu : u ∈ Icc (-Q) Q) :
    |referenceQuantileDiscrepancy lam h0 hpi Q L Y u| ≤ 1/2 := by
  let P : ℝ → ℝ := fun v => (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q v
  let xi : ℝ → ℝ := fun v => P v-(n : ℝ)/2
  have hLp : (0 : ℝ) ≤ L := Nat.cast_nonneg _
  have hc := (finiteIntervalCumulative_strictMono lam h0 hhalf hpi Q).monotone
  have hpmono : Monotone P := fun x y hxy => mul_le_mul_of_nonneg_left (hc hxy) hLp
  have hximono : Monotone xi := fun x y hxy => sub_le_sub_right (hpmono hxy) _
  have hp0 : P (-Q)=0 := by dsimp [P]; rw [finiteIntervalCumulative_left,mul_zero]
  have hpn : P Q=(n : ℝ) := by dsimp [P]; rw [finiteIntervalCumulative_right lam h0 hpi Q hQ]; exact hmass
  have hlo : 0 ≤ P u := by have h := hpmono hu.1; rwa [hp0] at h
  have hhi : P u ≤ (n : ℝ) := by have h := hpmono hu.2; rwa [hpn] at h
  have hl : ∀ j : Fin n, xi (Y j)=(j.val : ℝ)+1/2-(n : ℝ)/2 := by
    intro j
    dsimp [xi,P]
    rw [hlevels j]
  have hh := ordered_count_sawtooth_local Y hY.monotone xi hximono hl u
    (by dsimp [xi]; linarith) (by dsimp [xi]; linarith)
  dsimp [xi] at hh
  change |(rootCountLe Y u : ℝ)-P u| ≤ 1/2
  simpa only [sub_add_cancel] using hh

/-- The complete reference configuration exists for every finite
negative-kernel sub-half filling, before asserting root stability. -/
theorem exists_subhalf_reference_configuration (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (L n : ℕ)
    (hL : 0 < L) (hn : 0 < n) (hfill : 2*n < L) :
    ∃ (Q : ℝ) (Y : Fin n → ℝ), 0 < Q ∧
      finiteIntervalMass lam h0 hpi Q=(n : ℝ)/(L : ℝ) ∧ StrictMono Y ∧
      ∀ j : Fin n, Y j ∈ Ioo (-Q) Q ∧
        (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q (Y j)=(j.val : ℝ)+1/2 := by
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hf : (n : ℝ)/(L : ℝ) < 1/2 := by
    apply (div_lt_iff₀ hLp).mpr
    have hh : 2*(n : ℝ) < (L : ℝ) := by exact_mod_cast hfill
    linarith
  obtain ⟨Q,hQ,hm⟩ := exists_finiteIntervalCutoff lam h0 hhalf hpi ((n : ℝ)/(L : ℝ)) (div_pos hnp hLp) hf
  have hmass : (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ) := by rw [hm]; field_simp
  obtain ⟨Y,hY,hy⟩ := exists_finiteInterval_midQuantiles lam h0 hhalf hpi Q hQ.le L n hL hmass
  exact ⟨Q,Y,hQ,hm,hY,hy⟩

end
end SixVertex

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Data for the actual continuum reference configuration. This is
separate from ConsecutiveRoots, which requires the Bethe equations. -/
structure ReferenceQuantileData {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (L : ℕ) (Y : Fin n → ℝ) : Prop where
  interval_nonneg : 0 ≤ Q
  chain_pos : 0 < L
  mass : (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ)
  ordered : StrictMono Y
  location : ∀ j, Y j ∈ Ioo (-Q) Q
  level : ∀ j, (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q (Y j)=(j.val : ℝ)+1/2

theorem exists_subhalf_reference_data (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (L n : ℕ)
    (hL : 0 < L) (hn : 0 < n) (hfill : 2*n < L) :
    ∃ (Q : ℝ) (Y : Fin n → ℝ), 0 < Q ∧ ReferenceQuantileData lam h0 hpi Q L Y := by
  obtain ⟨Q,Y,hQ,hm,hY,hy⟩ := exists_subhalf_reference_configuration lam h0 hhalf hpi L n hL hn hfill
  refine ⟨Q,Y,hQ,⟨hQ.le,hL,?_,hY,(fun j => (hy j).1),(fun j => (hy j).2)⟩⟩
  rw [hm]
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  field_simp

end
end SixVertex
