import SixVertex.UniformFillingMass
import SixVertex.ReferenceQuantileGeometry

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Actual finite-window positivity throughout the physical range. -/
theorem finiteIntervalDensity_pos_all (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q u : ℝ) : 0 < finiteIntervalDensity lam h0 hpi Q u := by
  by_cases hh : Real.pi/2 ≤ lam
  · exact finiteIntervalDensity_pos lam h0 hh hpi Q u
  · exact finiteIntervalDensity_pos_positiveK lam h0 (lt_of_not_ge hh) Q u

/-- The actual cumulative integral is strictly increasing for every
physical parameter, before any discrete Bethe roots are asserted. -/
theorem finiteIntervalCumulative_strictMono_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) : StrictMono (finiteIntervalCumulative lam h0 hpi Q) :=
  strictMono_of_hasDerivAt_pos (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q)
    (finiteIntervalDensity_pos_all lam h0 hpi Q)

/-- Every interior cumulative level has one actual reference quantile. -/
theorem exists_unique_finiteIntervalQuantile_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (t : ℝ) (ht : 0 < t) (htmass : t < finiteIntervalMass lam h0 hpi Q) :
    ∃! y : ℝ, y ∈ Ioo (-Q) Q ∧ finiteIntervalCumulative lam h0 hpi Q y=t := by
  have hc := finiteIntervalCumulative_continuous lam h0 hpi Q
  have hm := finiteIntervalCumulative_strictMono_all lam h0 hpi Q
  have hin : t ∈ Icc (finiteIntervalCumulative lam h0 hpi Q (-Q))
      (finiteIntervalCumulative lam h0 hpi Q Q) := by
    rw [finiteIntervalCumulative_left,finiteIntervalCumulative_right lam h0 hpi Q hQ]
    exact ⟨ht.le,htmass.le⟩
  obtain ⟨y,hy,hyt⟩ := intermediate_value_Icc (show -Q ≤ Q by linarith) hc.continuousOn hin
  have hylo : -Q < y := by
    by_contra hn
    have hh := hm.monotone (le_of_not_gt hn)
    rw [hyt,finiteIntervalCumulative_left] at hh
    linarith
  have hyhi : y < Q := by
    by_contra hn
    have hh := hm.monotone (le_of_not_gt hn)
    rw [hyt,finiteIntervalCumulative_right lam h0 hpi Q hQ] at hh
    linarith
  refine ⟨y,⟨⟨hylo,hyhi⟩,hyt⟩,?_⟩
  intro z hz
  exact hm.injective (hz.2.trans hyt.symm)

/-- The manuscript's finite reference mid-quantiles, with exact ordinary
cumulative equations, strict ordering and open-interval location. No
on-shell Bethe equation is asserted for this reference configuration. -/
theorem exists_finiteInterval_midQuantiles_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (L n : ℕ) (hL : 0 < L) (hmass : (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ)) :
    ∃ Y : Fin n → ℝ, StrictMono Y ∧ ∀ j : Fin n,
      Y j ∈ Ioo (-Q) Q ∧
      (L : ℝ)*finiteIntervalCumulative lam h0 hpi Q (Y j)=(j.val : ℝ)+1/2 := by
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  let target : Fin n → ℝ := fun j => ((j.val : ℝ)+1/2)/(L : ℝ)
  have ht (j : Fin n) : 0 < target j ∧ target j < finiteIntervalMass lam h0 hpi Q := by
    constructor
    · dsimp [target]; positivity
    · dsimp [target]
      apply (div_lt_iff₀ hLp).mpr
      have hj : (j.val : ℝ)+1 ≤ (n : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr j.isLt)
      nlinarith [hmass]
  have hex (j : Fin n) : ∃ y : ℝ, y ∈ Ioo (-Q) Q ∧ finiteIntervalCumulative lam h0 hpi Q y=target j :=
    (exists_unique_finiteIntervalQuantile_all lam h0 hpi Q hQ (target j) (ht j).1 (ht j).2).exists
  let Y : Fin n → ℝ := fun j => Classical.choose (hex j)
  have hs (j : Fin n) : Y j ∈ Ioo (-Q) Q ∧ finiteIntervalCumulative lam h0 hpi Q (Y j)=target j :=
    Classical.choose_spec (hex j)
  have hm := finiteIntervalCumulative_strictMono_all lam h0 hpi Q
  refine ⟨Y,?_,?_⟩
  · intro i j hij
    have hijreal : (i.val : ℝ) < (j.val : ℝ) := by exact_mod_cast hij
    have htij : target i < target j := div_lt_div_of_pos_right (by linarith) hLp
    by_contra hn
    have hh := hm.monotone (le_of_not_gt hn)
    rw [(hs j).2,(hs i).2] at hh
    exact (not_le_of_gt htij) hh
  · intro j
    refine ⟨(hs j).1,?_⟩
    rw [(hs j).2]
    dsimp [target]
    field_simp

/-- The actual mass-selected reference mid-quantile data exist for every
physical lambda and every strictly subhalf finite filling. These are
reference points; the discrete Bethe equations remain a later obligation. -/
theorem exists_subhalf_reference_data_all (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (L n : ℕ) (hL : 0 < L) (hn : 0 < n) (hfill : 2*n < L) :
    ∃ (Q : ℝ) (Y : Fin n → ℝ),0 < Q ∧ ReferenceQuantileData lam h0 hpi Q L Y := by
  have hLp : (0 : ℝ) < L := Nat.cast_pos.mpr hL
  have hnp : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hf : (n : ℝ)/(L : ℝ) < 1/2 := by
    apply (div_lt_iff₀ hLp).mpr
    have hh : 2*(n : ℝ) < (L : ℝ) := by exact_mod_cast hfill
    linarith
  obtain ⟨Q,⟨hQ,hm⟩,_⟩ := exists_unique_finiteIntervalCutoff_all lam h0 hpi
    ((n : ℝ)/(L : ℝ)) (div_pos hnp hLp) hf
  have hQp : 0 < Q := by
    by_contra ht
    have hz : Q=0 := le_antisymm (le_of_not_gt ht) hQ
    rw [hz,finiteIntervalMass_zero] at hm
    have hp := div_pos hnp hLp
    linarith
  have hmass : (L : ℝ)*finiteIntervalMass lam h0 hpi Q=(n : ℝ) := by
    rw [hm]
    field_simp
  obtain ⟨Y,hY,hy⟩ := exists_finiteInterval_midQuantiles_all lam h0 hpi Q hQ L n hL hmass
  exact ⟨Q,Y,hQp,⟨hQ,hL,hmass,hY,(fun j => (hy j).1),(fun j => (hy j).2)⟩⟩

end
end SixVertex
