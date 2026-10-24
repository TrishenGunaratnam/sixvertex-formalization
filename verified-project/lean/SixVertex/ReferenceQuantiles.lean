import SixVertex.MassParameterContinuity

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

/-- Actual cumulative integral of the inverse-defined finite-interval density. -/
def finiteIntervalCumulative (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q u : ℝ) : ℝ :=
  ∫ v in -Q..u, finiteIntervalDensity lam h0 hpi Q v

theorem finiteIntervalCumulative_hasDerivAt (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q u : ℝ) : HasDerivAt (finiteIntervalCumulative lam h0 hpi Q)
      (finiteIntervalDensity lam h0 hpi Q u) u :=
  ((finiteIntervalDensity lam h0 hpi Q).continuous.integral_hasStrictDerivAt (-Q) u).hasDerivAt

theorem finiteIntervalCumulative_continuous (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) :
    Continuous (finiteIntervalCumulative lam h0 hpi Q) :=
  continuous_iff_continuousAt.mpr (fun u => (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q u).continuousAt)

theorem finiteIntervalCumulative_strictMono (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) :
    StrictMono (finiteIntervalCumulative lam h0 hpi Q) :=
  strictMono_of_hasDerivAt_pos (finiteIntervalCumulative_hasDerivAt lam h0 hpi Q)
    (finiteIntervalDensity_pos lam h0 hhalf hpi Q)

theorem finiteIntervalCumulative_left (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) (Q : ℝ) :
    finiteIntervalCumulative lam h0 hpi Q (-Q)=0 := by simp [finiteIntervalCumulative]

theorem finiteIntervalCumulative_right (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q : ℝ) (hQ : 0 ≤ Q) :
    finiteIntervalCumulative lam h0 hpi Q Q=finiteIntervalMass lam h0 hpi Q := by
  unfold finiteIntervalCumulative finiteIntervalMass
  rw [intervalIntegral.integral_of_le (by linarith),integral_Icc_eq_integral_Ioc]

/-- Every interior cumulative level has one actual reference quantile. -/
theorem exists_unique_finiteIntervalQuantile (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (t : ℝ) (ht : 0 < t) (htmass : t < finiteIntervalMass lam h0 hpi Q) :
    ∃! y : ℝ, y ∈ Ioo (-Q) Q ∧ finiteIntervalCumulative lam h0 hpi Q y=t := by
  have hc := finiteIntervalCumulative_continuous lam h0 hpi Q
  have hm := finiteIntervalCumulative_strictMono lam h0 hhalf hpi Q
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
theorem exists_finiteInterval_midQuantiles (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
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
    (exists_unique_finiteIntervalQuantile lam h0 hhalf hpi Q hQ (target j) (ht j).1 (ht j).2).exists
  let Y : Fin n → ℝ := fun j => Classical.choose (hex j)
  have hs (j : Fin n) : Y j ∈ Ioo (-Q) Q ∧ finiteIntervalCumulative lam h0 hpi Q (Y j)=target j :=
    Classical.choose_spec (hex j)
  have hm := finiteIntervalCumulative_strictMono lam h0 hhalf hpi Q
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

end
end SixVertex
