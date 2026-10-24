import SixVertex.DensityTailComparison
import SixVertex.FiniteIntervalMassBounds

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter Topology

/-- An even integrable profile has equal left and right exterior tails. -/
theorem even_integral_exterior_eq_two_tail (f : ℝ → ℝ) (hf : Integrable f)
    (heven : ∀ u, f (-u)=f u) (Q : ℝ) (hQ : 0 ≤ Q) :
    (∫ u in (Icc (-Q) Q)ᶜ, f u)=2*kernelTail f Q := by
  have hl : (∫ u in Iio (-Q), f u)=kernelTail f Q := by
    rw [← integral_indicator measurableSet_Iio]
    have ht := integral_sub_left_eq_self ((Iio (-Q)).indicator f) volume 0
    simp only [zero_sub] at ht
    rw [← ht]
    have he : (fun u => (Iio (-Q)).indicator f (-u))=(Ioi Q).indicator f := by
      funext u
      by_cases hu : Q < u
      · have hn : -u < -Q := neg_lt_neg hu
        simp [Set.indicator,hu,hn,heven]
      · have hn : ¬-u < -Q := by linarith
        simp [Set.indicator,hu,hn]
    rw [he,integral_indicator measurableSet_Ioi]
    rfl
  have he : ((Icc (-Q) Q)ᶜ).indicator f=(Iio (-Q)).indicator f+(Ioi Q).indicator f := by
    funext u
    by_cases hu : u ∈ Icc (-Q) Q
    · have hlo : ¬u < -Q := by linarith [hu.1]
      have hhi : ¬Q < u := by linarith [hu.2]
      simp [Set.indicator,hu,hlo,hhi]
    · have hh : u < -Q ∨ Q < u := by simpa only [mem_Icc,not_and_or,not_le] using hu
      rcases hh with hlo | hhi
      · have hn : ¬Q < u := by linarith
        simp [Set.indicator,hu,hlo,hn]
      · have hn : ¬u < -Q := by linarith
        simp [Set.indicator,hu,hhi,hn]
  rw [← integral_indicator measurableSet_Icc.compl,he]
  change (∫ u : ℝ, (Iio (-Q)).indicator f u+(Ioi Q).indicator f u)=_
  rw [integral_add (hf.indicator measurableSet_Iio) (hf.indicator measurableSet_Ioi),
    integral_indicator measurableSet_Iio,integral_indicator measurableSet_Ioi,hl]
  change kernelTail f Q+kernelTail f Q=2*kernelTail f Q
  ring

/-- The actual filling deficit and boundary density are comparable
uniformly in the cutoff, independently of a Fourier closed form. -/
theorem exists_finiteIntervalMass_deficit_boundary_comparison (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ Q : ℝ, 0 ≤ Q →
      c*fullLineDensityFunction lam h0 hpi Q ≤ 1/2-finiteIntervalMass lam h0 hpi Q ∧
      1/2-finiteIntervalMass lam h0 hpi Q ≤ C*fullLineDensityFunction lam h0 hpi Q := by
  obtain ⟨c,C,hc,hC,hbound⟩ := exists_fullLineDensity_tail_comparison lam hhalf hpi
  let d : ℝ := 2*(1-lam/Real.pi)
  have hd : 0 < d := mul_pos (by norm_num) (sub_pos.mpr ((div_lt_one Real.pi_pos).mpr hpi))
  refine ⟨2*c,2*C/d,mul_pos (by norm_num) hc,div_pos (mul_pos (by norm_num) hC) hd,?_⟩
  intro Q hQ
  have he : fullLineDensityExteriorMass lam h0 hpi Q=
      2*kernelTail (fun u => fullLineDensityFunction lam h0 hpi u) Q := by
    exact even_integral_exterior_eq_two_tail _ (fullLineDensityFunction_integrable lam h0 hpi)
      (fullLineDensityFunction_radiallyAntitone lam h0 hhalf.le hpi).even Q hQ
  have hb := finiteIntervalMass_deficit_bounds lam h0 hhalf.le hpi Q
  rw [he] at hb
  have ht := hbound Q hQ
  constructor
  · nlinarith only [hb.1,ht.1]
  · have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht.2 (by norm_num : (0 : ℝ) ≤ 2)) hd.le
    apply hb.2.trans
    exact hh.trans_eq (by dsimp [d]; ring)

/-- Divergence of the number of missing half-filled roots forces the
actual boundary density to diverge after multiplication by chain length. -/
theorem boundary_density_dense_of_missing_mass {ι : Type*} (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 < lam) (hpi : lam < Real.pi) (l : Filter ι) (L : ι → ℕ) (Q : ι → ℝ)
    (hQ : ∀ i, 0 ≤ Q i)
    (hmissing : Tendsto (fun i => (L i : ℝ)*(1/2-finiteIntervalMass lam h0 hpi (Q i))) l atTop) :
    Tendsto (fun i => (L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) l atTop := by
  obtain ⟨c,C,_,hC,hbound⟩ := exists_finiteIntervalMass_deficit_boundary_comparison lam h0 hhalf hpi
  apply tendsto_atTop.mpr
  intro a
  filter_upwards [hmissing.eventually (eventually_ge_atTop (C*a))] with i hi
  have hh := mul_le_mul_of_nonneg_left (hbound (Q i) (hQ i)).2 (Nat.cast_nonneg (L i))
  have hprod : C*a ≤ C*((L i : ℝ)*fullLineDensityFunction lam h0 hpi (Q i)) := by nlinarith only [hi,hh]
  exact (mul_le_mul_iff_right₀ hC).mp hprod

end
end SixVertex
