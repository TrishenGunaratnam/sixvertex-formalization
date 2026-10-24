import SixVertex.DyadicLogEnergy
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal

/-- Absolute Green kernel, with the genuine infinite diagonal value.
Away from the diagonal this is the absolute value of (1.1). -/
def greenAbsolute (d : ℝ) : ℝ≥0∞ :=
  if d=0 then ⊤ else ENNReal.ofReal |(-Real.log d)/(2*Real.pi)|

/-- Ordinary finite signed-measure energy means absolute integrability
against the total variations; the diagonal infinity is not replaced by
the junk value of the real logarithm. No cancellation is permitted. -/
def OrdinaryLogEnergy (μ : SignedMeasure ℂ) : Prop :=
  (∫⁻ p : ℂ × ℂ, greenAbsolute (dist p.1 p.2) ∂μ.totalVariation.prod μ.totalVariation) < ⊤

theorem logSingularity_le_greenAbsolute (d : ℝ) :
    logSingularity d ≤ ENNReal.ofReal (2*Real.pi)*greenAbsolute d := by
  have hc : 0 < 2*Real.pi := by positivity
  by_cases hz : d=0
  · subst d
    have hn : ENNReal.ofReal (2*Real.pi) ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hc
    simp only [logSingularity,greenAbsolute,ite_true]
    rw [ENNReal.mul_top hn]
  · rw [logSingularity,greenAbsolute,if_neg hz,if_neg hz]
    have he : max (-Real.log d) 0 ≤ (2*Real.pi)*|(-Real.log d)/(2*Real.pi)| := by
      rw [abs_div,abs_of_pos hc,mul_div_cancel₀ _ (ne_of_gt hc)]
      exact max_le (le_abs_self _) (abs_nonneg _)
    exact (ENNReal.ofReal_le_ofReal he).trans_eq (ENNReal.ofReal_mul hc.le)

theorem ordinaryLogEnergy_absolute (μ : SignedMeasure ℂ) (hμ : OrdinaryLogEnergy μ) :
    absoluteLogEnergy μ.totalVariation μ.totalVariation < ⊤ := by
  have hbound : absoluteLogEnergy μ.totalVariation μ.totalVariation ≤
      ENNReal.ofReal (2*Real.pi)*(∫⁻ p : ℂ × ℂ,
        greenAbsolute (dist p.1 p.2) ∂μ.totalVariation.prod μ.totalVariation) := by
    calc
      _ ≤ ∫⁻ p : ℂ × ℂ, ENNReal.ofReal (2*Real.pi)*greenAbsolute (dist p.1 p.2)
          ∂μ.totalVariation.prod μ.totalVariation := lintegral_mono (fun p => logSingularity_le_greenAbsolute _)
      _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
  exact hbound.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hμ)

/-- Finite absolute self-energy excludes all atoms, including diagonal
mass that a real-valued log kernel alone would fail to detect. -/
theorem absoluteLogEnergy_no_atoms (μ : Measure ℂ) [SFinite μ]
    (hμ : absoluteLogEnergy μ μ < ⊤) : ∀ z, μ {z}=0 := by
  have hmeas : Measurable (fun p : ℂ × ℂ => logSingularity (dist p.1 p.2)) :=
    logSingularity_measurable.comp (measurable_fst.dist measurable_snd)
  have hae := ae_lt_top hmeas (ne_of_lt hμ)
  have hdiag : μ.prod μ {p : ℂ × ℂ | p.1=p.2}=0 := by
    apply measure_mono_null (t := {p | ¬logSingularity (dist p.1 p.2) < ⊤}) ?_ (ae_iff.mp hae)
    intro p hp
    simp only [mem_setOf_eq] at hp ⊢
    simp [hp,logSingularity]
  intro z
  have hs : μ.prod μ {(z,z)}=0 := by
    apply measure_mono_null (t := {p : ℂ × ℂ | p.1=p.2}) ?_ hdiag
    intro p hp
    have hp' := mem_singleton_iff.mp hp
    subst p
    rfl
  rw [← singleton_prod_singleton,Measure.prod_prod] at hs
  exact (mul_eq_zero.mp hs).elim id id

/-- Lemma 7.6 is a statement about ordinary integrals, not renormalized
or principal-value energy. Compact support is unnecessary for these
forward implications once ordinary absolute Green integrability holds. -/
structure LogIntegrability (μ : SignedMeasure ℂ) : Prop where
  no_atoms : ∀ z, μ.totalVariation {z}=0
  signed_no_atoms : ∀ z, μ {z}=0
  absolute_energy : absoluteLogEnergy μ.totalVariation μ.totalVariation < ⊤
  mixed_energy : ∀ ν : SignedMeasure ℂ, OrdinaryLogEnergy ν →
    absoluteLogEnergy μ.totalVariation ν.totalVariation < ⊤

/-- All clauses of Lemma 7.6: no atoms, finite self absolute logarithmic
energy, and finite mixed absolute logarithmic energy. -/
theorem log_integrability (μ : SignedMeasure ℂ) (hμ : OrdinaryLogEnergy μ) :
    LogIntegrability μ := by
  have he:=ordinaryLogEnergy_absolute μ hμ
  have ha:=absoluteLogEnergy_no_atoms μ.totalVariation he
  exact ⟨ha,fun z => μ.null_of_totalVariation_zero (ha z),he,
    fun ν hν => absoluteLogEnergy_mixed_finite μ.totalVariation ν.totalVariation he
      (ordinaryLogEnergy_absolute ν hν)⟩

/-- The real Green function, used only off the diagonal. -/
def planeGreen (p : ℂ × ℂ) : ℝ := (-Real.log (dist p.1 p.2))/(2*Real.pi)

theorem greenAbsolute_measurable : Measurable greenAbsolute := by
  apply Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const
  exact ENNReal.measurable_ofReal.comp (continuous_abs.measurable.comp
    (Real.measurable_log.neg.div_const (2*Real.pi)))

theorem planeGreen_measurable : Measurable planeGreen :=
  (((measurable_fst.dist measurable_snd).log.neg).div_const _)

/-- This equivalence checks the ordinary-integral convention: finite
extended absolute Green integral is ordinary Bochner integrability
away from a null diagonal. The zero assigned to `Real.log 0` cannot
make an atomic measure pass the condition. -/
theorem finite_extended_green_iff (m : Measure (ℂ × ℂ)) :
    (∫⁻ p, greenAbsolute (dist p.1 p.2) ∂m) < ⊤ ↔
      m {p : ℂ × ℂ | p.1=p.2}=0 ∧ Integrable planeGreen m := by
  have hmeas : Measurable (fun p : ℂ × ℂ => greenAbsolute (dist p.1 p.2)) :=
    greenAbsolute_measurable.comp (measurable_fst.dist measurable_snd)
  have hcongr : (∀ᵐ p : ℂ × ℂ ∂m, p.1≠p.2) →
      (fun p : ℂ × ℂ => greenAbsolute (dist p.1 p.2)) =ᵐ[m]
        (fun p => ENNReal.ofReal ‖planeGreen p‖) := by
    intro ha
    filter_upwards [ha] with p hp
    simp only [greenAbsolute,planeGreen,if_neg (dist_ne_zero.mpr hp),Real.norm_eq_abs]
  constructor
  · intro h
    have ha : ∀ᵐ p : ℂ × ℂ ∂m, p.1≠p.2 := by
      filter_upwards [ae_lt_top hmeas (ne_of_lt h)] with p hp
      intro heq
      simp [heq,greenAbsolute] at hp
    have hd : m {p : ℂ × ℂ | p.1=p.2}=0 := by
      simpa only [ae_iff,not_not] using ha
    refine ⟨hd,planeGreen_measurable.aestronglyMeasurable,?_⟩
    rw [hasFiniteIntegral_iff_norm]
    exact (lintegral_congr_ae (hcongr ha)) ▸ h
  · rintro ⟨hd,hi⟩
    have ha : ∀ᵐ p : ℂ × ℂ ∂m, p.1≠p.2 := by
      simpa only [ae_iff,not_not] using hd
    rw [lintegral_congr_ae (hcongr ha)]
    exact (hasFiniteIntegral_iff_norm _).mp hi.hasFiniteIntegral

end
end SixVertex
