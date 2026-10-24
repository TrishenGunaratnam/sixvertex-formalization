import SixVertex.KernelTailBounds

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem integral_exp_neg_two_Ioi (u : ℝ) :
    (∫ v in Ioi u, Real.exp (-2*v))=Real.exp (-2*u)/2 := by
  have h := integral_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) u
  convert h using 1 <;> ring

/-- Pointwise exponential envelopes give actual two-sided tail bounds. -/
theorem kernelTail_exponential_bounds (q : ℝ → ℝ) (hq : Integrable q) (c C : ℝ)
    (hlo : ∀ v, 0 ≤ v → c*Real.exp (-2*v) ≤ q v)
    (hhi : ∀ v, 0 ≤ v → q v ≤ C*Real.exp (-2*v)) (u : ℝ) (hu : 0 ≤ u) :
    (c/2)*Real.exp (-2*u) ≤ kernelTail q u ∧ kernelTail q u ≤ (C/2)*Real.exp (-2*u) := by
  have he : IntegrableOn (fun v : ℝ => Real.exp (-2*v)) (Ioi u) :=
    integrableOn_exp_mul_Ioi (a := (-2 : ℝ)) (by norm_num) u
  have hloint : (∫ v in Ioi u, c*Real.exp (-2*v)) ≤ kernelTail q u := by
    apply integral_mono_ae (he.const_mul c) hq.integrableOn
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hlo v (hu.trans hv.le)
  have hhiint : kernelTail q u ≤ ∫ v in Ioi u, C*Real.exp (-2*v) := by
    apply integral_mono_ae hq.integrableOn (he.const_mul C)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with v hv
    exact hhi v (hu.trans hv.le)
  rw [integral_const_mul,integral_exp_neg_two_Ioi] at hloint hhiint
  constructor <;> linarith

theorem kernelTail_antitone (q : ℝ → ℝ) (hq : Integrable q) (hpos : ∀ v, 0 ≤ q v) :
    Antitone (kernelTail q) := by
  intro u v huv
  exact setIntegral_mono_set hq.integrableOn (Eventually.of_forall (fun x => hpos x))
    (Eventually.of_forall (fun x (hx : x ∈ Ioi v) => show x ∈ Ioi u from lt_of_le_of_lt huv hx))

/-- Relative exponential tail decay, uniformly in both nonnegative
arguments. Its constants come from the two actual pointwise envelopes. -/
theorem kernelTail_shift_exponential (q : ℝ → ℝ) (hq : Integrable q) (c C : ℝ) (hc : 0 < c)
    (hC : 0 ≤ C) (hlo : ∀ v, 0 ≤ v → c*Real.exp (-2*v) ≤ q v)
    (hhi : ∀ v, 0 ≤ v → q v ≤ C*Real.exp (-2*v)) (u t : ℝ) (hu : 0 ≤ u) (ht : 0 ≤ t) :
    kernelTail q (u+t) ≤ (C/c)*Real.exp (-2*t)*kernelTail q u := by
  have hb0 := (kernelTail_exponential_bounds q hq c C hlo hhi u hu).1
  have hb1 := (kernelTail_exponential_bounds q hq c C hlo hhi (u+t) (add_nonneg hu ht)).2
  have he : Real.exp (-2*(u+t))=Real.exp (-2*t)*Real.exp (-2*u) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [he] at hb1
  have hm := mul_le_mul_of_nonneg_left hb0 (mul_nonneg (div_nonneg hC hc.le) (Real.exp_pos (-2*t)).le)
  have hi : (C/c)*Real.exp (-2*t)*((c/2)*Real.exp (-2*u))=
      (C/2)*(Real.exp (-2*t)*Real.exp (-2*u)) := by field_simp [hc.ne']
  rw [hi] at hm
  exact hb1.trans hm

end
end SixVertex
