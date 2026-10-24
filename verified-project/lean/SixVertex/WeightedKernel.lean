import SixVertex.KernelDerivatives
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace SixVertex
noncomputable section
open MeasureTheory Filter Topology Set

theorem integrable_exp_neg_abs : Integrable (fun u : ℝ => Real.exp (-|u|)) := by
  have hl : IntegrableOn (fun u : ℝ => Real.exp (-|u|)) (Iic 0) :=
    (integrableOn_exp_Iic 0).congr_fun (fun u hu => by rw [abs_of_nonpos hu,neg_neg]) measurableSet_Iic
  have hr : IntegrableOn (fun u : ℝ => Real.exp (-|u|)) (Ioi 0) :=
    (integrableOn_exp_neg_Ioi 0).congr_fun (fun u hu => by rw [abs_of_pos hu]) measurableSet_Ioi
  rw [← integrableOn_univ,← Iic_union_Ioi (a := (0 : ℝ)),integrableOn_union]
  exact ⟨hl,hr⟩

/-- A single integrable majorant controls all exponential weights a <= 1. -/
theorem exponential_weight_majorant (k : ℝ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ u, |k u| ≤ C*Real.exp (-2*|u|)) (a : ℝ) (ha : a ≤ 1) (u : ℝ) :
    |Real.exp (a*|u|)*k u| ≤ C*Real.exp (-|u|) := by
  rw [abs_mul,abs_of_pos (Real.exp_pos _)]
  calc
    _ ≤ Real.exp (a*|u|)*(C*Real.exp (-2*|u|)) :=
      mul_le_mul_of_nonneg_left (hdecay u) (Real.exp_pos _).le
    _ = C*(Real.exp (a*|u|)*Real.exp (-2*|u|)) := by ring
    _ = C*Real.exp ((a-2)*|u|) := by rw [← Real.exp_add]; congr 2 <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by nlinarith [abs_nonneg u])) hC

theorem integrable_exponential_weight (k : ℝ → ℝ) (hk : Continuous k) (C : ℝ) (hC : 0 ≤ C)
    (hdecay : ∀ u, |k u| ≤ C*Real.exp (-2*|u|)) (a : ℝ) (ha : a ≤ 1) :
    Integrable (fun u : ℝ => Real.exp (a*|u|)*k u) := by
  apply (integrable_exp_neg_abs.const_mul C).mono' (by fun_prop)
  apply Eventually.of_forall
  intro u
  change |Real.exp (a*|u|)*k u| ≤ C*Real.exp (-|u|)
  exact exponential_weight_majorant k C hC hdecay a ha u

def weightedKernelAbs (lam a u : ℝ) : ℝ := Real.exp (a*|u|)*|kernelK lam u|
def weightedKernelMass (lam a : ℝ) : ℝ := ∫ u : ℝ, weightedKernelAbs lam a u

theorem weightedKernelAbs_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (a : ℝ) (ha : a ≤ 1) : Integrable (weightedKernelAbs lam a) := by
  have hk : Continuous (kernelK lam) :=
    continuous_phaseDensity lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hi:=integrable_exponential_weight (kernelK lam) hk (2/(Real.pi*(Real.sin lam)^2))
    (by positivity) (fun u => kernelK_exponential_bound lam u h0 hpi) a ha
  change Integrable (fun u : ℝ => Real.exp (a*|u|)*|kernelK lam u|)
  simpa only [abs_mul,abs_of_pos (Real.exp_pos _)] using hi.abs

/-- Continuity of the weighted L1 mass is proved by dominated convergence,
not inferred from pointwise convergence of the weights. -/
theorem weightedKernelMass_continuousAt_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ContinuousAt (weightedKernelMass lam) 0 := by
  have hk : Continuous (kernelK lam) :=
    continuous_phaseDensity lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  let C : ℝ := 2/(Real.pi*(Real.sin lam)^2)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hparam : ∀ᶠ a : ℝ in 𝓝 0, a ≤ 1 :=
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)).mono (fun a ha => ha.le)
  apply continuousAt_of_dominated (bound := fun u : ℝ => C*Real.exp (-|u|))
  · exact Eventually.of_forall (fun a => by
      change AEStronglyMeasurable (fun u : ℝ => Real.exp (a*|u|)*|kernelK lam u|)
      fun_prop)
  · filter_upwards [hparam] with a ha
    exact Eventually.of_forall (fun u => by
      simpa only [weightedKernelAbs,Real.norm_eq_abs,abs_mul,abs_abs,abs_of_pos (Real.exp_pos _)] using
        exponential_weight_majorant (kernelK lam) C hC (fun u => kernelK_exponential_bound lam u h0 hpi) a ha u)
  · exact integrable_exp_neg_abs.const_mul C
  · exact Eventually.of_forall (fun u => by
      change ContinuousAt (fun a : ℝ => Real.exp (a*|u|)*|kernelK lam u|) 0
      fun_prop)

theorem weightedKernelMass_zero (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    weightedKernelMass lam 0=|1-2*lam/Real.pi| := by
  unfold weightedKernelMass
  simp only [weightedKernelAbs,zero_mul,Real.exp_zero,one_mul]
  exact integral_abs_kernelK lam h0 hpi

/-- The small positive weight asserted at the start of Section 3 is
constructed from continuity and the strict unweighted contraction. -/
theorem exists_positive_weight_kernel_contraction (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ∃ a : ℝ, 0 < a ∧ a < 1 ∧ Integrable (weightedKernelAbs lam a) ∧ weightedKernelMass lam a < 1 := by
  have hz : weightedKernelMass lam 0 < 1 := by
    simpa only [weightedKernelMass,weightedKernelAbs,zero_mul,Real.exp_zero,one_mul] using
      kernelK_L1_mass_lt_one lam h0 hpi
  have hnear : ∀ᶠ a : ℝ in 𝓝 0, weightedKernelMass lam a < 1 :=
    (weightedKernelMass_continuousAt_zero lam h0 hpi).eventually (gt_mem_nhds hz)
  obtain ⟨d,hd,hall⟩ := Metric.eventually_nhds_iff.mp hnear
  let a : ℝ := (min d 1)/2
  have ha : 0 < a := by dsimp [a]; positivity
  have had : a < d := by have h:=min_le_left d 1; dsimp [a]; linarith
  have ha1 : a < 1 := by have h:=min_le_right d 1; dsimp [a]; linarith
  refine ⟨a,ha,ha1,weightedKernelAbs_integrable lam h0 hpi a ha1.le,?_⟩
  apply hall
  simpa only [Real.dist_eq,sub_zero,abs_of_pos ha] using had

theorem weightedKernelPrime_integrable (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (a : ℝ) (ha : a ≤ 1) : Integrable (fun u : ℝ => Real.exp (a*|u|)*kernelKPrime lam u) := by
  have hk : Continuous (kernelKPrime lam) :=
    continuous_phaseDensityPrime lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  exact integrable_exponential_weight (kernelKPrime lam) hk
    ((2/(Real.sin lam)^2)*(2/(Real.pi*(Real.sin lam)^2))) (by positivity)
    (fun u => kernelKPrime_exponential_bound lam u h0 hpi) a ha

end
end SixVertex
