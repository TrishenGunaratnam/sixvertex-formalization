import SixVertex.FullLineDensityRadial
import SixVertex.WeightedCorrectedDensity

namespace SixVertex
noncomputable section
open MeasureTheory Set Filter Topology

theorem fullLineDensity_exterior_le_boundary (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (v : ℝ) (hv : v ∉ Icc (-Q) Q) :
    fullLineDensityFunction lam h0 hpi v ≤ fullLineDensityFunction lam h0 hpi Q := by
  apply fullLineDensityFunction_radiallyAntitone lam h0 hhalf hpi Q v
  rw [abs_of_nonneg hQ]
  by_contra hab
  have hh : |v| ≤ Q := (lt_of_not_ge hab).le
  exact hv (abs_le.mp hh)

/-- The actual density defect has exactly the exterior-kernel source. -/
theorem finiteIntervalDensity_defect_source (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (Q u : ℝ) :
    ((fullLineDensityFunction lam h0 hpi-finiteIntervalDensity lam h0 hpi Q)+
      physicalWindowOperator lam h0 hpi Q (fullLineDensityFunction lam h0 hpi-finiteIntervalDensity lam h0 hpi Q)) u=
      ∫ v in (Icc (-Q) Q)ᶜ, (-kernelK lam (u-v))*fullLineDensityFunction lam h0 hpi v := by
  let r := fullLineDensityFunction lam h0 hpi
  let rq := finiteIntervalDensity lam h0 hpi Q
  let A := physicalWindowOperator lam h0 hpi Q
  have heq : rq+A rq=physicalSourceFunction lam h0 hpi := physicalWindowInverse_solves lam h0 hpi Q _
  have hF : (r-rq)+A (r-rq)=r+A r-physicalSourceFunction lam h0 hpi := by
    rw [map_sub,← heq]
    abel
  change ((r-rq)+A (r-rq)) u=_
  rw [hF]
  have hi : Integrable (fun v : ℝ => (-kernelK lam (u-v))*r v) :=
    ((kernelK_integrable lam h0 hpi).neg.comp_sub_left u).mul_bdd r.continuous.aestronglyMeasurable
      (Eventually.of_forall r.norm_coe_le_norm)
  have hfull := congrArg (fun f : BoundedRealFunction => f u) (fullLineDensityFunction_equation lam h0 hpi)
  change r u+boundedConvolutionValue (kernelK lam) r u=physicalSourceFunction lam h0 hpi u at hfull
  rw [boundedConvolutionValue_translated_kernel,physicalSourceFunction_apply] at hfull
  have hwhole : (∫ v : ℝ, (-kernelK lam (u-v))*r v)=r u-kernelS lam u := by
    have hneg : (fun v : ℝ => (-kernelK lam (u-v))*r v)=(fun v : ℝ => -(kernelK lam (u-v)*r v)) := by funext v; ring
    rw [hneg,integral_neg]
    linarith
  have hin : (∫ v in Icc (-Q) Q, (-kernelK lam (u-v))*r v)= -(A r u) := by
    change (∫ v in Icc (-Q) Q, (-kernelK lam (u-v))*r v)= -(physicalWindowOperator lam h0 hpi Q r u)
    rw [physicalWindowOperator_apply,← integral_neg]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => by ring)
  rw [setIntegral_compl measurableSet_Icc hi,hwhole,hin]
  change r u+A r u-physicalSourceFunction lam h0 hpi u=_
  rw [physicalSourceFunction_apply]
  ring

/-- The positive exit kernel loses at most h times the boundary value,
on the entire whole-line extension. -/
theorem finiteIntervalDensity_defect_le_boundary (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q) (u : ℝ) :
    fullLineDensityFunction lam h0 hpi u-finiteIntervalDensity lam h0 hpi Q u ≤
      kernelL1Mass (kernelK lam)*fullLineDensityFunction lam h0 hpi Q := by
  let r := fullLineDensityFunction lam h0 hpi
  let d := r-finiteIntervalDensity lam h0 hpi Q
  let A := physicalWindowOperator lam h0 hpi Q
  let h := kernelL1Mass (kernelK lam)
  let c : BoundedRealFunction := BoundedContinuousFunction.const ℝ (h*r Q)
  have hh : h < 1 := kernelK_L1_mass_lt_one lam h0 hpi
  have hrQ : 0 ≤ r Q := (fullLineDensityFunction_pos lam h0 hhalf hpi Q).le
  have hsource (x : ℝ) : (d+A d) x ≤ c x+A c x := by
    change ((fullLineDensityFunction lam h0 hpi-finiteIntervalDensity lam h0 hpi Q)+
      physicalWindowOperator lam h0 hpi Q (fullLineDensityFunction lam h0 hpi-finiteIntervalDensity lam h0 hpi Q)) x ≤ _
    rw [finiteIntervalDensity_defect_source]
    let k : ℝ → ℝ := fun v => -kernelK lam (x-v)
    have hk : Integrable k := (kernelK_integrable lam h0 hpi).neg.comp_sub_left x
    have hkr : Integrable (fun v => k v*r v) := hk.mul_bdd r.continuous.aestronglyMeasurable
      (Eventually.of_forall r.norm_coe_le_norm)
    have hk0 (v : ℝ) : 0 ≤ k v := neg_nonneg.mpr (kernelK_nonpos lam _ hhalf hpi)
    have hcomp : (∫ v in (Icc (-Q) Q)ᶜ, k v*r v) ≤ ∫ v in (Icc (-Q) Q)ᶜ, r Q*k v := by
      apply integral_mono_ae hkr.integrableOn (hk.const_mul (r Q)).integrableOn
      apply (ae_restrict_iff' measurableSet_Icc.compl).mpr
      apply Eventually.of_forall
      intro v hv
      have hb := fullLineDensity_exterior_le_boundary lam h0 hhalf hpi Q hQ v hv
      exact (mul_le_mul_of_nonneg_left hb (hk0 v)).trans_eq (mul_comm _ _)
    have hmass : (∫ v : ℝ, k v)=h := by
      calc
        _ = ∫ v : ℝ, |kernelK lam (x-v)| := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun v => (abs_of_nonpos (kernelK_nonpos lam _ hhalf hpi)).symm)
        _ = _ := integral_sub_left_eq_self (fun v : ℝ => |kernelK lam v|) volume x
    let a : ℝ := ∫ v in Icc (-Q) Q, k v
    have ha : 0 ≤ a := integral_nonneg (fun v => hk0 v)
    rw [integral_const_mul,setIntegral_compl measurableSet_Icc hk,hmass] at hcomp
    have hc : c x+A c x=h*r Q*(1-a) := by
      change h*r Q+physicalWindowOperator lam h0 hpi Q c x=_
      rw [physicalWindowOperator_apply]
      change h*r Q+(∫ v in Icc (-Q) Q, kernelK lam (x-v)*(h*r Q))=_
      rw [integral_mul_const]
      have hsign : (∫ v in Icc (-Q) Q, kernelK lam (x-v))= -a := by
        dsimp [a,k]
        rw [integral_neg,neg_neg]
      rw [hsign]
      ring
    rw [hc]
    have hpos := mul_nonneg (mul_nonneg hrQ (sub_nonneg.mpr hh.le)) ha
    change (∫ v in (Icc (-Q) Q)ᶜ, k v*r v) ≤ _
    apply hcomp.trans
    change r Q*(h-a) ≤ h*r Q*(1-a)
    nlinarith
  have hc := physicalWindowInverse_le_supersolution lam h0 hhalf hpi Q (d+A d) c hsource u
  rw [physicalWindowInverse_solution_unique lam h0 hpi Q (d+A d) d rfl] at hc
  exact hc

/-- The manuscript's lower density comparison in the negative-kernel
regime, proved from the actual radial density and exit-kernel bound. -/
theorem finiteIntervalDensity_lower_comparison (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (u : ℝ) (hu : u ∈ Icc (-Q) Q) :
    (1-kernelL1Mass (kernelK lam))*fullLineDensityFunction lam h0 hpi u ≤
      finiteIntervalDensity lam h0 hpi Q u := by
  have hd := finiteIntervalDensity_defect_le_boundary lam h0 hhalf hpi Q hQ u
  have hr : fullLineDensityFunction lam h0 hpi Q ≤ fullLineDensityFunction lam h0 hpi u := by
    apply fullLineDensityFunction_radiallyAntitone lam h0 hhalf hpi u Q
    rw [abs_of_nonneg hQ]
    exact abs_le.mpr hu
  have hm := mul_le_mul_of_nonneg_left hr (kernelL1Mass_nonneg (kernelK lam))
  nlinarith

/-- A full-line boundary density threshold implies the actual minimum
density threshold required for uniform reference correction. -/
theorem finiteIntervalDensity_boundary_lower (lam : ℝ) (h0 : 0 < lam)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (Q : ℝ) (hQ : 0 ≤ Q)
    (u : ℝ) (hu : u ∈ Icc (-Q) Q) :
    (1-kernelL1Mass (kernelK lam))*fullLineDensityFunction lam h0 hpi Q ≤
      finiteIntervalDensity lam h0 hpi Q u := by
  have hh := kernelK_L1_mass_lt_one lam h0 hpi
  have hr : fullLineDensityFunction lam h0 hpi Q ≤ fullLineDensityFunction lam h0 hpi u := by
    apply fullLineDensityFunction_radiallyAntitone lam h0 hhalf hpi u Q
    rw [abs_of_nonneg hQ]
    exact abs_le.mpr hu
  exact (mul_le_mul_of_nonneg_left hr (sub_pos.mpr hh).le).trans
    (finiteIntervalDensity_lower_comparison lam h0 hhalf hpi Q hQ u hu)

end
end SixVertex
