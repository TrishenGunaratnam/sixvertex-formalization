import SixVertex.FiniteGaudin
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace SixVertex

open scoped ContDiff

open scoped Matrix

open Filter Topology

theorem gaudinCLM_bijective {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hdet : (gaudinMatrix lam b L Y).det ≠ 0) :
    Function.Bijective (gaudinCLM lam b L Y) := by
  have hunit : IsUnit (gaudinMatrix lam b L Y) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
  have hi : Function.Injective (gaudinCLM lam b L Y) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hunit
  exact ⟨hi, LinearMap.injective_iff_surjective.mp hi⟩

theorem contDiff_countingTarget (n : ℕ) : ContDiff ℝ ω (countingTarget n) := by
  apply contDiff_pi.mpr
  intro j
  exact contDiff_const.add (contDiff_id.div_const Real.pi)

theorem hasDerivAt_countingTarget (n : ℕ) (twist : ℝ) :
    HasDerivAt (countingTarget n) (fun _ => 1/Real.pi) twist := by
  apply hasDerivAt_pi.mpr
  intro j
  simpa only [countingTarget, id_eq] using
    ((hasDerivAt_id twist).div_const Real.pi).const_add
      ((j.val : ℝ)+1-((n : ℝ)+1)/2)

/-- Differentiation of any local real root branch gives G dY/dt = 1/pi. -/
theorem counting_branch_derivative {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (ψ : ℝ → Fin n → ℝ) (twist : ℝ)
    (hψ : DifferentiableAt ℝ ψ twist)
    (heq : ∀ᶠ t in 𝓝 twist, countingSystem lam b L (ψ t) = countingTarget n t) :
    gaudinMatrix lam b L (ψ twist) *ᵥ deriv ψ twist = fun _ => 1/Real.pi := by
  have hd := (hasFDerivAt_countingSystem lam b L (ψ twist) h0 hpi).comp_hasDerivAt twist hψ.hasDerivAt
  have hg : countingTarget n =ᶠ[𝓝 twist] (countingSystem lam b L ∘ ψ) :=
    heq.mono (fun _ h => h.symm)
  have ht := hd.congr_of_eventuallyEq hg
  exact ht.unique (hasDerivAt_countingTarget n twist)

/-- A nonsingular counting Jacobian gives a REAL ANALYTIC local root
branch. Ordering is preserved, and the twist derivative is proved at
every sufficiently nearby parameter, not only at the base point. -/
theorem exists_analytic_root_branch {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (Y : Fin n → ℝ) (twist : ℝ)
    (hY : ConsecutiveRoots lam b L Y twist) (hdet : (gaudinMatrix lam b L Y).det ≠ 0) :
    ∃ ψ : ℝ → Fin n → ℝ, ψ twist = Y ∧ AnalyticAt ℝ ψ twist ∧
      ∀ᶠ t in 𝓝 twist, ConsecutiveRoots lam b L (ψ t) t ∧ AnalyticAt ℝ ψ t ∧
        gaudinMatrix lam b L (ψ t) *ᵥ deriv ψ t = (fun _ => 1/Real.pi) := by
  classical
  have hbij := gaudinCLM_bijective lam b L Y hdet
  let e : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    ContinuousLinearEquiv.ofBijective (gaudinCLM lam b L Y)
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2)
  have he : (e : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) = gaudinCLM lam b L Y :=
    ContinuousLinearEquiv.coe_ofBijective _ _ _
  have hd : HasFDerivAt (countingSystem lam b L) (e : _ →L[ℝ] _) Y := by
    rw [he]
    exact hasFDerivAt_countingSystem lam b L Y h0 hpi
  have hc : ContDiffAt ℝ ω (countingSystem lam b L) Y :=
    (contDiff_countingSystem (n := n) lam b L).contDiffAt
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  let inv := hc.localInverse hd hn
  let ψ : ℝ → Fin n → ℝ := fun t => inv (countingTarget n t)
  have htarget : countingTarget n twist = countingSystem lam b L Y := hY.2.symm
  have hbase : ψ twist = Y := by
    dsimp [ψ, inv]
    rw [htarget, hc.localInverse_apply_image hd hn]
  have hInv : ContDiffAt ℝ ω inv (countingTarget n twist) := by
    rw [htarget]
    exact hc.to_localInverse hd hn
  have hψ : ContDiffAt ℝ ω ψ twist :=
    hInv.comp twist (contDiff_countingTarget n).contDiffAt
  have htend : Tendsto (countingTarget n) (𝓝 twist) (𝓝 (countingSystem lam b L Y)) := by
    rw [← htarget]
    exact (contDiff_countingTarget n).continuous.continuousAt.tendsto
  have heq : ∀ᶠ t in 𝓝 twist, countingSystem lam b L (ψ t) = countingTarget n t :=
    htend.eventually (hc.hasStrictFDerivAt' hd hn).eventually_right_inverse
  have hmono : ∀ᶠ t in 𝓝 twist, StrictMono (ψ t) := by
    change ∀ᶠ t in 𝓝 twist, ∀ i j : Fin n, i < j → ψ t i < ψ t j
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i < j
    · have hi := (continuous_apply i).continuousAt.comp hψ.continuousAt
      have hj := (continuous_apply j).continuousAt.comp hψ.continuousAt
      have hlt : ψ twist i < ψ twist j := by rw [hbase]; exact hY.1 hij
      exact (hi.eventually_lt hj hlt).mono (fun t ht _ => ht)
    · exact Eventually.of_forall (fun _ ht => False.elim (hij ht))
  have heqgerm := eventually_eventually_nhds.mpr heq
  have hψnear : ∀ᶠ t in 𝓝 twist, ContDiffAt ℝ ω ψ t := hψ.eventually (by simp)
  refine ⟨ψ, hbase, hψ.analyticAt, ?_⟩
  filter_upwards [heq, heqgerm, hmono, hψnear] with t ht hg hm ha
  exact ⟨⟨hm, ht⟩, ha.analyticAt,
    counting_branch_derivative lam b L h0 hpi ψ t (ha.differentiableAt hn) hg⟩

end SixVertex
