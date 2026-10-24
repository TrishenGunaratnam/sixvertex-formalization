import SixVertex.FreeFermionRoots

namespace SixVertex
open Filter Topology
open scoped ContDiff Matrix

/-- Joint real analyticity in phase parameter and spatial argument, on the
physical sine-nonzero domain. -/
theorem contDiffAt_barePhase_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (θ u : E → ℝ) (x : E) (hθ : ContDiffAt ℝ ω θ x) (hu : ContDiffAt ℝ ω u x)
    (hsin : Real.sin (θ x) ≠ 0) : ContDiffAt ℝ ω (fun z => barePhase (θ z) (u z)) x := by
  have hc := Real.contDiff_cos.contDiffAt.comp x hθ
  have hs := Real.contDiff_sin.contDiffAt.comp x hθ
  have hsh := Real.contDiff_sinh.contDiffAt.comp x hu
  have hch := Real.contDiff_cosh.contDiffAt.comp x hu
  have hm := (hc.div hs hsin).mul (hsh.div hch (Real.cosh_pos (u x)).ne')
  exact (Real.contDiff_arctan.contDiffAt.comp x hm).div_const Real.pi

noncomputable def parameterCountingSystem (b : ℕ → ℝ) (L n : ℕ)
    (p : ℝ × (Fin n → ℝ)) : Fin n → ℝ := countingSystem p.1 b L p.2

theorem contDiffAt_parameterCountingSystem (b : ℕ → ℝ) (L n : ℕ) (lam : ℝ)
    (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    ContDiffAt ℝ ω (parameterCountingSystem b L n) (lam,Y) := by
  have hfst : ContDiffAt ℝ ω (fun p : ℝ × (Fin n → ℝ) => p.1) (lam,Y) := contDiffAt_fst
  have heval (j : Fin n) : ContDiffAt ℝ ω (fun p : ℝ × (Fin n → ℝ) => p.2 j) (lam,Y) :=
    (contDiff_apply ℝ (fun _ : Fin n => ℝ) j).contDiffAt.comp (lam,Y) contDiffAt_snd
  apply contDiffAt_pi.mpr
  intro j
  apply ContDiffAt.sub
  · apply ContDiffAt.sum
    intro a ha
    exact contDiffAt_barePhase_comp _ _ (lam,Y) (hfst.div_const 2) ((heval j).sub contDiffAt_const)
      (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  · apply ContDiffAt.sum
    intro i hi
    exact contDiffAt_barePhase_comp _ _ (lam,Y) hfst ((heval j).sub (heval i))
      (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'

/-- The root-coordinate partial derivative of the joint parameter map is
exactly the already verified Gaudin Jacobian. -/
theorem parameterCountingSystem_partial (b : ℕ → ℝ) (L n : ℕ) (lam : ℝ)
    (Y : Fin n → ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    fderiv ℝ (parameterCountingSystem b L n) (lam,Y) ∘L
      ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ) = gaudinCLM lam b L Y := by
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hc := contDiffAt_parameterCountingSystem b L n lam Y h0 hpi
  have hi : HasFDerivAt (fun X : Fin n → ℝ => (lam,X))
      (ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)) Y := by
    exact hasFDerivAt_prodMk_right lam Y
  have h := hc.differentiableAt hn |>.hasFDerivAt |>.comp Y hi
  exact h.unique (hasFDerivAt_countingSystem lam b L Y h0 hpi)

/-- The parameter-continuation step used in Lemma 3.1, with ordering retained.
This is local in lambda; it does not assume or assert global compactness. -/
theorem exists_analytic_parameter_root_branch {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (Y : Fin n → ℝ) (twist : ℝ)
    (hY : ConsecutiveRoots lam b L Y twist) (hdet : (gaudinMatrix lam b L Y).det ≠ 0) :
    ∃ ψ : ℝ → Fin n → ℝ, ψ lam = Y ∧ AnalyticAt ℝ ψ lam ∧
      ∀ᶠ a in 𝓝 lam, 0 < a ∧ a < Real.pi ∧ ConsecutiveRoots a b L (ψ a) twist ∧ AnalyticAt ℝ ψ a := by
  classical
  let F := parameterCountingSystem b L n
  have hc : ContDiffAt ℝ ω F (lam,Y) := contDiffAt_parameterCountingSystem b L n lam Y h0 hpi
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hi : (fderiv ℝ F (lam,Y) ∘L ContinuousLinearMap.inr ℝ ℝ (Fin n → ℝ)).IsInvertible := by
    rw [parameterCountingSystem_partial b L n lam Y h0 hpi]
    have hbij := gaudinCLM_bijective lam b L Y hdet
    refine ⟨ContinuousLinearEquiv.ofBijective (gaudinCLM lam b L Y)
      (LinearMap.ker_eq_bot.mpr hbij.1) (LinearMap.range_eq_top.mpr hbij.2),?_⟩
    exact ContinuousLinearEquiv.coe_ofBijective _ _ _
  let ψ := hc.implicitFunction hn hi
  have hbase : ψ lam = Y := hc.implicitFunction_apply_self hn hi
  have ha : ContDiffAt ℝ ω ψ lam := hc.contDiffAt_implicitFunction hn hi
  have heq : ∀ᶠ a in 𝓝 lam, countingSystem a b L (ψ a) = countingTarget n twist := by
    have he := hc.eventually_apply_implicitFunction hn hi
    exact he.mono (fun a hae => hae.trans hY.2)
  have hmono : ∀ᶠ a in 𝓝 lam, StrictMono (ψ a) := by
    change ∀ᶠ a in 𝓝 lam, ∀ i j : Fin n, i < j → ψ a i < ψ a j
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    by_cases hij : i < j
    · have hi := (continuous_apply i).continuousAt.comp ha.continuousAt
      have hj := (continuous_apply j).continuousAt.comp ha.continuousAt
      have hlt : ψ lam i < ψ lam j := by rw [hbase]; exact hY.1 hij
      exact (hi.eventually_lt hj hlt).mono (fun a hh _ => hh)
    · exact Eventually.of_forall (fun _ hh => False.elim (hij hh))
  have hnear := ha.eventually (by simp)
  refine ⟨ψ,hbase,ha.analyticAt,?_⟩
  filter_upwards [heq,hmono,hnear,lt_mem_nhds h0,gt_mem_nhds hpi] with a he hm haa hapos hapi
  exact ⟨hapos,hapi,⟨hm,he⟩,haa.analyticAt⟩

end SixVertex
