import SixVertex.RootSeeds

namespace SixVertex
open Filter Topology

noncomputable def phaseEnd (θ : ℝ) : ℝ := 1/2-θ/Real.pi

theorem arctan_cot_physical (θ : ℝ) (h0 : 0 < θ) (hpi : θ < Real.pi) :
    Real.arctan (Real.cos θ/Real.sin θ) = Real.pi/2-θ := by
  have he : Real.cos θ/Real.sin θ = Real.tan (Real.pi/2-θ) := by
    rw [Real.tan_pi_div_two_sub,Real.tan_eq_sin_div_cos,inv_div]
  rw [he,Real.arctan_tan (by linarith) (by linarith)]

/-- The endpoint limit is joint in the physical parameter and real argument.
This is the uniform-in-parameter germ required by the escape argument. -/
theorem barePhase_tendsto_atTop {A : Type*} (l : Filter A) (θ u : A → ℝ) (θ0 : ℝ)
    (h0 : 0 < θ0) (hpi : θ0 < Real.pi) (hθ : Tendsto θ l (𝓝 θ0)) (hu : Tendsto u l atTop) :
    Tendsto (fun a => barePhase (θ a) (u a)) l (𝓝 (phaseEnd θ0)) := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hc := ((Real.continuous_cos.tendsto θ0).comp hθ).div
    ((Real.continuous_sin.tendsto θ0).comp hθ) hs
  have ht := hc.mul (tanh_tendsto_atTop.comp hu)
  have ha := ((Real.continuous_arctan.tendsto ((Real.cos θ0/Real.sin θ0)*1)).comp ht).div_const Real.pi
  simp only [mul_one,arctan_cot_physical θ0 h0 hpi] at ha
  have he : (Real.pi/2-θ0)/Real.pi = phaseEnd θ0 := by
    unfold phaseEnd
    field_simp
    <;> ring
  rw [he] at ha
  exact ha.congr (fun a => by
    simp only [Function.comp_def,Pi.div_apply,Real.tanh_eq_sinh_div_cosh,barePhase])

theorem barePhase_tendsto_atBot {A : Type*} (l : Filter A) (θ u : A → ℝ) (θ0 : ℝ)
    (h0 : 0 < θ0) (hpi : θ0 < Real.pi) (hθ : Tendsto θ l (𝓝 θ0)) (hu : Tendsto u l atBot) :
    Tendsto (fun a => barePhase (θ a) (u a)) l (𝓝 (-phaseEnd θ0)) := by
  have ht := barePhase_tendsto_atTop l θ (fun a => -u a) θ0 h0 hpi hθ
    (tendsto_neg_atBot_atTop.comp hu)
  exact ht.neg.congr (fun a => by rw [barePhase_neg,neg_neg])

theorem countingS_tendsto_atTop {A : Type*} (l : Filter A) (lam u : A → ℝ) (lam0 : ℝ)
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam l (𝓝 lam0)) (hu : Tendsto u l atTop) :
    Tendsto (fun a => countingS (lam a) (u a)) l (𝓝 (phaseEnd (lam0/2))) :=
  barePhase_tendsto_atTop l (fun a => lam a/2) u (lam0/2) (by linarith)
    (by linarith [Real.pi_pos]) (hLam.div_const 2) hu

theorem countingTheta_tendsto_atTop {A : Type*} (l : Filter A) (lam u : A → ℝ) (lam0 : ℝ)
    (h0 : 0 < lam0) (hpi : lam0 < Real.pi) (hLam : Tendsto lam l (𝓝 lam0)) (hu : Tendsto u l atTop) :
    Tendsto (fun a => countingTheta (lam a) (u a)) l (𝓝 (phaseEnd lam0)) :=
  barePhase_tendsto_atTop l lam u lam0 h0 hpi hLam hu

end SixVertex
