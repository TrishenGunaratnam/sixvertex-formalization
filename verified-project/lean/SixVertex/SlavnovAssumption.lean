import SixVertex.ScalarProductSetup

namespace SixVertex

/-- The eigenvalue before imposing the Bethe equations. Root coordinates are
independent complex variables, so these derivatives are not branch derivatives. -/
noncomputable def independentBetheTau {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (X : Fin n → ℂ) (twist : ℝ) (u : ℂ) : ℂ :=
  Complex.exp (Complex.I*twist)*vacuumA (Complex.I*lam) (fun a => (b a : ℂ)) u L *
    (∏ j, betheF (Complex.I*lam) (X j-u)) +
  Complex.exp (-Complex.I*twist)*vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) u L *
    (∏ j, betheF (Complex.I*lam) (u-X j))

noncomputable def independentRootDerivative {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (u : ℂ) (j : Fin n) : ℂ :=
  deriv (fun z => independentBetheTau lam b L (Function.update (fun k => (Y k : ℂ)) j z) twist u) (Y j)

/-- User-authorized external assumption: exactly the derivative-over-Cauchy
Slavnov identity, cross-multiplied on its generic domain. -/
def SlavnovIdentity {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) : Prop :=
  ∀ U : Fin n → ℂ, (∀ k, SourceRegular lam b L Y (U k)) →
    (∀ j k, Complex.sinh (U k-Y j) ≠ 0) →
    algebraicScalarProduct lam b L Y U * (scalarCauchy Y U).det =
      Complex.exp (-((n : ℂ)*Complex.I*twist)) *
      (∏ j, vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L) *
      (Matrix.of (fun j k => independentRootDerivative lam b L Y twist (U k) j)).det

@[simp] theorem hyperbolicCot_neg (z : ℂ) : hyperbolicCot (-z) = -hyperbolicCot z := by
  simp [hyperbolicCot, Complex.cosh_neg, Complex.sinh_neg, div_neg]

theorem hasDerivAt_betheF (t z : ℂ) (hz : Complex.sinh z ≠ 0)
    (hzt : Complex.sinh (z+t) ≠ 0) :
    HasDerivAt (betheF t) (betheF t z * (hyperbolicCot (z+t)-hyperbolicCot z)) z := by
  convert (((hasDerivAt_id z).add_const t).csinh.div (Complex.hasDerivAt_sinh z) hz) using 1
  · funext x
    rfl
  · simp only [id_eq]
    unfold betheF hyperbolicCot
    field_simp
    <;> ring

/-- A finite product with one independent root coordinate. -/
theorem prod_update_coordinate {n : ℕ} (f : ℂ → ℂ) (Y : Fin n → ℂ)
    (j : Fin n) (z : ℂ) :
    (∏ k, f (Function.update Y j z k)) = f z * ∏ k ∈ Finset.univ.erase j, f (Y k) := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
  simp only [Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro k hk
  rw [Function.update_of_ne (Finset.mem_erase.mp hk).1]

/-- The independent root derivative is the paper's source column with its
exact extracted vacuum factor and twist normalization. -/
theorem independentRootDerivative_source {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (u : ℂ) (hu : SourceRegular lam b L Y u)
    (hcross : ∀ j, Complex.sinh (u-Y j) ≠ 0) (j : Fin n) :
    independentRootDerivative lam b L Y twist u j =
      Complex.exp (Complex.I*twist)*extractedVacuum lam b L Y u *
        (-2*(Real.pi : ℂ)*Complex.I)*scalarSource lam b L Y twist u j := by
  classical
  let t := Complex.I*(lam : ℂ)
  let P := ∏ k, betheF t ((Y k : ℂ)-u)
  let Q := ∏ k, betheF t (u-Y k)
  have hm : Complex.sinh ((Y j : ℂ)-u) ≠ 0 := by
    rw [show (Y j : ℂ)-u = -(u-Y j) by ring, Complex.sinh_neg]
    exact neg_ne_zero.mpr (hcross j)
  have hmt : Complex.sinh ((Y j : ℂ)-u+t) ≠ 0 := by
    dsimp [t]
    rw [show (Y j : ℂ)-u+Complex.I*lam = -(u-Y j-Complex.I*lam) by ring, Complex.sinh_neg]
    exact neg_ne_zero.mpr (hu.2 j).1
  have hdP := (hasDerivAt_betheF t ((Y j : ℂ)-u) hm hmt).comp (Y j : ℂ)
    ((hasDerivAt_id (Y j : ℂ)).sub_const u)
  have hdQ := (hasDerivAt_betheF t (u-Y j) (hcross j) (hu.2 j).2).comp (Y j : ℂ)
    ((hasDerivAt_const (Y j : ℂ) u).sub (hasDerivAt_id (Y j : ℂ)))
  have hp : HasDerivAt (fun z : ℂ => ∏ k, betheF t (Function.update (fun k => (Y k : ℂ)) j z k-u))
      (P*(hyperbolicCot ((Y j : ℂ)-u+t)-hyperbolicCot ((Y j : ℂ)-u))) (Y j : ℂ) := by
    simp only [prod_update_coordinate (fun z => betheF t (z-u))]
    convert hdP.mul_const (∏ k ∈ Finset.univ.erase j, betheF t ((Y k : ℂ)-u)) using 1
    · funext z
      rfl
    · have hPeq : P = betheF t ((Y j : ℂ)-u) * ∏ k ∈ Finset.univ.erase j, betheF t ((Y k : ℂ)-u) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
      rw [hPeq]
      simp only [Function.comp_def, mul_one]
      ring
  have hq : HasDerivAt (fun z : ℂ => ∏ k, betheF t (u-Function.update (fun k => (Y k : ℂ)) j z k))
      (-Q*(hyperbolicCot (u-Y j+t)-hyperbolicCot (u-Y j))) (Y j : ℂ) := by
    simp only [prod_update_coordinate (fun z => betheF t (u-z))]
    convert hdQ.mul_const (∏ k ∈ Finset.univ.erase j, betheF t (u-Y k)) using 1
    · funext z
      rfl
    · have hQeq : Q = betheF t (u-Y j) * ∏ k ∈ Finset.univ.erase j, betheF t (u-Y k) :=
        (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)).symm
      rw [hQeq]
      simp only [Function.comp_def, zero_sub, sub_zero, one_mul, mul_neg, mul_one]
      ring
  have hd := (hp.const_mul (Complex.exp (Complex.I*twist)*vacuumA t (fun a => (b a : ℂ)) u L)).add
    (hq.const_mul (Complex.exp (-Complex.I*twist)*vacuumL t (fun a => (b a : ℂ)) u L))
  change HasDerivAt (fun z => independentBetheTau lam b L (Function.update (fun k => (Y k : ℂ)) j z) twist u) _ _ at hd
  rw [independentRootDerivative, hd.deriv]
  have hPn : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    apply div_ne_zero
    · dsimp [t]
      rw [show (Y k : ℂ)-u+Complex.I*lam = -(u-Y k-Complex.I*lam) by ring, Complex.sinh_neg]
      exact neg_ne_zero.mpr (hu.2 k).1
    · rw [show (Y k : ℂ)-u = -(u-Y k) by ring, Complex.sinh_neg]
      exact neg_ne_zero.mpr (hcross k)
  have hphase : Complex.exp (Complex.I*twist)*Complex.exp (-2*Complex.I*twist) =
      Complex.exp (-Complex.I*twist) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  have hquot : betheQ lam b L Y u = vacuumL t (fun a => (b a : ℂ)) u L /
      vacuumA t (fun a => (b a : ℂ)) u L * (Q/P) := by
    unfold betheQ
    congr 1
    dsimp [P, Q, t]
    rw [← Finset.prod_div_distrib]
    apply Finset.prod_congr rfl
    intro k hk
    rw [shifted_ratio_as_f _ _ (hcross k)]
    congr 2
    ring
  rw [show (Y j : ℂ)-u+t = -(u-Y j-t) by ring,
    show (Y j : ℂ)-u = -(u-Y j) by ring, hyperbolicCot_neg, hyperbolicCot_neg]
  unfold extractedVacuum scalarSource betheFProduct
  change _ = Complex.exp (Complex.I*twist)*(vacuumA t (fun a => (b a : ℂ)) u L*P)*
    (-2*(Real.pi : ℂ)*Complex.I)* (-(1/(2*(Real.pi : ℂ)*Complex.I)) *
      ((1+Complex.exp (-2*Complex.I*twist)*betheQ lam b L Y u)*hyperbolicCot (u-Y j) -
        hyperbolicCot (u-Y j-t) - Complex.exp (-2*Complex.I*twist)*
        betheQ lam b L Y u*hyperbolicCot (u-Y j+t)))
  rw [hquot]
  have ha : vacuumA t (fun a => (b a : ℂ)) u L ≠ 0 := hu.1
  field_simp [ha, hPn, Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  ring_nf at hphase ⊢
  linear_combination -(vacuumL t (fun a => (b a : ℂ)) u L*Q*
    (hyperbolicCot (u-Y j)-hyperbolicCot (u-Y j+t)))*hphase

/-- The source-column version is derived, including every prefactor; it is
not a second external assumption. -/
theorem slavnov_source_of_identity {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (hSlavnov : SlavnovIdentity lam b L Y twist) :
    SlavnovSourceIdentity lam b L Y twist := by
  intro U hreg hcross
  have h := hSlavnov U hreg hcross
  have hmat : (Matrix.of (fun j k => independentRootDerivative lam b L Y twist (U k) j)) =
      Matrix.of (fun j k => (Complex.exp (Complex.I*twist)*extractedVacuum lam b L Y (U k)*
        (-2*(Real.pi : ℂ)*Complex.I))*scalarSourceMatrix lam b L Y twist U j k) := by
    ext j k
    exact independentRootDerivative_source lam b L Y twist (U k) (hreg k) (fun j => hcross j k) j
  rw [hmat, Matrix.det_mul_row] at h
  simp only [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  have he : Complex.exp (-((n : ℂ)*Complex.I*twist))*Complex.exp (Complex.I*twist)^n = 1 := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    convert Complex.exp_zero using 1
    congr 1
    ring
  convert h using 1
  linear_combination -((-2*(Real.pi : ℂ)*Complex.I)^n *
    (∏ j, vacuumL (Complex.I*lam) (fun a => (b a : ℂ)) (Y j) L)*
    (∏ k, extractedVacuum lam b L Y (U k))*(scalarSourceMatrix lam b L Y twist U).det)*he

end SixVertex
