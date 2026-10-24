import SixVertex.FiniteBetheData
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.LinearAlgebra.Matrix.Block

namespace SixVertex
open Filter Topology

noncomputable def hyperbolicCot (z : ℂ) : ℂ := Complex.cosh z / Complex.sinh z

noncomputable def scalarSource {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (u : ℂ) (j : Fin n) : ℂ :=
  -(1/(2*(Real.pi : ℂ)*Complex.I)) *
    ((1+Complex.exp (-2*Complex.I*twist)*betheQ lam b L Y u)*hyperbolicCot (u-Y j)
      - hyperbolicCot (u-Y j-Complex.I*lam)
      - Complex.exp (-2*Complex.I*twist)*betheQ lam b L Y u *
        hyperbolicCot (u-Y j+Complex.I*lam))

noncomputable def complexGaudin {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  (gaudinMatrix lam b L Y).map Complex.ofRealHom

/-- The two regular coth terms are exactly the real interaction kernel. -/
theorem coth_difference_kernel (lam u : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    (hyperbolicCot ((u : ℂ)-Complex.I*lam) -
      hyperbolicCot ((u : ℂ)+Complex.I*lam)) / (2*(Real.pi : ℂ)*Complex.I) =
      (kernelK lam u : ℂ) := by
  have hs := (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hplus := sinh_real_shift_ne_zero u lam hs
  have hminus := sinh_real_shift_ne_zero u (-lam) (by simpa using hs)
  have em : (u : ℂ)+Complex.I*(-lam : ℝ) = (u : ℂ)-Complex.I*lam := by push_cast; ring
  rw [em] at hminus
  unfold hyperbolicCot kernelK phaseDensity
  simp only [Complex.ofReal_div, Complex.ofReal_mul]
  have hp : Complex.sinh ((u : ℂ)+Complex.I*lam) * Complex.sinh ((u : ℂ)-Complex.I*lam) =
      ((Real.cosh (2*u)-Real.cos (2*lam))/2 : ℝ) := by
    rw [← em, sinh_real_shift, sinh_real_shift]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg, Real.cosh_two_mul,
      Real.cos_two_mul_eq_one_sub, Complex.ofReal_div, Complex.ofReal_sub,
      Complex.ofReal_add, Complex.ofReal_pow, Complex.ofReal_ofNat, Complex.ofReal_one,
      Complex.ofReal_mul]
    have hh := congrArg Complex.ofReal (Real.cosh_sq u)
    have ht := congrArg Complex.ofReal (Real.sin_sq_add_cos_sq lam)
    simp only [Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_one] at hh ht
    ring_nf
    simp only [Complex.I_sq]
    linear_combination ((Real.cosh u : ℂ)^2)*ht - ((Real.cos lam : ℂ)^2)*hh + hh/2 - ht
  have hn : Complex.cosh ((u : ℂ)-Complex.I*lam) * Complex.sinh ((u : ℂ)+Complex.I*lam) -
      Complex.cosh ((u : ℂ)+Complex.I*lam) * Complex.sinh ((u : ℂ)-Complex.I*lam) =
      Complex.I*(Real.sin (2*lam) : ℂ) := by
    calc
      _ = Complex.sinh (((u : ℂ)+Complex.I*lam)-((u : ℂ)-Complex.I*lam)) := by
        conv_rhs => rw [Complex.sinh_sub]
        ring
      _ = _ := by
        rw [show ((u : ℂ)+Complex.I*lam)-((u : ℂ)-Complex.I*lam) =
          ((2*lam : ℝ) : ℂ)*Complex.I by push_cast; ring,
          Complex.sinh_mul_I, ← Complex.ofReal_sin]
        ring
  have hd : (↑(Real.cosh (2*u)-Real.cos (2*lam)) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (phase_denominator_pos lam u hs).ne'
  field_simp [hplus, hminus, Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat] at hp
  linear_combination (↑(Real.cosh (2*u)-Real.cos (2*lam)) : ℂ)*hn -
    (2*Complex.I*(Real.sin (2*lam) : ℂ))*hp

/-- Holomorphic regularity of q on a neighborhood of every real spectral point. -/
theorem betheQ_differentiableAt_real {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (b : ℕ → ℝ) (L : ℕ) (Y : Fin n → ℝ) (u : ℝ) :
    DifferentiableAt ℂ (betheQ lam b L Y) (u : ℂ) := by
  unfold betheQ
  apply DifferentiableAt.mul
  · apply DifferentiableAt.div
    · simp only [vacuumL_product]
      fun_prop
    · simp only [vacuumA_product]
      fun_prop
    · exact vacuumA_real_ne_zero lam h0 hpi b L u
  · apply DifferentiableAt.fun_finset_prod
    intro k hk
    apply DifferentiableAt.div
    · fun_prop
    · fun_prop
    · have hn := sinh_real_shift_ne_zero (u-Y k) (-lam)
        (by simpa using (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne')
      convert hn using 1 <;> push_cast <;> congr 1 <;> ring

/-- The phase computation fixes the complex derivative, including its sign. -/
theorem betheQ_hasDerivAt_real {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (b : ℕ → ℝ) (L : ℕ) (hEven : Even L)
    (Y : Fin n → ℝ) (u : ℝ) :
    HasDerivAt (betheQ lam b L Y)
      (2*(Real.pi : ℂ)*Complex.I*(countingSlope lam b L Y u : ℂ)*betheQ lam b L Y u)
      (u : ℂ) := by
  have hd := (betheQ_differentiableAt_real lam h0 hpi b L Y u).hasDerivAt
  have hx := (hasDerivAt_countingXi lam b L Y u h0 hpi).ofReal_comp
  have he := ((hx.const_mul (2*(Real.pi : ℂ)*Complex.I)).cexp).const_mul ((-1 : ℂ)^n)
  have he' : HasDerivAt (fun v : ℝ => betheQ lam b L Y v)
      (2*(Real.pi : ℂ)*Complex.I*(countingSlope lam b L Y u : ℂ)*betheQ lam b L Y u) u := by
    convert he using 1
    · funext v
      exact betheQ_counting_phase lam b L hEven Y v h0 hpi
    · rw [betheQ_counting_phase lam b L hEven Y u h0 hpi]
      ring
  rw [hd.comp_ofReal.unique he'] at hd
  exact hd

/-- Cancellation of a simple coth pole by a vanishing differentiable factor. -/
theorem tendsto_zero_mul_coth {f : ℂ → ℂ} {d p : ℂ}
    (hf : HasDerivAt f d p) (hp : f p = 0) :
    Tendsto (fun u => f u * hyperbolicCot (u-p)) (𝓝[≠] p) (𝓝 d) := by
  have hs : HasDerivAt (fun u : ℂ => Complex.sinh (u-p)) 1 p := by
    simpa using ((hasDerivAt_id p).sub_const p).csinh
  have hc : ContinuousAt (fun u : ℂ => Complex.cosh (u-p)) p := by fun_prop
  have hl := (hf.tendsto_slope.div hs.tendsto_slope (by norm_num)).mul
    (hc.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [div_one, sub_self, Complex.cosh_zero, mul_one] at hl
  apply hl.congr'
  filter_upwards [self_mem_nhdsWithin] with u hu
  have hup : u-p ≠ 0 := sub_ne_zero.mpr hu
  simp only [Pi.div_apply, slope_def_field, hp, sub_zero, Complex.sinh_zero, sub_self, hyperbolicCot]
  field_simp
  <;> ring

/-- The twist coefficient is exactly -1 at each on-shell root. -/
theorem onShell_twist_q {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (twist : ℝ) (hShell : OnShell lam b L Y twist) (k : Fin n) :
    Complex.exp (-2*Complex.I*twist)*betheQ lam b L Y (Y k) = -1 := by
  rw [hShell k, mul_neg, ← Complex.exp_add]
  rw [show -2*Complex.I*(twist : ℂ)+(2*Complex.I*twist) = 0 by ring, Complex.exp_zero]

/-- Real root differences have no unshifted sinh zeros except on the diagonal. -/
theorem real_sinh_sub_ne {n : ℕ} (Y : Fin n → ℝ) (hY : Function.Injective Y)
    {j k : Fin n} (hjk : j ≠ k) : Complex.sinh ((Y k : ℂ)-Y j) ≠ 0 := by
  rw [← Complex.ofReal_sub, ← Complex.ofReal_sinh]
  exact Complex.ofReal_ne_zero.mpr (fun h => hjk (hY (sub_eq_zero.mp (Real.sinh_eq_zero.mp h))).symm)

/-- Every entry of the source column has its asserted complex limit at a root.
The diagonal is a proved pole cancellation, not a division-by-zero value. -/
theorem scalarSource_gaudin_limit {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (b : ℕ → ℝ) (L : ℕ) (hEven : Even L)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (twist : ℝ)
    (hShell : OnShell lam b L Y twist) (k j : Fin n) :
    Tendsto (fun u => scalarSource lam b L Y twist u j)
      (𝓝[≠] (Y k : ℂ)) (𝓝 (complexGaudin lam b L Y j k)) := by
  let κ := Complex.exp (-2*Complex.I*twist)
  let f := fun u => 1+κ*betheQ lam b L Y u
  have hq := betheQ_hasDerivAt_real lam h0 hpi b L hEven Y (Y k)
  have hκ := onShell_twist_q lam b L Y twist hShell k
  have hf : HasDerivAt f (-2*(Real.pi : ℂ)*Complex.I*(countingSlope lam b L Y (Y k) : ℂ)) (Y k : ℂ) := by
    convert (hq.const_mul κ).const_add 1 using 1
    dsimp [κ]
    linear_combination -(2*(Real.pi : ℂ)*Complex.I*(countingSlope lam b L Y (Y k) : ℂ))*hκ
  have hf0 : f (Y k) = 0 := by dsimp [f, κ]; rw [hκ]; ring
  have hm : ContinuousAt (fun u => hyperbolicCot (u-Y j-Complex.I*lam)) (Y k : ℂ) := by
    apply ContinuousAt.div <;> try fun_prop
    have hn := sinh_real_shift_ne_zero (Y k-Y j) (-lam)
      (by simpa using (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne')
    convert hn using 1 <;> push_cast <;> congr 1 <;> ring
  have hp : ContinuousAt (fun u => hyperbolicCot (u-Y j+Complex.I*lam)) (Y k : ℂ) := by
    apply ContinuousAt.div <;> try fun_prop
    simpa only [Complex.ofReal_sub] using
      sinh_real_shift_ne_zero (Y k-Y j) lam (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
  have hkernel := coth_difference_kernel lam (Y k-Y j) h0 hpi
  simp only [Complex.ofReal_sub] at hkernel
  have hlead : Tendsto (fun u => f u * hyperbolicCot (u-Y j)) (𝓝[≠] (Y k : ℂ))
      (𝓝 (if j=k then -2*(Real.pi : ℂ)*Complex.I*(countingSlope lam b L Y (Y k) : ℂ) else 0)) := by
    by_cases hjk : j=k
    · subst j
      simpa using tendsto_zero_mul_coth hf hf0
    · simp only [hjk, if_false]
      have hc : ContinuousAt (fun u => hyperbolicCot (u-Y j)) (Y k : ℂ) := by
        apply ContinuousAt.div <;> try fun_prop
        exact real_sinh_sub_ne Y hY hjk
      have hfc : ContinuousAt (fun u => f u * hyperbolicCot (u-Y j)) (Y k : ℂ) := hf.continuousAt.mul hc
      have ht := hfc.tendsto.mono_left (nhdsWithin_le_nhds (s := {((Y k : ℂ))}ᶜ))
      rw [hf0, zero_mul] at ht
      exact ht
  have hl := ((hlead.sub (hm.tendsto.mono_left nhdsWithin_le_nhds)).sub
    (((hq.continuousAt.tendsto.mono_left nhdsWithin_le_nhds).const_mul κ).mul
      (hp.tendsto.mono_left nhdsWithin_le_nhds))).const_mul (-(1/(2*(Real.pi : ℂ)*Complex.I)))
  change Tendsto (fun u => scalarSource lam b L Y twist u j) _ _ at hl
  convert hl using 2
  change (((if j=k then countingSlope lam b L Y (Y j) else 0) + kernelK lam (Y j-Y k) : ℝ) : ℂ) = _
  rw [Complex.ofReal_add]
  dsimp [κ] at *
  rw [hκ]
  rw [show Y k-Y j = -(Y j-Y k) by ring, kernelK_neg] at hkernel
  by_cases hjk : j=k
  · subst j
    simp only [ite_true]
    field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] at hkernel ⊢
    linear_combination -hkernel
  · simp only [hjk, if_false, Complex.ofReal_zero, zero_add]
    field_simp [Complex.I_ne_zero, Complex.ofReal_ne_zero.mpr Real.pi_ne_zero] at hkernel ⊢
    linear_combination -hkernel

/-- A punctured complex neighborhood of a real root contains no other sinh zeros. -/
theorem eventually_sinh_sub_ne (p : ℂ) :
    ∀ᶠ u in 𝓝[≠] p, Complex.sinh (u-p) ≠ 0 := by
  have hs : HasDerivAt (fun u : ℂ => Complex.sinh (u-p)) 1 p := by
    simpa using ((hasDerivAt_id p).sub_const p).csinh
  have he := hs.tendsto_slope.eventually (eventually_ne_nhds (show (1 : ℂ) ≠ 0 by norm_num))
  filter_upwards [he] with u hu
  simp only [slope_def_field, sub_self, Complex.sinh_zero, sub_zero] at hu
  exact (div_ne_zero_iff.mp hu).1

end SixVertex
