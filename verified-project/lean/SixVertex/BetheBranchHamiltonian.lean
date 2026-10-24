import SixVertex.BetheBranchEnergy
import SixVertex.BetheBranchContinuity
import SixVertex.ActualFreeBetheEnergy
import SixVertex.PhysicalBetheColumn
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Normed.Module.Connected

namespace SixVertex
open Filter Topology
noncomputable section

/-- The physical midpoint is in the regular ABA domain except when the
shifted zero at lambda = 2 pi / 3 is encountered. -/
theorem realRootSet_midpoint_regular {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (Y : Fin n → ℝ)
    (hshift : Real.sin (3*lam/2) ≠ 0) :
    BetheRegular (Complex.I*(lam : ℂ))
      (insert (betheSwapCoordinate lam 0) (rootSet Y)) := by
  classical
  let t : ℂ := Complex.I*(lam : ℂ)
  let x : ℂ := betheSwapCoordinate lam 0
  have hr := real_rootSet_regular lam h0 hpi Y
  have hhalf : Real.sin (lam/2) ≠ 0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos])).ne'
  have hx : x ∉ rootSet Y := by
    intro hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx
    have him := congrArg Complex.im hj
    simp [x,betheSwapCoordinate] at him
    linarith [h0]
  refine ⟨?_,?_⟩
  · intro p hp q hq hpq
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        exact False.elim (hpq rfl)
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
        have h := sinh_real_shift_ne_zero (-Y j) (lam/2) hhalf
        convert h using 1 <;> dsimp [x,betheSwapCoordinate] <;> push_cast <;> ring
    · rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
        have h := sinh_real_shift_ne_zero (-Y j) (lam/2) hhalf
        have h1 : Complex.sinh (betheSwapCoordinate lam 0-(Y j : ℂ)) ≠ 0 := by
          convert h using 1 <;> dsimp [betheSwapCoordinate] <;> push_cast <;> ring
        have he : (Y j : ℂ)-betheSwapCoordinate lam 0 =
            -(betheSwapCoordinate lam 0-(Y j : ℂ)) := by ring
        rw [he,Complex.sinh_neg]
        exact neg_ne_zero.mpr h1
      · exact hr.1 p hp q hq hpq
  · intro p hp q hq
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        simpa [x,t,betheSwapCoordinate] using physical_deformation_ne_zero lam h0 hpi
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
        have h := sinh_real_shift_ne_zero (-Y j) (3*lam/2) hshift
        convert h using 1 <;> dsimp [x,t,betheSwapCoordinate] <;> push_cast <;> ring
    · rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
        have h := sinh_real_shift_ne_zero (Y j) (lam/2) hhalf
        convert h using 1 <;> dsimp [x,t,betheSwapCoordinate] <;> push_cast <;> ring
      · exact hr.2 p hp q hq

private theorem complex_sinh_realShift_ne_zero_of_im (x : ℂ) (y : ℝ)
    (hsin : Real.sin x.im ≠ 0) : Complex.sinh (x-(y : ℂ)) ≠ 0 := by
  have h := sinh_real_shift_ne_zero (x.re-y) x.im hsin
  have he : ((x.re-y : ℝ) : ℂ) + Complex.I*(x.im : ℂ) = x-(y : ℂ) := by
    apply Complex.ext
    · simp
    · simp
  simpa only [he] using h

private theorem betheF_comp_analyticAt (t : ℂ) (f : ℂ → ℂ) (x : ℂ)
    (hf : AnalyticAt ℂ f x) (hden : Complex.sinh (f x) ≠ 0) :
    AnalyticAt ℂ (fun z => betheF t (f z)) x := by
  have harg : AnalyticAt ℂ (fun z => f z+t) x := hf.add analyticAt_const
  have hnum : AnalyticAt ℂ (fun z => Complex.sinh (f z+t)) x :=
    Complex.analyticAt_sinh.comp harg
  have hden' : AnalyticAt ℂ (fun z => Complex.sinh (f z)) x :=
    Complex.analyticAt_sinh.comp hf
  convert hnum.div hden' hden using 1 <;> rfl

private theorem homogeneous_aba_analyticAt_midpoint_ball {n : ℕ} (lam : ℝ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (L : ℕ) (Y : Fin n → ℝ)
    (x : ℂ) (hx : x ∈ Metric.ball (betheSwapCoordinate lam 0) (lam/4)) :
    AnalyticAt ℂ (fun z => abaEigenvalue (Complex.I*(lam : ℂ)) (fun _ => 0)
      L 0 (rootSet Y) z) x := by
  classical
  let t : ℂ := Complex.I*(lam : ℂ)
  have hdist : ‖x-betheSwapCoordinate lam 0‖ < lam/4 := by
    simpa [Metric.mem_ball, dist_eq_norm] using hx
  have himdiff : |x.im-lam/2| ≤ ‖x-betheSwapCoordinate lam 0‖ := by
    have hh := Complex.abs_im_le_norm (x-betheSwapCoordinate lam 0)
    simpa [betheSwapCoordinate] using hh
  have himlo : 0 < x.im := by
    have := abs_lt.mp (lt_of_le_of_lt himdiff hdist)
    linarith [h0]
  have himhi : x.im < Real.pi := by
    have := abs_lt.mp (lt_of_le_of_lt himdiff hdist)
    nlinarith [hpi,Real.pi_pos]
  have hsin : Real.sin x.im ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi himlo himhi).ne'
  have hsinNeg : Real.sin (-x.im) ≠ 0 := by rw [Real.sin_neg]; exact neg_ne_zero.mpr hsin
  have hA : AnalyticAt ℂ (fun z => vacuumA t (fun _ => 0) z L) x := by
    simp only [vacuumA_product]
    fun_prop
  have hL : AnalyticAt ℂ (fun z => vacuumL t (fun _ => 0) z L) x := by
    simp only [vacuumL_product]
    fun_prop
  have hF : AnalyticAt ℂ (fun z => ∏ p ∈ rootSet Y, betheF t (p-z)) x := by
    apply Finset.analyticAt_fun_prod
    intro p hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    have hg : AnalyticAt ℂ (fun z : ℂ => (Y j : ℂ)-z) x := by fun_prop
    have hd := complex_sinh_realShift_ne_zero_of_im x (Y j) hsin
    have hd' : Complex.sinh ((Y j : ℂ)-x) ≠ 0 := by
      have he : (Y j : ℂ)-x = -(x-(Y j : ℂ)) := by ring
      rw [he, Complex.sinh_neg]
      exact neg_ne_zero.mpr hd
    exact betheF_comp_analyticAt t _ x hg hd'
  have hG : AnalyticAt ℂ (fun z => ∏ p ∈ rootSet Y, betheF t (z-p)) x := by
    apply Finset.analyticAt_fun_prod
    intro p hp
    obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
    have hg : AnalyticAt ℂ (fun z : ℂ => z-(Y j : ℂ)) x := by fun_prop
    have hd := complex_sinh_realShift_ne_zero_of_im x (Y j) hsin
    exact betheF_comp_analyticAt t _ x hg hd
  simp only [abaEigenvalue,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul]
  exact (hA.mul hF).add (hL.mul hG)

private theorem homogeneous_aba_analyticOn_midpoint_ball {n : ℕ} (lam : ℝ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (L : ℕ) (Y : Fin n → ℝ) :
    AnalyticOnNhd ℂ (fun z => abaEigenvalue (Complex.I*(lam : ℂ)) (fun _ => 0)
      L 0 (rootSet Y) z) (Metric.ball (betheSwapCoordinate lam 0) (lam/4)) := by
  intro z hz
  exact homogeneous_aba_analyticAt_midpoint_ball lam h0 hpi L Y z hz

private theorem exceptional_midpoint_lift_regular {n : ℕ} (Y : Fin n → ℝ)
    (δ : ℝ) (hδ : 0 < δ) (hδlt : δ < Real.pi/12) :
    BetheRegular (Complex.I*((2*Real.pi/3 : ℝ) : ℂ))
      (insert (Complex.I*((Real.pi/3+δ : ℝ) : ℂ)) (rootSet Y)) := by
  classical
  let lam : ℝ := 2*Real.pi/3
  let x : ℂ := Complex.I*((Real.pi/3+δ : ℝ) : ℂ)
  let t : ℂ := Complex.I*(lam : ℂ)
  have h0 : 0 < lam := by dsimp [lam]; positivity
  have hpi : lam < Real.pi := by dsimp [lam]; linarith [Real.pi_pos]
  have hs1 : Real.sin (Real.pi/3+δ) ≠ 0 := by
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos,hδ])
      (by linarith [Real.pi_pos,hδlt])).ne'
  have hs2 : Real.sin (Real.pi/3-δ) ≠ 0 := by
    exact (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos,hδlt])
      (by linarith [Real.pi_pos,hδ])).ne'
  have hs3 : Real.sin (Real.pi+δ) ≠ 0 := by
    have he : Real.sin (Real.pi+δ) = -Real.sin δ := by
      rw [Real.sin_add,Real.sin_pi,Real.cos_pi]
      ring
    rw [he]
    exact neg_ne_zero.mpr (Real.sin_pos_of_pos_of_lt_pi hδ (by linarith [Real.pi_pos,hδlt])).ne'
  have hr := real_rootSet_regular lam h0 hpi Y
  refine ⟨?_,?_⟩
  · intro p hp q hq hpq
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        exact False.elim (hpq rfl)
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
        have h := sinh_real_shift_ne_zero (-Y j) (Real.pi/3+δ) hs1
        have h1 : Complex.sinh (x-(Y j : ℂ)) ≠ 0 := by
          have harg : x-(Y j : ℂ) = (-(Y j : ℝ) : ℂ) +
              Complex.I*((Real.pi/3+δ : ℝ) : ℂ) := by
            simp [x]
            push_cast
            ring
          rw [harg]
          simpa only [Complex.ofReal_neg] using h
        exact h1
    · rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
        have h := sinh_real_shift_ne_zero (-Y j) (Real.pi/3+δ) hs1
        have h1 : Complex.sinh (x-(Y j : ℂ)) ≠ 0 := by
          have harg : x-(Y j : ℂ) = (-(Y j : ℝ) : ℂ) +
              Complex.I*((Real.pi/3+δ : ℝ) : ℂ) := by
            simp [x]
            push_cast
            ring
          rw [harg]
          simpa only [Complex.ofReal_neg] using h
        have he : (Y j : ℂ)-x=-(x-(Y j : ℂ)) := by ring
        rw [he,Complex.sinh_neg]
        exact neg_ne_zero.mpr h1
      · exact hr.1 p hp q hq hpq
  · intro p hp q hq
    rcases Finset.mem_insert.mp hp with hp | hp
    · subst p
      rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        simpa [lam,t] using physical_deformation_ne_zero lam h0 hpi
      · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
        have h := sinh_real_shift_ne_zero (-Y j) (Real.pi+δ) hs3
        have h1 : Complex.sinh (x-(Y j : ℂ)+t) ≠ 0 := by
          have harg : x-(Y j : ℂ)+t = (-(Y j : ℝ) : ℂ) +
              Complex.I*((Real.pi+δ : ℝ) : ℂ) := by
            simp [x,lam,t]
            push_cast
            ring
          rw [harg]
          simpa only [Complex.ofReal_neg] using h
        exact h1
    · rcases Finset.mem_insert.mp hq with hq | hq
      · subst q
        obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
        have h := sinh_real_shift_ne_zero (Y j) (Real.pi/3-δ) hs2
        have h1 : Complex.sinh ((Y j : ℂ)-x+t) ≠ 0 := by
          have harg : (Y j : ℂ)-x+t = (Y j : ℝ) +
              Complex.I*((Real.pi/3-δ : ℝ) : ℂ) := by
            simp [x,lam,t]
            push_cast
            ring
          rw [harg]
          exact h
        exact h1
      · exact hr.2 p hp q hq

private theorem lambda_eq_two_pi_div_three_of_shift_sine_zero (lam : ℝ)
    (h0 : 0 < lam) (hpi : lam < Real.pi)
    (hs : Real.sin (3*lam/2)=0) : lam=2*Real.pi/3 := by
  obtain ⟨m,hm⟩ := Real.sin_eq_zero_iff.mp hs
  have hlow : 0 < 3*lam/2 := by positivity
  have hupp : 3*lam/2 < 2*Real.pi := by nlinarith [Real.pi_pos,hpi]
  have hmloR : (0:ℝ) < (m:ℝ) := by nlinarith [hm,Real.pi_pos]
  have hmhiR : (m:ℝ) < 2 := by nlinarith [hm,Real.pi_pos]
  have hmlo : 0 < m := by exact_mod_cast hmloR
  have hmhi : m < 2 := by exact_mod_cast hmhiR
  have hmone : m=1 := by omega
  rw [hmone] at hm
  nlinarith [hm]

/-- The entire transfer-matrix eigenvalue agrees locally with the ABA formula
at the physical midpoint. At the exceptional shifted-sinh point, agreement
away from the midpoint extends across it by analytic continuation. -/
private theorem physical_entire_bethe_swap_local_identity {n : ℕ} (lam : ℝ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (L : ℕ)
    (Y : Fin n → ℝ) (rho : ℂ → ℂ) (hrho : ∀ x, AnalyticAt ℂ rho x)
    (hgen : ∀ x, x ∉ rootSet Y →
      BetheRegular (Complex.I*(lam : ℂ)) (insert x (rootSet Y)) →
      rho x = abaEigenvalue (Complex.I*(lam : ℂ)) (fun _ => 0) L 0 (rootSet Y) x) :
    (fun z => rho (betheSwapCoordinate lam z)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => abaEigenvalue (Complex.I*(lam : ℂ)) (fun _ => 0) L 0 (rootSet Y)
        (betheSwapCoordinate lam z)) ∧
    rho (betheSwapCoordinate lam 0) =
      abaEigenvalue (Complex.I*(lam : ℂ)) (fun _ => 0) L 0 (rootSet Y)
        (betheSwapCoordinate lam 0) := by
  let t : ℂ := Complex.I*(lam : ℂ)
  let x₀ : ℂ := betheSwapCoordinate lam 0
  have hx₀ : x₀ ∉ rootSet Y := by
    intro hx
    obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hx
    have him := congrArg Complex.im hj
    simp [x₀,betheSwapCoordinate] at him
    linarith [h0]
  have hcont : ContinuousAt (betheSwapCoordinate lam) (0 : ℂ) := by
    unfold betheSwapCoordinate
    fun_prop
  by_cases hshift : Real.sin (3*lam/2) ≠ 0
  · have hmid := realRootSet_midpoint_regular lam h0 hpi Y hshift
    have hnear := regular_spectral_eventually t
      (physical_deformation_ne_zero lam h0 hpi) (rootSet Y) x₀ hx₀ hmid
    have heq : (fun z => rho (betheSwapCoordinate lam z)) =ᶠ[𝓝 (0 : ℂ)]
        (fun z => abaEigenvalue t (fun _ => 0) L 0 (rootSet Y)
          (betheSwapCoordinate lam z)) := by
      filter_upwards [hcont.eventually hnear] with z hz
      exact hgen _ hz.1 hz.2
    exact ⟨heq,hgen x₀ hx₀ hmid⟩
  · have hzero : Real.sin (3*lam/2) = 0 := by
      by_contra h
      exact hshift h
    have hlam : lam = 2*Real.pi/3 :=
      lambda_eq_two_pi_div_three_of_shift_sine_zero lam h0 hpi hzero
    have hx₀formula : x₀ = Complex.I*((Real.pi/3 : ℝ) : ℂ) := by
      simp [x₀,betheSwapCoordinate,hlam]
      push_cast
      ring
    let δ : ℕ → ℝ := fun k => (Real.pi/24)/((k : ℝ)+1)
    let xseq : ℕ → ℂ := fun k =>
      Complex.I*((Real.pi/3+δ k : ℝ) : ℂ)
    have hδpos (k : ℕ) : 0 < δ k := by
      dsimp [δ]
      positivity
    have hδlt (k : ℕ) : δ k < Real.pi/12 := by
      have hk : 1 ≤ (k : ℝ)+1 := by
        have hk0 : 0 ≤ (k : ℝ) := Nat.cast_nonneg k
        linarith
      dsimp [δ]
      apply (div_lt_iff₀ (by linarith : (0 : ℝ) < (k : ℝ)+1)).2
      nlinarith [Real.pi_pos,hk]
    have hδt : Tendsto δ atTop (𝓝 (0 : ℝ)) := by
      dsimp [δ]
      simpa [div_eq_mul_inv,mul_comm] using
        (tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (Real.pi/24))
    have hcontδ : ContinuousAt
        (fun d : ℝ => Complex.I*((Real.pi/3+d : ℝ) : ℂ)) 0 := by
      fun_prop
    have hxseqt : Tendsto xseq atTop (𝓝 x₀) := by
      change Tendsto ((fun d : ℝ => Complex.I*((Real.pi/3+d : ℝ) : ℂ)) ∘ δ)
        atTop (𝓝 x₀)
      rw [hx₀formula]
      simpa only [add_zero] using hcontδ.tendsto.comp hδt
    have hxseqne (k : ℕ) : xseq k ≠ x₀ := by
      intro h
      have him := congrArg Complex.im h
      simp [xseq,hx₀formula] at him
      linarith [hδpos k]
    have hxseqroot (k : ℕ) : xseq k ∉ rootSet Y := by
      intro h
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp h
      have him := congrArg Complex.im hj
      simp [xseq] at him
      linarith [hδpos k]
    have hseqEq (k : ℕ) :
        rho (xseq k) = abaEigenvalue t (fun _ => 0) L 0 (rootSet Y) (xseq k) := by
      have hregular₀ := exceptional_midpoint_lift_regular Y (δ k) (hδpos k) (hδlt k)
      have hregular : BetheRegular t (insert (xseq k) (rootSet Y)) := by
        simpa [t,hlam,xseq] using hregular₀
      exact hgen (xseq k) (hxseqroot k) hregular
    have hxwithin : Tendsto xseq atTop (𝓝[≠] x₀) :=
      tendsto_nhdsWithin_iff.mpr ⟨hxseqt,Filter.Eventually.of_forall hxseqne⟩
    have hseqfreq : ∃ᶠ k in atTop,
        rho (xseq k) = abaEigenvalue t (fun _ => 0) L 0 (rootSet Y) (xseq k) :=
      Filter.Eventually.frequently (Filter.Eventually.of_forall hseqEq)
    have hfreq : ∃ᶠ x in 𝓝[≠] x₀,
        rho x = abaEigenvalue t (fun _ => 0) L 0 (rootSet Y) x :=
      hxwithin.frequently hseqfreq
    let U := Metric.ball x₀ (lam/4)
    have hrad : 0 < lam/4 := by positivity
    have hx₀U : x₀ ∈ U := Metric.mem_ball_self hrad
    have hrhoOn : AnalyticOnNhd ℂ rho U := by
      intro z hz
      exact hrho z
    have habaOn : AnalyticOnNhd ℂ
        (fun z => abaEigenvalue t (fun _ => 0) L 0 (rootSet Y) z) U := by
      intro z hz
      exact homogeneous_aba_analyticAt_midpoint_ball lam h0 hpi L Y z hz
    have hid : Set.EqOn rho
        (fun z => abaEigenvalue t (fun _ => 0) L 0 (rootSet Y) z) U :=
      hrhoOn.eqOn_of_preconnected_of_frequently_eq habaOn
        Metric.isPreconnected_ball hx₀U hfreq
    have hlocal : (fun z => rho (betheSwapCoordinate lam z)) =ᶠ[𝓝 (0 : ℂ)]
        (fun z => abaEigenvalue t (fun _ => 0) L 0 (rootSet Y)
          (betheSwapCoordinate lam z)) := by
      have hnear : ∀ᶠ x in 𝓝 x₀,
          rho x = abaEigenvalue t (fun _ => 0) L 0 (rootSet Y) x := by
        filter_upwards [Metric.ball_mem_nhds x₀ hrad] with x hx
        exact hid hx
      filter_upwards [hcont.eventually hnear] with z hz
      exact hz
    exact ⟨hlocal,hid hx₀U⟩

/-- Entire eigenvalue continuation transfers the exact ABA derivative to the
continued eigenline, including the exceptional shifted-sinh point by analytic
continuation. -/
theorem physical_entire_bethe_swap_hasDerivAt {n : ℕ} (lam : ℝ)
    (h0 : 0 < lam) (hpi : lam < Real.pi) (L : ℕ) (hL : 2 ≤ L)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (rho : ℂ → ℂ)
    (hrho : ∀ x, AnalyticAt ℂ rho x)
    (hgen : ∀ x, x ∉ rootSet Y →
      BetheRegular (Complex.I*(lam : ℂ)) (insert x (rootSet Y)) →
      rho x = abaEigenvalue (Complex.I*(lam : ℂ)) (fun _ => 0) L 0 (rootSet Y) x) :
    HasDerivAt (fun z => rho (betheSwapCoordinate lam z))
      (((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ) *
        rho (betheSwapCoordinate lam 0)) 0 := by
  obtain ⟨heq,hvalue⟩ := physical_entire_bethe_swap_local_identity
    lam h0 hpi L Y rho hrho hgen
  have hABAderiv := homogeneous_aba_swap_hasDerivAt lam h0 hpi L hL Y hY
  have hderiv := hABAderiv.congr_of_eventuallyEq heq
  rw [← hvalue] at hderiv
  exact hderiv

/-- On the globally constructed homogeneous root branch, the physical
Hamiltonian acts by the exact finite-chain energy throughout the physical
interval. Analytic continuation handles the exceptional midpoint; the sole
external mathematical input remains A01. -/
theorem nonpositiveKernel_hamiltonian_eigenline_of_nonzero {K n : ℕ} (lam eta : ℝ)
    (hEven : Even (K+1)) (hfill : 2*n ≤ K+1)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hV : physicalBetheVector lam (fun _ => 0) (K+1)
      (nonpositiveKernelRoots (fun _ => 0) (K+1) (by omega) n hfill lam)≠0) :
    let Y := nonpositiveKernelRoots (fun _ => 0) (K+1) (by omega) n hfill lam
    homogeneousLinkHamiltonian lam eta K *
      (quantumGauge (K+1) * betheState (Complex.I*(lam : ℂ))
        (physical_deformation_ne_zero lam (lt_of_lt_of_le (by positivity) hhalf) hpi)
        (fun _ => 0) (K+1) (rootSet Y)) =
      (-((eta : ℂ) * (2*Real.pi*∑ j,kernelS lam (Y j) - ((K+1) : ℝ)*Real.cot lam))) •
        (quantumGauge (K+1) * betheState (Complex.I*(lam : ℂ))
          (physical_deformation_ne_zero lam (lt_of_lt_of_le (by positivity) hhalf) hpi)
          (fun _ => 0) (K+1) (rootSet Y)) := by
  classical
  let L : ℕ := K+1
  let hLpos : 0 < L := by dsimp [L]; omega
  let h0 : 0 < lam := lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.pi/2) hhalf
  let Y : Fin n → ℝ := nonpositiveKernelRoots (fun _ => 0) L hLpos n hfill lam
  have hroots := nonpositiveKernelRoots_spec (fun _ => 0) L hLpos n hfill lam hhalf hpi
  have hY : Function.Injective Y := hroots.1.injective
  have hfinite := nonpositiveKernelRoots_finite_data (fun _ => 0) L hLpos hEven n hfill lam hhalf hpi
  have hShell := hfinite.1
  have hdet : (gaudinMatrix lam (fun _ => 0) L Y).det ≠ 0 := hfinite.2.2.ne'
  let ht := physical_deformation_ne_zero lam h0 hpi
  let B := betheState (Complex.I*(lam : ℂ)) ht (fun _ => 0) L (rootSet Y)
  have hV' : physicalBetheVector lam (fun _ => 0) L Y ≠ 0 := by
    simpa [L,Y,hLpos] using hV
  have hB : B ≠ 0 := by
    exact betheState_ne_zero_of_physicalBetheVector lam h0 hpi (fun _ => 0) L Y hY hV'
  let M := quantumGauge L * B
  have hM : M ≠ 0 := quantumGauge_mul_ne_zero L B hB
  obtain ⟨u,hu⟩ := exists_real_fresh_spectral Y
  obtain ⟨rho,hrho,heigen,hgen⟩ := balancedRoots_entire_eigenvalue
    (Complex.I*(lam : ℂ)) ht (fun _ => 0) L 0 (rootSet Y)
    (onShell_balancedRoots lam h0 hpi (fun _ => 0) L Y hY 0 hShell) hB u hu
    (real_insert_rootSet_regular lam h0 hpi Y u)
  let x₀ : ℂ := betheSwapCoordinate lam 0
  have hLtwo : 2 ≤ L := by
    dsimp [L]
    obtain ⟨m,hm⟩ := hEven
    omega
  have hrhoSwap := physical_entire_bethe_swap_hasDerivAt lam h0 hpi L hLtwo
    Y hY rho hrho hgen
  let sign : ℂ := (-1 : ℂ)^n
  let sigma : ℂ → ℂ := fun z => sign * rho (betheSwapCoordinate lam z)
  have hsigDeriv : HasDerivAt sigma
      (sign * (((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ) * rho x₀)) 0 := by
    exact hrhoSwap.const_mul sign
  have hphys (z : ℂ) : homogeneousPhysicalRow lam L z * M = sigma z • M := by
    have h := physical_eigenvector_of_standard_even lam ht (fun _ => 0) L hEven 0
      (rootSet Y) (betheSwapCoordinate lam z) (rho (betheSwapCoordinate lam z)) (heigen _)
    rw [physicalTwistedRow_swapCoordinate lam L z] at h
    simpa [M,sigma,sign,rootSet_card Y hY] using h
  obtain ⟨hsigma0,hHam⟩ := homogeneous_physical_eigenline_logarithmic lam eta h0 hpi K
    M sigma (sign * (((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ) * rho x₀))
    hsigDeriv hphys hM
  have hsign : sign ≠ 0 := by simp [sign]
  have hrho0 : rho x₀ ≠ 0 := by
    intro hz
    apply hsigma0
    simp [sigma,x₀,hz]
  have hscalar : (-(eta : ℂ) *
      (sign * (((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ) * rho x₀))) /
      (sign * rho x₀) =
      -((eta : ℂ) * ((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ)) := by
    field_simp [hsign,hrho0]
    <;> ring
  have hSigma0 : sigma 0 = sign*rho x₀ := by simp [sigma,x₀]
  have hscalar' : (-(eta : ℂ) *
      (sign * (((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ) * rho x₀))) /
      sigma 0 =
      -((eta : ℂ) * ((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ)) := by
    rw [hSigma0]
    exact hscalar
  rw [hscalar'] at hHam
  simpa [M,B,Y,L,hLpos] using hHam

/-- The A01 version of the Hamiltonian eigenline theorem. -/
theorem nonpositiveKernel_hamiltonian_eigenline {K n : ℕ} (lam eta : ℝ)
    (hEven : Even (K+1)) (hfill : 2*n ≤ K+1)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hSlavnov : SlavnovIdentity lam (fun _ => 0) (K+1)
      (nonpositiveKernelRoots (fun _ => 0) (K+1) (by omega) n hfill lam) 0) :
    let Y := nonpositiveKernelRoots (fun _ => 0) (K+1) (by omega) n hfill lam
    homogeneousLinkHamiltonian lam eta K *
      (quantumGauge (K+1) * betheState (Complex.I*(lam : ℂ))
        (physical_deformation_ne_zero lam (lt_of_lt_of_le (by positivity) hhalf) hpi)
        (fun _ => 0) (K+1) (rootSet Y)) =
      (-((eta : ℂ) * (2*Real.pi*∑ j,kernelS lam (Y j) - ((K+1) : ℝ)*Real.cot lam))) •
        (quantumGauge (K+1) * betheState (Complex.I*(lam : ℂ))
          (physical_deformation_ne_zero lam (lt_of_lt_of_le (by positivity) hhalf) hpi)
          (fun _ => 0) (K+1) (rootSet Y)) := by
  have hV := nonpositiveKernelPhysicalBetheVector_ne_zero (fun _ => 0) (K+1)
    (by omega) hEven n hfill lam hhalf hpi hSlavnov
  exact nonpositiveKernel_hamiltonian_eigenline_of_nonzero lam eta hEven hfill hhalf hpi hV

/-- The same continued Hamiltonian eigenline, evaluated on the physical
vacuum column, is the actual Hilbert Bethe vector in its particle sector. -/
theorem nonpositiveKernel_physicalBetheVector_eigenline {K n : ℕ} (lam eta : ℝ)
    (hEven : Even (K+1)) (hfill : 2*n ≤ K+1)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi)
    (hSlavnov : SlavnovIdentity lam (fun _ => 0) (K+1)
      (nonpositiveKernelRoots (fun _ => 0) (K+1) (by omega) n hfill lam) 0) :
    (homogeneousLinkHamiltonian lam eta K).mulVec
      (physicalBetheVector lam (fun _ => 0) (K+1)
        (nonpositiveKernelRoots (fun _ => 0) (K+1) (by omega) n hfill lam)) =
      (-((eta : ℂ) * (2*Real.pi*∑ j,
        kernelS lam ((nonpositiveKernelRoots (fun _ => 0) (K+1) (by omega) n hfill lam) j) -
        ((K+1) : ℝ)*Real.cot lam))) •
        physicalBetheVector lam (fun _ => 0) (K+1)
          (nonpositiveKernelRoots (fun _ => 0) (K+1) (by omega) n hfill lam) := by
  classical
  let L : ℕ := K+1
  have hLpos : 0 < L := by dsimp [L]; omega
  have h0 : 0 < lam := lt_of_lt_of_le (by positivity : (0 : ℝ) < Real.pi/2) hhalf
  let Y : Fin n → ℝ := nonpositiveKernelRoots (fun _ => 0) L hLpos n hfill lam
  have hroots := nonpositiveKernelRoots_spec (fun _ => 0) L hLpos n hfill lam hhalf hpi
  have hY : Function.Injective Y := hroots.1.injective
  let B := betheState (Complex.I*(lam : ℂ))
    (physical_deformation_ne_zero lam h0 hpi) (fun _ => 0) L (rootSet Y)
  let M := quantumGauge L * B
  have hmatrix := nonpositiveKernel_hamiltonian_eigenline lam eta hEven hfill hhalf hpi hSlavnov
  have hmatrix' : homogeneousLinkHamiltonian lam eta K * M =
      (-((eta : ℂ) * (2*Real.pi*∑ j,kernelS lam (Y j) -
        (L : ℝ)*Real.cot lam))) • M := by
    simpa [M,B,L,Y,hLpos] using hmatrix
  let e : RowSpins L → ℂ := Pi.single (plusSpins L) 1
  have hcolumn : M.mulVec e = physicalBetheVector lam (fun _ => 0) L Y := by
    rw [show e = Pi.single (plusSpins L) 1 by rfl,Matrix.mulVec_single_one]
    funext q
    simpa [M,B] using (physicalBetheVector_eq_betheState_column lam h0 hpi
      (fun _ => 0) L Y hY q).symm
  have h := congrArg (fun A : Matrix (RowSpins L) (RowSpins L) ℂ => A.mulVec e) hmatrix'
  rw [← Matrix.mulVec_mulVec] at h
  simp only [Matrix.smul_mulVec] at h
  simpa [hcolumn,M,L,Y] using h

end
end SixVertex
