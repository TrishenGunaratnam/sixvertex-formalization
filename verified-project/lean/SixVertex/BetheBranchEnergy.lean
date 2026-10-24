import SixVertex.FreeBetheEigenvalueDerivative
import SixVertex.KernelDerivatives

namespace SixVertex
noncomputable section

private theorem homogeneous_vacuumA_swap_hasDerivAt (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (L : ℕ) :
    HasDerivAt (fun z : ℂ => vacuumA (Complex.I * (lam : ℂ)) (fun _ => 0)
      (betheSwapCoordinate lam z) L)
      (-(L : ℂ) * (Real.cot lam : ℂ)) 0 := by
  let t : ℂ := Complex.I * (lam : ℂ)
  let f : ℂ → ℂ := fun z => Complex.sinh (t - Complex.I * z) / Complex.sinh t
  have ht : Complex.sinh t ≠ 0 := by
    dsimp [t]
    exact physical_deformation_ne_zero lam h0 hpi
  have harg : HasDerivAt (fun z : ℂ => t - Complex.I * z) (-Complex.I) 0 := by
    have h := (hasDerivAt_const (0 : ℂ) t).sub
      ((hasDerivAt_id (0 : ℂ)).const_mul Complex.I)
    change HasDerivAt ((fun _ : ℂ => t) - (fun z : ℂ => Complex.I * z)) (-Complex.I) 0
    simpa using h
  have hf : HasDerivAt f
      ((-Complex.I * Complex.cosh t) / Complex.sinh t) 0 := by
    dsimp [f]
    have hsinh : HasDerivAt Complex.sinh (Complex.cosh t) (t - Complex.I * 0) := by
      simpa using Complex.hasDerivAt_sinh t
    have hc := (hsinh.comp 0 harg).div_const (Complex.sinh t)
    convert hc using 1
    · ext z
      simp [Function.comp_apply, div_eq_mul_inv, mul_comm]
    · ring
  have hcoef : (-Complex.I * Complex.cosh t) / Complex.sinh t =
      -(Real.cot lam : ℂ) := by
    have hs := sinh_physical_deformation lam
    have hc : Complex.cosh (Complex.I * (lam : ℂ)) = (Real.cos lam : ℂ) := by
      rw [mul_comm Complex.I, Complex.cosh_mul_I]
      simp
    dsimp [t]
    rw [hs, hc]
    rw [Real.cot_eq_cos_div_sin, Complex.ofReal_div, ← Complex.ofReal_sin]
    have hsin : Real.sin lam ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi h0 hpi).ne'
    field_simp [Complex.I_ne_zero, hsin]
    <;> ring
  have hprod : ∀ z, vacuumA (Complex.I * (lam : ℂ)) (fun _ => 0)
      (betheSwapCoordinate lam z) L = f z ^ L := by
    intro z
    rw [vacuumA_product]
    have harg' : ∀ j : ℕ, betheSwapCoordinate lam z - (0 : ℂ) + t / 2 = t - Complex.I * z := by
      intro j
      dsimp [betheSwapCoordinate, t]
      push_cast
      ring
    calc
      _ = ∏ j ∈ Finset.range L, f z := by
        apply Finset.prod_congr rfl
        intro j hj
        dsimp [f]
        rw [harg' j]
      _ = f z ^ L := by simp [Finset.card_range]
  have hpow := hf.fun_pow L
  have hfinal : HasDerivAt (fun z : ℂ => f z ^ L)
      (-(L : ℂ) * (Real.cot lam : ℂ)) 0 := by
    have hf0 : f 0 = 1 := by simp [f, ht]
    rw [hf0, hcoef] at hpow
    convert hpow using 1 <;> simp <;> ring
  exact hfinal.congr_of_eventuallyEq (Filter.Eventually.of_forall hprod)

theorem physical_betheFactor_swap_kernel_deriv (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (y : ℝ) :
    HasDerivAt (fun z : ℂ => betheF (Complex.I * (lam : ℂ))
      ((y : ℂ) - betheSwapCoordinate lam z))
      (((2 * Real.pi * kernelS lam y : ℝ) : ℂ) *
        betheF (Complex.I * (lam : ℂ))
          ((y : ℂ) - betheSwapCoordinate lam 0)) 0 := by
  let t : ℂ := Complex.I * (lam : ℂ)
  have hs : Real.sin (-lam / 2) ≠ 0 := by
    have hh := Real.sin_pos_of_pos_of_lt_pi
      (show 0 < lam / 2 by positivity)
      (show lam / 2 < Real.pi by linarith [hpi])
    have hneg : Real.sin (-lam / 2) = -Real.sin (lam / 2) := by
      rw [neg_div, Real.sin_neg]
    rw [hneg]
    exact neg_ne_zero.mpr hh.ne'
  have hd : Complex.sinh ((y : ℂ) - t / 2) ≠ 0 := by
    have h := sinh_real_shift_ne_zero y (-lam / 2) hs
    convert h using 1 <;> dsimp [t] <;> push_cast <;> congr 1 <;> ring
  have hbase := bethe_factor_swap_hasDerivAt t (y : ℂ) hd
  have hprod : 2 * Complex.sinh ((y : ℂ) - t / 2) * Complex.sinh ((y : ℂ) + t / 2) =
      ((Real.cosh (2*y) - Real.cos lam : ℝ) : ℂ) := by
    have h := sinh_shift_product (y : ℂ) (t / 2)
    rw [show 2 * (t / 2) = t by ring,
      show Complex.cosh t = (Real.cos lam : ℂ) by
        dsimp [t]
        rw [mul_comm Complex.I, Complex.cosh_mul_I]
        simp] at h
    simpa using h
  have hcoef : ((2 * Real.pi * kernelS lam y : ℝ) : ℂ) =
      2 * (Real.sin lam : ℂ) / ((Real.cosh (2*y) - Real.cos lam : ℝ) : ℂ) := by
    simp [kernelS]
    have hp : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp [hp]
    <;> ring
  have hsin : Complex.sinh t = Complex.I * (Real.sin lam : ℂ) := by
    dsimp [t]
    rw [sinh_physical_deformation]
    simp
  have hderiv : (-Complex.I * Complex.sinh t) / Complex.sinh ((y : ℂ) - t/2)^2 =
      ((2 * Real.pi * kernelS lam y : ℝ) : ℂ) *
        (Complex.sinh ((y : ℂ) + t/2) / Complex.sinh ((y : ℂ) - t/2)) := by
    rw [hsin, hcoef]
    have hdenpos : 0 < Real.cosh (2*y) - Real.cos lam := by
      have hh := phase_denominator_pos (lam/2) y
        (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos,hpi])).ne'
      simpa only [show 2 * (lam / 2) = lam by ring] using hh
    have hDne : (2 * Complex.sinh ((y : ℂ) - t/2) *
        Complex.sinh ((y : ℂ) + t/2)) ≠ 0 := by
      rw [hprod]
      exact Complex.ofReal_ne_zero.mpr hdenpos.ne'
    rw [← hprod]
    have hplus : Complex.sinh ((y : ℂ) + t/2) ≠ 0 := by
      intro hz
      apply hDne
      rw [hz]
      simp
    have hminusAlt : Complex.sinh ((↑y * 2 - t) / 2) ≠ 0 := by
      convert hd using 1 <;> push_cast <;> ring
    have hplusAlt : Complex.sinh ((↑y * 2 + t) / 2) ≠ 0 := by
      convert hplus using 1 <;> push_cast <;> ring
    field_simp [hd, hplus, hminusAlt, hplusAlt, hDne]
    simp only [Complex.I_sq]
    <;> ring
  have heq : (fun z : ℂ => betheF t
      ((y : ℂ) - betheSwapCoordinate lam z)) =
      (fun z : ℂ => betheF t ((y : ℂ) - (t/2 - Complex.I*z))) := by
    funext z
    dsimp [betheSwapCoordinate, t]
  rw [← heq] at hbase
  rw [hderiv] at hbase
  have hval : betheF t ((y : ℂ) - betheSwapCoordinate lam 0) =
      Complex.sinh ((y : ℂ) + t / 2) / Complex.sinh ((y : ℂ) - t / 2) := by
    simp only [betheF]
    congr 1 <;> dsimp [betheSwapCoordinate, t] <;> push_cast <;> ring
  rw [hval]
  exact hbase


private theorem general_vacuumL_swap_hasDerivAt (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (L : ℕ) (hL : 2 ≤ L) :
    HasDerivAt (fun z : ℂ => vacuumL (Complex.I * (lam : ℂ)) (fun _ => 0)
      (betheSwapCoordinate lam z) L) 0 0 := by
  let t : ℂ := Complex.I * (lam : ℂ)
  let f : ℂ → ℂ := fun z => Complex.sinh (-Complex.I * z) / Complex.sinh t
  have ht : Complex.sinh t ≠ 0 := by
    dsimp [t]
    exact physical_deformation_ne_zero lam h0 hpi
  have harg : HasDerivAt (fun z : ℂ => -Complex.I*z) (-Complex.I) 0 := by
    simpa only [id_eq, mul_one] using
      (hasDerivAt_id (0 : ℂ)).const_mul (-Complex.I)
  have hf : HasDerivAt f
      ((-Complex.I * Complex.cosh 0) / Complex.sinh t) 0 := by
    dsimp [f]
    have hsinh : HasDerivAt Complex.sinh (Complex.cosh 0) (-Complex.I*0) := by
      simpa using Complex.hasDerivAt_sinh 0
    convert (hsinh.comp 0 harg).div_const (Complex.sinh t) using 1
    · ext z
      simp [Function.comp_apply,div_eq_mul_inv,mul_comm]
    · ring
  have hf0 : f 0 = 0 := by simp [f,ht]
  have hpow := hf.fun_pow L
  have hpow0 : HasDerivAt (fun z : ℂ => f z ^ L) 0 0 := by
    rw [hf0] at hpow
    have hn : L - 1 ≠ 0 := by omega
    simpa [hn] using hpow
  have hprod : ∀ z, vacuumL (Complex.I * (lam : ℂ)) (fun _ => 0)
      (betheSwapCoordinate lam z) L = f z ^ L := by
    intro z
    rw [vacuumL_product]
    have harg' : ∀ j : ℕ, betheSwapCoordinate lam z - (0 : ℂ) - t/2 = -Complex.I*z := by
      intro j
      dsimp [betheSwapCoordinate,t]
      push_cast
      ring
    calc
      _ = ∏ j ∈ Finset.range L, f z := by
        apply Finset.prod_congr rfl
        intro j hj
        dsimp [f]
        rw [harg' j]
      _ = f z ^ L := by simp [Finset.card_range]
  exact hpow0.congr_of_eventuallyEq (Filter.Eventually.of_forall hprod)

/-- For every finite set of real roots, the homogeneous ABA transfer
 eigenvalue has the exact physical logarithmic derivative. The lower vacuum
 term vanishes to order at least two, while each Bethe factor contributes the
 physical kernel. -/
theorem homogeneous_aba_swap_hasDerivAt {n : ℕ} (lam : ℝ) (h0 : 0 < lam)
    (hpi : lam < Real.pi) (L : ℕ) (hL : 2 ≤ L)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) :
    HasDerivAt (fun z : ℂ => abaEigenvalue (Complex.I*(lam : ℂ)) (fun _ => 0)
      L 0 (rootSet Y) (betheSwapCoordinate lam z))
      (((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ) *
        abaEigenvalue (Complex.I*(lam : ℂ)) (fun _ => 0)
          L 0 (rootSet Y) (betheSwapCoordinate lam 0)) 0 := by
  classical
  let t : ℂ := Complex.I*(lam : ℂ)
  let F : Fin n → ℂ → ℂ := fun j z => betheF t ((Y j : ℂ)-betheSwapCoordinate lam z)
  let G : Fin n → ℂ → ℂ := fun j z => betheF t (betheSwapCoordinate lam z-(Y j : ℂ))
  have hF := finite_product_log_derivative Finset.univ F
    (fun j => ((2*Real.pi*kernelS lam (Y j) : ℝ) : ℂ))
    (fun j _ => physical_betheFactor_swap_kernel_deriv lam h0 hpi (Y j))
  have hprodF : ∀ z, (∏ p ∈ rootSet Y, betheF t (p-betheSwapCoordinate lam z)) = ∏ j,F j z := by
    intro z
    rw [prod_rootSet Y hY]
  have hFroot := hF.congr_of_eventuallyEq (Filter.Eventually.of_forall hprodF)
  have hGdiff : DifferentiableAt ℂ (fun z => ∏ p ∈ rootSet Y,
      betheF t (betheSwapCoordinate lam z-p)) 0 := by
    rw [show (fun z => ∏ p ∈ rootSet Y, betheF t (betheSwapCoordinate lam z-p)) =
      (fun z => ∏ j,G j z) by
        funext z
        rw [prod_rootSet Y hY]]
    apply DifferentiableAt.fun_finsetProd
    intro j hj
    have hs : Real.sin (lam/2) ≠ 0 :=
      (Real.sin_pos_of_pos_of_lt_pi (by positivity) (by linarith [Real.pi_pos,hpi])).ne'
    have hd : Complex.sinh (betheSwapCoordinate lam 0-(Y j : ℂ)) ≠ 0 := by
      have h := sinh_real_shift_ne_zero (-Y j) (lam/2) hs
      convert h using 1 <;> dsimp [betheSwapCoordinate] <;> push_cast <;> ring
    have hcoord : DifferentiableAt ℂ (fun z : ℂ => betheSwapCoordinate lam z - (Y j : ℂ)) 0 := by
      unfold betheSwapCoordinate
      fun_prop
    exact (betheF_differentiableAt t _ hd).comp 0 hcoord
  have hA := homogeneous_vacuumA_swap_hasDerivAt lam h0 hpi L
  have hA0 : vacuumA (Complex.I*(lam : ℂ)) (fun _ => 0)
      (betheSwapCoordinate lam 0) L = 1 := by
    have htnz : Complex.sinh (Complex.I*(lam : ℂ)) ≠ 0 :=
      physical_deformation_ne_zero lam h0 hpi
    rw [vacuumA_product]
    simp [betheSwapCoordinate, htnz]
  have hLvac := general_vacuumL_swap_hasDerivAt lam h0 hpi L hL
  have hL0 : vacuumL (Complex.I*(lam : ℂ)) (fun _ => 0)
      (betheSwapCoordinate lam 0) L = 0 := by
    rw [vacuumL_product]
    have hLne : L ≠ 0 := by omega
    simp [betheSwapCoordinate, hLne]
  have hsum : (∑ j : Fin n, ((2*Real.pi*kernelS lam (Y j) : ℝ) : ℂ)) =
      (((2*Real.pi*∑ j,kernelS lam (Y j) : ℝ) : ℂ)) := by
    push_cast
    rw [Finset.mul_sum]
  have hupper : HasDerivAt (fun z : ℂ =>
      vacuumA t (fun _ => 0) (betheSwapCoordinate lam z) L *
        (∏ p ∈ rootSet Y, betheF t (p-betheSwapCoordinate lam z)))
      (((2*Real.pi*∑ j,kernelS lam (Y j) - (L : ℝ)*Real.cot lam : ℝ) : ℂ) *
        (∏ p ∈ rootSet Y, betheF t (p-betheSwapCoordinate lam 0))) 0 := by
    have h := hA.mul hFroot
    rw [hA0] at h
    rw [← hprodF 0] at h
    convert h using 1
    rw [hsum]
    have hprod0 : (∏ p ∈ rootSet Y, betheF t (p-betheSwapCoordinate lam 0)) =
        ∏ p ∈ rootSet Y, betheF t (-betheSwapCoordinate lam 0+p) := by
      apply Finset.prod_congr rfl
      intro p hp
      congr 2 <;> ring
    rw [hprod0]
    push_cast
    ring
  have hlower : HasDerivAt (fun z : ℂ =>
      vacuumL t (fun _ => 0) (betheSwapCoordinate lam z) L *
        (∏ p ∈ rootSet Y, betheF t (betheSwapCoordinate lam z-p))) 0 0 := by
    convert hLvac.mul hGdiff.hasDerivAt using 1 <;> simp [hL0]
  have hfun : (fun z : ℂ => abaEigenvalue t (fun _ => 0) L 0 (rootSet Y)
      (betheSwapCoordinate lam z)) = (fun z =>
      vacuumA t (fun _ => 0) (betheSwapCoordinate lam z) L *
        (∏ p ∈ rootSet Y, betheF t (p-betheSwapCoordinate lam z)) +
      vacuumL t (fun _ => 0) (betheSwapCoordinate lam z) L *
        (∏ p ∈ rootSet Y, betheF t (betheSwapCoordinate lam z-p))) := by
    funext z
    simp [abaEigenvalue,t]
  rw [hfun]
  have h := hupper.add hlower
  have hval : abaEigenvalue t (fun _ => 0) L 0 (rootSet Y)
      (betheSwapCoordinate lam 0) =
      ∏ p ∈ rootSet Y, betheF t (p-betheSwapCoordinate lam 0) := by
    simp [abaEigenvalue,t,hA0,hL0]
  rw [hval]
  convert h using 1 <;> simp

end
end SixVertex
