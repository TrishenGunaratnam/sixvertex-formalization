import SixVertex.FreeBetheScalarDerivative
import SixVertex.BetheOnShell

namespace SixVertex
noncomputable section

/-- Finite logarithmic differentiation in a form that needs no division. -/
theorem finite_product_log_derivative {I : Type*} [DecidableEq I]
    (S : Finset I) (f : I → ℂ → ℂ) (c : I → ℂ)
    (hf : ∀ i ∈ S,HasDerivAt (f i) (c i*f i 0) 0) :
    HasDerivAt (fun z => ∏ i ∈ S,f i z)
      ((∑ i ∈ S,c i)*(∏ i ∈ S,f i 0)) 0 := by
  induction S using Finset.induction_on with
  | empty => simpa using hasDerivAt_const (0 : ℂ) (1 : ℂ)
  | @insert i S hi ih =>
    have hh := (hf i (Finset.mem_insert_self i S)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simp only [Finset.prod_insert hi,Finset.sum_insert hi]
    convert hh using 1; ring

theorem betheF_differentiableAt (t x : ℂ) (hx : Complex.sinh x≠0) :
    DifferentiableAt ℂ (betheF t) x := by
  exact (((hasDerivAt_id x).add_const t).csinh.div (Complex.hasDerivAt_sinh x) hx).differentiableAt

theorem free_bethe_reverse_swap_differentiableAt (y : ℝ) :
    DifferentiableAt ℂ (fun z : ℂ => betheF (Complex.I*((Real.pi/2 : ℝ) : ℂ))
      (betheSwapCoordinate (Real.pi/2) z-(y : ℂ))) 0 := by
  have hs : Real.sin (Real.pi/4)≠0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos])).ne'
  have hd : Complex.sinh (betheSwapCoordinate (Real.pi/2) 0-(y : ℂ))≠0 := by
    convert sinh_real_shift_ne_zero (-y) (Real.pi/4) hs using 1
    congr 1
    unfold betheSwapCoordinate
    push_cast
    ring
  have hcoord : DifferentiableAt ℂ (fun z : ℂ => betheSwapCoordinate (Real.pi/2) z-(y : ℂ)) 0 := by
    unfold betheSwapCoordinate
    fun_prop
  exact (betheF_differentiableAt _ _ hd).comp 0 hcoord

/-- The actual ABA eigenvalue in the physical coordinate has logarithmic
derivative twice the sum of the one-particle cosine dispersions. The lower
vacuum term and its derivative both vanish for a chain of length at least two. -/
theorem free_aba_swap_hasDerivAt {particles : ℕ} (n : ℕ) (Y : Fin particles → ℝ)
    (hY : Function.Injective Y) :
    HasDerivAt (fun z : ℂ => abaEigenvalue (Complex.I*((Real.pi/2 : ℝ) : ℂ))
      (fun _ => 0) (n+2) 0 (rootSet Y) (betheSwapCoordinate (Real.pi/2) z))
      ((2*(∑ j,(Real.cos (physicalRootMomentum (Real.pi/2) (Y j)) : ℂ)))*
        abaEigenvalue (Complex.I*((Real.pi/2 : ℝ) : ℂ))
          (fun _ => 0) (n+2) 0 (rootSet Y) (betheSwapCoordinate (Real.pi/2) 0)) 0 := by
  classical
  let F : Fin particles → ℂ → ℂ := fun j z =>
    betheF (Complex.I*((Real.pi/2 : ℝ) : ℂ)) ((Y j : ℂ)-betheSwapCoordinate (Real.pi/2) z)
  let G : Fin particles → ℂ → ℂ := fun j z =>
    betheF (Complex.I*((Real.pi/2 : ℝ) : ℂ)) (betheSwapCoordinate (Real.pi/2) z-(Y j : ℂ))
  have hF := finite_product_log_derivative Finset.univ F
    (fun j => 2*(Real.cos (physicalRootMomentum (Real.pi/2) (Y j)) : ℂ))
    (fun j _ => free_bethe_factor_swap_hasDerivAt (Y j))
  have hG : DifferentiableAt ℂ (fun z => ∏ j,G j z) 0 :=
    DifferentiableAt.fun_finsetProd (fun j _ => free_bethe_reverse_swap_differentiableAt (Y j))
  have hc : HasDerivAt (fun z : ℂ => Complex.cos z^(n+2)) 0 0 := by
    simpa using! (Complex.hasDerivAt_cos (0 : ℂ)).fun_pow (n+2)
  have hs : HasDerivAt (fun z : ℂ => (-Complex.sin z)^(n+2)) 0 0 := by
    have hn : n+2-1=n+1 := by omega
    simpa [hn] using! (Complex.hasDerivAt_sin (0 : ℂ)).neg.fun_pow (n+2)
  have hf (z : ℂ) : abaEigenvalue (Complex.I*((Real.pi/2 : ℝ) : ℂ))
      (fun _ => 0) (n+2) 0 (rootSet Y) (betheSwapCoordinate (Real.pi/2) z)=
      Complex.cos z^(n+2)*(∏ j,F j z)+(-Complex.sin z)^(n+2)*(∏ j,G j z) := by
    simp only [abaEigenvalue,Complex.ofReal_zero,mul_zero,Complex.exp_zero,one_mul,
      (free_vacuum_swap_factors (n+2) z).1,(free_vacuum_swap_factors (n+2) z).2,
      prod_rootSet Y hY,F,G]
  simp_rw [hf]
  convert (hc.mul hF).add (hs.mul hG.hasDerivAt) using 1
  simp only [Complex.sin_zero,Complex.cos_zero,neg_zero,one_pow,zero_pow (by omega : n+2≠0),
    zero_mul,zero_add,add_zero,one_mul,← Finset.mul_sum]

end
end SixVertex
