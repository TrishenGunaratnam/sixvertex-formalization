import SixVertex.FreeSlaterVandermonde
import Mathlib.Order.Interval.Finset.Fin

namespace SixVertex
noncomputable section

/-- Each coordinate occurs n-1 times in the ordered-pair phase sum. -/
theorem sum_ordered_pair_coordinates {n : ℕ} (x : Fin n → ℂ) :
    (∑ i,∑ j ∈ Finset.Ioi i,(x i+x j))=((n-1 : ℕ) : ℂ)*(∑ i,x i) := by
  have hs : (∑ i,∑ j ∈ Finset.Ioi i,x j)=∑ j,∑ i ∈ Finset.Iio j,x j := by
    simp_rw [← Finset.filter_lt_eq_Ioi,← Finset.filter_gt_eq_Iio,Finset.sum_filter]
    exact Finset.sum_comm
  simp_rw [Finset.sum_add_distrib]
  rw [hs]
  simp only [Finset.sum_const,Fin.card_Ioi,Fin.card_Iio,nsmul_eq_mul]
  rw [← Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi : n-1-i.val+i.val=n-1 := by have := i.isLt;omega
  have hc : (((n-1-i.val : ℕ) : ℂ)+(i.val : ℂ))=((n-1 : ℕ) : ℂ) := by exact_mod_cast hi
  rw [← add_mul,hc]

/-- Exact difference of two Fourier site phases in sine form. -/
theorem freeSitePhase_sub_sine (L : ℕ) (x y : ℤ) :
    freeSitePhase L y-freeSitePhase L x=
      (-2*Complex.I)*Complex.exp (Complex.I*((-Real.pi*((x : ℝ)+(y : ℝ))/(L : ℝ) : ℝ) : ℂ))*
        (Real.sin (Real.pi*((y : ℝ)-(x : ℝ))/(L : ℝ)) : ℂ) := by
  let a : ℂ := Complex.I*((-Real.pi*((x : ℝ)+(y : ℝ))/(L : ℝ) : ℝ) : ℂ)
  let t : ℂ := ((Real.pi*((y : ℝ)-(x : ℝ))/(L : ℝ) : ℝ) : ℂ)
  have hy : Complex.exp a*Complex.exp (-t*Complex.I)=freeSitePhase L y := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [a,t,freeSitePhase]
    push_cast
    ring
  have hx : Complex.exp a*Complex.exp (t*Complex.I)=freeSitePhase L x := by
    rw [← Complex.exp_add]
    congr 1
    dsimp [a,t,freeSitePhase]
    push_cast
    ring
  change _=(-2*Complex.I)*Complex.exp a*(Real.sin _ : ℂ)
  rw [Complex.ofReal_sin]
  change _=(-2*Complex.I)*Complex.exp a*Complex.sin t
  calc
    _ = Complex.exp a*Complex.exp (-t*Complex.I)-Complex.exp a*Complex.exp (t*Complex.I) := by rw [hy,hx]
    _ = _ := by
      rw [Complex.sin]
      ring_nf
      simp only [Complex.I_sq]
      ring

/-- The sine Vandermonde amplitude is strictly positive on ordered
configurations contained in one period. -/
theorem ordered_sine_vandermonde_pos {n : ℕ} (L : ℕ) (hL : 0<L)
    (x : Fin n → ℤ) (hx : StrictMono x) (hx0 : ∀ i,0≤x i) (hxL : ∀ i,x i<(L : ℤ)) :
    0<∏ i,∏ j ∈ Finset.Ioi i,Real.sin (Real.pi*((x j : ℝ)-(x i : ℝ))/(L : ℝ)) := by
  have hL' : (0 : ℝ)<L := by exact_mod_cast hL
  apply Finset.prod_pos
  intro i _
  apply Finset.prod_pos
  intro j hj
  have hxy : (x i : ℝ)<x j := by exact_mod_cast hx (Finset.mem_Ioi.mp hj)
  have h0 : (0 : ℝ)≤x i := by exact_mod_cast hx0 i
  have htop : (x j : ℝ)<L := by exact_mod_cast hxL j
  apply Real.sin_pos_of_pos_of_lt_pi
  · exact div_pos (mul_pos Real.pi_pos (sub_pos.mpr hxy)) hL'
  · apply (div_lt_iff₀ hL').mpr
    nlinarith [Real.pi_pos]

/-- A fixed phase depending only on particle number,not on the configuration. -/
def freeSlaterPhase (n : ℕ) : ℂ := ∏ i : Fin n,∏ _j ∈ Finset.Ioi i,(-2*Complex.I)

/-- The entire configuration-dependent phase cancels,leaving a positive
sine Vandermonde times one fixed particle-number phase. -/
theorem freeSlaterWave_sine_product {n : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin n → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0) (x : Fin n → ℤ) :
    freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j)) x=
      freeSlaterPhase n*((∏ i,∏ j ∈ Finset.Ioi i,
        Real.sin (Real.pi*((x j : ℝ)-(x i : ℝ))/(L : ℝ)) : ℝ) : ℂ) := by
  classical
  by_cases hn : n=0
  · subst n
    have he : freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j)) x=1 := by
      exact Matrix.det_isEmpty (A := (fun (i j : Fin 0) =>
        freePlaneWave (physicalRootMomentum (Real.pi/2) (Y j)) (x i)))
    rw [he]
    simp [freeSlaterPhase]
  let c : ℂ := Complex.I*(Real.pi : ℂ)/(L : ℂ)
  let v : Fin n → ℂ := fun i => (x i : ℂ)
  have hb (i : Fin n) : Complex.I*((Real.pi*((n : ℝ)-1)*(x i : ℝ)/(L : ℝ) : ℝ) : ℂ)=
      c*((n : ℂ)-1)*v i := by dsimp [c,v];push_cast;ring
  have he (i j : Fin n) : Complex.I*((-Real.pi*((x i : ℝ)+(x j : ℝ))/(L : ℝ) : ℝ) : ℂ)=
      -c*(v i+v j) := by dsimp [c,v];push_cast;ring
  have hc : ((n-1 : ℕ) : ℂ)=(n : ℂ)-1 := by
    rw [Nat.cast_sub (by omega : 1≤n)]
    norm_num
  have hphase :
      (∏ i,Complex.exp (Complex.I*((Real.pi*((n : ℝ)-1)*(x i : ℝ)/(L : ℝ) : ℝ) : ℂ)))*
      (∏ i,∏ j ∈ Finset.Ioi i,
        Complex.exp (Complex.I*((-Real.pi*((x i : ℝ)+(x j : ℝ))/(L : ℝ) : ℝ) : ℂ)))=1 := by
    simp_rw [hb,he,← Complex.exp_sum]
    rw [← Complex.exp_add]
    have hp := sum_ordered_pair_coordinates v
    rw [hc] at hp
    have hz : (∑ i,c*((n : ℂ)-1)*v i)+(∑ i,∑ j ∈ Finset.Ioi i,-c*(v i+v j))=0 := by
      simp_rw [← Finset.mul_sum]
      rw [hp]
      ring
    rw [hz,Complex.exp_zero]
  rw [freeSlaterWave_vandermonde L hL Y hY x,Matrix.det_vandermonde]
  simp_rw [freeSitePhase_sub_sine,Finset.prod_mul_distrib]
  have hcast : (∏ i,∏ j ∈ Finset.Ioi i,
      (Real.sin (Real.pi*((x j : ℝ)-(x i : ℝ))/(L : ℝ)) : ℂ))=
      ((∏ i,∏ j ∈ Finset.Ioi i,
        Real.sin (Real.pi*((x j : ℝ)-(x i : ℝ))/(L : ℝ)) : ℝ) : ℂ) := by
    simp only [Complex.ofReal_prod]
  rw [hcast]
  have hprod := congrArg (fun z : ℂ => freeSlaterPhase n*
    ((∏ i,∏ j ∈ Finset.Ioi i,
      Real.sin (Real.pi*((x j : ℝ)-(x i : ℝ))/(L : ℝ)) : ℝ) : ℂ)*z) hphase
  dsimp [freeSlaterPhase] at hprod ⊢
  simp only [Finset.prod_mul_distrib] at hprod ⊢
  linear_combination hprod

/-- One configuration-independent normalization makes every ordered
free-point Slater amplitude real and strictly positive. -/
theorem freeSlaterWave_fixed_phase_positive {n : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin n → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (x : Fin n → ℤ) (hx : StrictMono x) (hx0 : ∀ i,0≤x i) (hxL : ∀ i,x i<(L : ℤ)) :
    let a := freeSlaterWave (fun j => physicalRootMomentum (Real.pi/2) (Y j)) x/freeSlaterPhase n
    a.im=0 ∧ 0<a.re := by
  have hc : freeSlaterPhase n≠0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    exact mul_ne_zero (by norm_num) Complex.I_ne_zero
  dsimp only
  rw [freeSlaterWave_sine_product L hL Y hY x,mul_div_cancel_left₀ _ hc]
  simp only [Complex.ofReal_im,Complex.ofReal_re,true_and]
  exact ordered_sine_vandermonde_pos L hL x hx hx0 hxL

end
end SixVertex
