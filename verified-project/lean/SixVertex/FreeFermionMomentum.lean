import SixVertex.FreeFermionRoots
import SixVertex.BethePhaseData

namespace SixVertex
noncomputable section

/-- The physical sign convention fixes momentum as minus the counting phase. -/
def physicalRootMomentum (lam u : ℝ) : ℝ := -2*Real.pi*countingS lam u

/-- Exact physical shift phase,including the sign gauge in the paper. -/
theorem physicalRootMomentum_phase (lam u : ℝ) (h0 : 0<lam) (hpi : lam<Real.pi) :
    Complex.exp (Complex.I*(physicalRootMomentum lam u : ℂ))=
      -betheF (Complex.I*(lam : ℂ)) ((u : ℂ)-Complex.I*(lam : ℂ)/2) := by
  have hs : Real.sin (lam/2)≠0 :=
    (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])).ne'
  have h := shifted_ratio_upper (lam/2) u hs
  have he : (u : ℂ)-Complex.I*(lam : ℂ)/2+Complex.I*(lam : ℂ)=
      (u : ℂ)+Complex.I*(lam/2 : ℝ) := by push_cast;ring
  have hd : (u : ℂ)-Complex.I*(lam : ℂ)/2=(u : ℂ)-Complex.I*(lam/2 : ℝ) := by
    push_cast;ring
  unfold betheF
  rw [he,hd,h]
  simp only [neg_neg]
  congr 1
  simp only [physicalRootMomentum,countingS,Complex.ofReal_mul,Complex.ofReal_neg,
    Complex.ofReal_ofNat]
  ring

/-- The real branch of the physical momentum at the free point. -/
theorem physicalRootMomentum_freeFermion (u : ℝ) :
    physicalRootMomentum (Real.pi/2) u = -2*Real.arctan (Real.tanh u) := by
  rw [physicalRootMomentum,countingS_freeFermion]
  field_simp

/-- Exact cosine dispersion in the physical momentum convention. -/
theorem freeFermion_momentum_cos (u : ℝ) :
    Real.cos (physicalRootMomentum (Real.pi/2) u)=1/Real.cosh (2*u) := by
  rw [physicalRootMomentum_freeFermion,show -2*Real.arctan (Real.tanh u)=
    -(2*Real.arctan (Real.tanh u)) by ring,Real.cos_neg,Real.cos_two_mul,
    Real.cos_sq_arctan,Real.tanh_eq_sinh_div_cosh,Real.cosh_two_mul]
  have hc : Real.cosh u≠0 := (Real.cosh_pos u).ne'
  have hh : Real.cosh u^2+Real.sinh u^2≠0 := by positivity
  have ht : 1+(Real.sinh u/Real.cosh u)^2≠0 := by positivity
  field_simp [hc,hh,ht]
  nlinarith [Real.cosh_sq u]

/-- The actual source kernel at the free point. -/
theorem kernelS_freeFermion (u : ℝ) :
    kernelS (Real.pi/2) u=1/(Real.pi*Real.cosh (2*u)) := by
  simp [kernelS,Real.sin_pi_div_two,Real.cos_pi_div_two]

/-- At eta=1/2,the paper's one-root Hamiltonian energy is exactly -cos p. -/
theorem freeFermion_root_energy (u : ℝ) :
    -2*Real.pi*(1/2)*kernelS (Real.pi/2) u=
      -Real.cos (physicalRootMomentum (Real.pi/2) u) := by
  rw [kernelS_freeFermion,freeFermion_momentum_cos]
  field_simp

/-- Homogeneous free-point roots give the precise centered momentum grid.
The minus sign reverses the order of the increasing rapidities. -/
theorem consecutiveRoots_freeFermion_momentum {n : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin n → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0) (j : Fin n) :
    physicalRootMomentum (Real.pi/2) (Y j)=
      Real.pi*((n : ℝ)-1-2*(j.val : ℝ))/(L : ℝ) := by
  have h := congrFun hY.2 j
  change countingXi (Real.pi/2) (fun _ => 0) L Y (Y j)=countingTarget n 0 j at h
  rw [countingXi_freeFermion] at h
  simp only [freeFermionCounting,sub_zero,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at h
  unfold countingTarget at h
  norm_num at h
  unfold physicalRootMomentum
  have hL' : (L : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hL)
  apply (eq_div_iff hL').mpr
  linear_combination (-2*Real.pi)*h

/-- The momentum spacing and centering follow from the actual root equations. -/
theorem consecutiveRoots_freeFermion_momentum_center {n : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin n → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0)
    (i j : Fin n) (hij : i.val+j.val+1=n) :
    physicalRootMomentum (Real.pi/2) (Y i)=
      -physicalRootMomentum (Real.pi/2) (Y j) := by
  rw [consecutiveRoots_freeFermion_momentum L hL Y hY i,
    consecutiveRoots_freeFermion_momentum L hL Y hY j]
  have hc : (i.val : ℝ)+(j.val : ℝ)+1=n := by exact_mod_cast hij
  rw [← hc]
  ring

/-- Every occupied momentum satisfies the fermionic circle sign. -/
theorem consecutiveRoots_freeFermion_circle_sign {n : ℕ} (L : ℕ) (hL : 0<L)
    (Y : Fin n → ℝ) (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0) (j : Fin n) :
    Complex.exp (Complex.I*((L : ℝ)*physicalRootMomentum (Real.pi/2) (Y j) : ℝ))=
      (-1 : ℂ)^(n-1) := by
  have hm := consecutiveRoots_freeFermion_momentum L hL Y hY j
  have hL' : (L : ℝ)≠0 := by exact_mod_cast (Nat.ne_of_gt hL)
  have hmul : (L : ℝ)*physicalRootMomentum (Real.pi/2) (Y j)=
      Real.pi*((n : ℝ)-1-2*(j.val : ℝ)) := by
    rw [hm]
    field_simp
  have he : Complex.I*(((L : ℝ)*physicalRootMomentum (Real.pi/2) (Y j) : ℝ) : ℂ)=
      ((n+1 : ℕ) : ℂ)*((Real.pi : ℂ)*Complex.I)-
        ((j.val+1 : ℕ) : ℂ)*(2*(Real.pi : ℂ)*Complex.I) := by
    rw [hmul]
    push_cast
    ring
  rw [he,sub_eq_add_neg,Complex.exp_add,Complex.exp_nat_mul,
    Complex.exp_pi_mul_I,Complex.exp_neg,Complex.exp_nat_mul_two_pi_mul_I]
  have hn : n+1=(n-1)+2 := by have := j.isLt;omega
  rw [hn,pow_add]
  norm_num

/-- The occupied free-point momenta lie strictly in the central half-circle. -/
theorem consecutiveRoots_freeFermion_momentum_bound {n : ℕ} (L : ℕ) (hL : 0<L)
    (hfill : 2*n≤L) (Y : Fin n → ℝ)
    (hY : ConsecutiveRoots (Real.pi/2) (fun _ => 0) L Y 0) (j : Fin n) :
    |physicalRootMomentum (Real.pi/2) (Y j)|<Real.pi/2 := by
  rw [consecutiveRoots_freeFermion_momentum L hL Y hY j]
  have hL' : (0 : ℝ)<L := by exact_mod_cast hL
  have hj : (j.val : ℝ)+1≤n := by exact_mod_cast (Nat.succ_le_of_lt j.isLt)
  have hj0 : (0 : ℝ)≤j.val := Nat.cast_nonneg _
  have hf : (2 : ℝ)*n≤L := by exact_mod_cast hfill
  apply abs_lt.mpr
  constructor
  · apply (lt_div_iff₀ hL').mpr
    nlinarith [Real.pi_pos]
  · apply (div_lt_iff₀ hL').mpr
    nlinarith [Real.pi_pos]

end
end SixVertex
