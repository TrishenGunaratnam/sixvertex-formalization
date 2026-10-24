import SixVertex.PhysicalHoppingSign
import SixVertex.SpinSwapConnectivity

namespace SixVertex
noncomputable section

theorem minusCount_appendSpin (n : ℕ) (q : RowSpins n) (a : Fin 2) :
    minusCount (n+1) (appendSpin n q a)=minusCount n q+a.val := by
  induction n with
  | zero => cases q;simp [minusCount,appendSpin]
  | succ n ih =>
    change q.1.val+minusCount (n+1) (appendSpin n q.2 a)=
      q.1.val+minusCount n q.2+a.val
    rw [ih]
    omega

theorem minusCount_unappendSpin (n : ℕ) (q : RowSpins (n+1)) :
    minusCount (n+1) q=minusCount n (unappendSpin n q).1+(unappendSpin n q).2.val := by
  have h := minusCount_appendSpin n (unappendSpin n q).1 (unappendSpin n q).2
  simpa only [append_unappend] using h

/-- The actual cyclic translation preserves the particle number. -/
theorem minusCount_cyclicSpinTranslation (n : ℕ) (q : RowSpins (n+1)) :
    minusCount (n+1) (cyclicSpinTranslation n q)=minusCount (n+1) q := by
  change minusCount (n+1) (appendSpin n q.2 q.1)= _
  rw [minusCount_appendSpin]
  simp only [minusCount]
  omega

theorem minusCount_cyclic_iterate (n k : ℕ) (q : RowSpins (n+1)) :
    minusCount (n+1) (((cyclicSpinTranslation n : RowSpins (n+1) → RowSpins (n+1))^[k]) q)=
      minusCount (n+1) q := by
  induction k generalizing q with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply,ih,minusCount_cyclicSpinTranslation]

/-- The explicit periodic seam link preserves the total particle number. -/
theorem periodicSeamLink_charge_zero (lam eta : ℝ) (n : ℕ)
    (q r : RowSpins (n+2)) (h : minusCount (n+2) q≠minusCount (n+2) r) :
    periodicSeamLink lam eta n q r=0 := by
  unfold periodicSeamLink
  split_ifs with hm
  · rw [physicalLinkOperator_eq_sixMatrix]
    apply sixMatrix_charge_zero
    intro hp
    have hq := minusCount_unappendSpin n q.2
    have hr := minusCount_unappendSpin n r.2
    rw [hm] at hq
    apply h
    change q.1.val+minusCount (n+1) q.2=r.1.val+minusCount (n+1) r.2
    change (unappendSpin n q.2).2.val+q.1.val=
      (unappendSpin n r.2).2.val+r.1.val at hp
    omega
  · rfl

/-- The actual full logarithmic row Hamiltonian has no entries between
different particle sectors. -/
theorem homogeneousLinkHamiltonian_charge_zero (lam eta : ℝ) (n : ℕ)
    (q r : RowSpins (n+2)) (h : minusCount (n+2) q≠minusCount (n+2) r) :
    homogeneousLinkHamiltonian lam eta (n+1) q r=0 := by
  rw [homogeneousLinkHamiltonian_eq_periodic_links]
  simp only [periodicLinkHamiltonian,Matrix.sum_apply]
  apply Finset.sum_eq_zero
  intro k _
  rw [translatedMatrix_apply]
  apply periodicSeamLink_charge_zero
  simpa only [minusCount_cyclic_iterate (n+1)] using h

/-- The actual Hamiltonian maps each previously defined Bethe particle
sector into itself. -/
theorem homogeneousLinkHamiltonian_sector (lam eta : ℝ) (n : ℕ) (k : ℤ)
    (v : RowSpins (n+2) → ℂ) (hv : SpinSector (n+2) k v) :
    SpinSector (n+2) k ((homogeneousLinkHamiltonian lam eta (n+1)).mulVec v) := by
  intro q hq
  simp only [Matrix.mulVec,dotProduct]
  apply Finset.sum_eq_zero
  intro r _
  by_cases hr : (minusCount (n+2) r : ℤ)=k
  · have hqr : minusCount (n+2) q≠minusCount (n+2) r := by omega
    rw [homogeneousLinkHamiltonian_charge_zero lam eta n q r hqr,zero_mul]
  · rw [hv r hr,mul_zero]

/-- A hop at the first two sites has a strictly negative entry in the
actual full Hamiltonian;the other translated links cannot cancel it. -/
theorem homogeneousLinkHamiltonian_head_hop_re_neg (lam eta : ℝ) (h0 : 0<lam)
    (hpi : lam<Real.pi) (heta : 0<eta) (n : ℕ)
    (a b : Fin 2) (t : RowSpins n) (hab : a≠b) :
    (homogeneousLinkHamiltonian lam eta (n+1) (a,b,t) (b,a,t)).re<0 := by
  have hne : (a,b,t)≠(b,a,t) := by
    intro h
    exact hab (congrArg Prod.fst h)
  rw [homogeneousLinkHamiltonian_eq_periodic_links]
  simp only [periodicLinkHamiltonian,Matrix.sum_apply,Complex.re_sum]
  have hall (k : Fin (n+2)) :
      ((spinPermutation (cyclicSpinTranslation (n+1)).symm^k.val*
        periodicSeamLink lam eta n*spinPermutation (cyclicSpinTranslation (n+1))^k.val)
          (a,b,t) (b,a,t)).re≤0 := by
    rw [translatedMatrix_apply]
    apply periodicSeamLink_offdiag_re_nonpos lam eta h0 hpi heta.le
    intro h
    exact hne (((cyclicSpinTranslation (n+1)).injective.iterate k.val) h)
  have hstrict :
      ((spinPermutation (cyclicSpinTranslation (n+1)).symm^(1 : ℕ)*
        periodicSeamLink lam eta n*spinPermutation (cyclicSpinTranslation (n+1))^(1 : ℕ))
          (a,b,t) (b,a,t)).re<0 := by
    rw [translatedMatrix_apply]
    simp only [Function.iterate_one]
    change (periodicSeamLink lam eta n (b,appendSpin n t a) (a,appendSpin n t b)).re<0
    simp only [periodicSeamLink,unappend_append,ite_true]
    rw [physicalLinkOperator_eq_sixMatrix]
    have hp : (a,b)≠(b,a) := by
      intro h
      exact hab (congrArg Prod.fst h)
    simp only [sixMatrix,if_neg hp,eq_self_iff_true,and_self,ite_true]
    have hc : (-(eta : ℂ)/Complex.sin (lam : ℂ))=((-eta/Real.sin lam : ℝ) : ℂ) := by simp
    rw [hc,Complex.ofReal_re]
    exact div_neg_of_neg_of_pos (neg_neg_of_pos heta) (Real.sin_pos_of_pos_of_lt_pi h0 hpi)
  have hsum := Finset.sum_lt_sum (s:=Finset.univ) (g:=fun _ : Fin (n+2) => (0 : ℝ))
    (fun k _ => hall k) (show ∃ k ∈ (Finset.univ : Finset (Fin (n+2))),
      ((spinPermutation (cyclicSpinTranslation (n+1)).symm^k.val*
        periodicSeamLink lam eta n*spinPermutation (cyclicSpinTranslation (n+1))^k.val)
          (a,b,t) (b,a,t)).re<0 from ⟨⟨1,by omega⟩,Finset.mem_univ _,hstrict⟩)
  simpa using hsum

end
end SixVertex
