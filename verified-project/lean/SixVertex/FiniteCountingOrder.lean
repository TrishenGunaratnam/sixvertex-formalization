import SixVertex.ReferenceResidual

namespace SixVertex
noncomputable section

theorem countingS_strictMono (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi) :
    StrictMono (countingS lam) :=
  strictMono_of_hasDerivAt_pos (fun x => hasDerivAt_countingS lam x h0 hpi)
    (fun x => kernelS_pos lam x h0 hpi)

theorem countingTheta_antitone (lam : ℝ) (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) :
    Antitone (countingTheta lam) := by
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  exact antitone_of_hasDerivAt_nonpos (fun x => hasDerivAt_countingTheta lam x h0 hpi)
    (fun x => kernelK_nonpos lam x hhalf hpi)

/-- A maximum principle for the homogeneous counting system. In the
negative-kernel regime, comparison of the actual equations forces
coordinatewise comparison of arbitrary configurations. -/
theorem homogeneous_countingSystem_order_reflecting {n : ℕ} (lam : ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (L : ℕ) (hL : 0 < L)
    (X Z : Fin n → ℝ)
    (hF : ∀ i, countingSystem lam (fun _ => 0) L X i ≤ countingSystem lam (fun _ => 0) L Z i) :
    ∀ i, X i ≤ Z i := by
  classical
  have h0 : 0 < lam := by linarith [Real.pi_pos]
  intro j
  by_contra hj
  letI : Nonempty (Fin n) := ⟨j⟩
  obtain ⟨i,_,hi⟩ := Finset.univ.exists_max_image (fun k => X k-Z k) Finset.univ_nonempty
  have hij := hi j (Finset.mem_univ j)
  have hpos : Z i < X i := by linarith [lt_of_not_ge hj]
  have htheta : (∑ k : Fin n, countingTheta lam (X i-X k)) ≤
      ∑ k : Fin n, countingTheta lam (Z i-Z k) := by
    apply Finset.sum_le_sum
    intro k _
    apply countingTheta_antitone lam hhalf hpi
    have hh := hi k (Finset.mem_univ k)
    linarith
  have hs := (countingS_strictMono lam h0 hpi) hpos
  have hsL := mul_lt_mul_of_pos_left hs (Nat.cast_pos.mpr hL : (0 : ℝ) < L)
  have hf := hF i
  simp only [countingSystem,countingXi,sub_zero,Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hf
  linarith

/-- Uniform translations leave all interaction differences unchanged. -/
theorem homogeneous_countingSystem_translate {n : ℕ} (lam : ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    countingSystem lam (fun _ => 0) L (fun j => Y j+t) i=
      countingSystem lam (fun _ => 0) L Y i+(L : ℝ)*(countingS lam (Y i+t)-countingS lam (Y i)) := by
  have hdiff (j : Fin n) : Y i+t-(Y j+t)=Y i-Y j := by ring
  simp only [countingSystem,countingXi,sub_zero,Finset.sum_const,Finset.card_range,nsmul_eq_mul,hdiff]
  ring

/-- A concrete sub/supersolution bracket gives a physical displacement
bound for exact roots; the reference configuration need not be on shell. -/
theorem homogeneous_roots_bracket {n : ℕ} (lam : ℝ)
    (hhalf : Real.pi/2 ≤ lam) (hpi : lam < Real.pi) (L : ℕ) (hL : 0 < L)
    (Y Z : Fin n → ℝ) (twist t : ℝ)
    (hZ : countingSystem lam (fun _ => 0) L Z=countingTarget n twist)
    (hlo : ∀ i, countingSystem lam (fun _ => 0) L (fun j => Y j-t) i ≤ countingTarget n twist i)
    (hhi : ∀ i, countingTarget n twist i ≤ countingSystem lam (fun _ => 0) L (fun j => Y j+t) i) :
    ∀ i, |Z i-Y i| ≤ t := by
  have hl := homogeneous_countingSystem_order_reflecting lam hhalf hpi L hL (fun j => Y j-t) Z
    (fun i => by rw [hZ]; exact hlo i)
  have hh := homogeneous_countingSystem_order_reflecting lam hhalf hpi L hL Z (fun j => Y j+t)
    (fun i => by rw [hZ]; exact hhi i)
  intro i
  exact abs_le.mpr ⟨by linarith [hl i],by linarith [hh i]⟩

end
end SixVertex
