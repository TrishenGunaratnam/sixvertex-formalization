import SixVertex.BetheScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Instances.Matrix

namespace SixVertex

open Filter Topology

/-- Standard monodromy entries, with deformation t = i lambda in the paper. -/
noncomputable def betheBlock (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ)
    (a c : Fin 2) : Matrix (RowSpins n) (RowSpins n) ℂ :=
  rowBlock (fun j => hyperbolicR t (x-b j-t/2)) n a c

noncomputable abbrev betheA (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) := betheBlock t b n x 0 0
noncomputable abbrev betheB (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) := betheBlock t b n x 0 1
noncomputable abbrev betheC (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) := betheBlock t b n x 1 0
noncomputable abbrev betheL (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (x : ℂ) := betheBlock t b n x 1 1

theorem bethe_finite_RTT (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (p u : ℂ) (q r : RowSpins n) :
    hyperbolicR t (p-u) *
      forwardRows (fun j => hyperbolicR t (p-b j-t/2))
        (fun j => hyperbolicR t (u-b j-t/2)) n q r =
    reverseRows (fun j => hyperbolicR t (p-b j-t/2))
        (fun j => hyperbolicR t (u-b j-t/2)) n q r * hyperbolicR t (p-u) := by
  apply finite_chain_RTT
  intro j
  have he : (p-b j-t/2)-(u-b j-t/2) = p-u := by ring
  simpa only [he] using hyperbolic_local_RTT t ht (p-b j-t/2) (u-b j-t/2)

theorem bethe_AB (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (p u : ℂ) (hpu : Complex.sinh (p-u) ≠ 0) :
    betheA t b n p * betheB t b n u =
      betheF t (u-p) • (betheB t b n u * betheA t b n p) +
      betheG t (p-u) • (betheB t b n p * betheA t b n u) := by
  ext q r
  have h := congrArg (fun M : Matrix PairSpin PairSpin ℂ => M (0,0) (1,0))
    (bethe_finite_RTT t ht b n u p q r)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    hyperbolicR, sixMatrix, forwardRows, reverseRows] at h
  norm_num at h
  change (Complex.sinh (u-p+t) / Complex.sinh t) *
      (betheB t b n u * betheA t b n p) q r =
    (betheB t b n p * betheA t b n u) q r +
      (betheA t b n p * betheB t b n u) q r *
        (Complex.sinh (u-p) / Complex.sinh t) at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  generalize (betheA t b n p * betheB t b n u) q r = X at h ⊢
  generalize (betheB t b n u * betheA t b n p) q r = Y at h ⊢
  generalize (betheB t b n p * betheA t b n u) q r = Z at h ⊢
  unfold betheF betheG
  have hn : Complex.sinh (u-p) = -Complex.sinh (p-u) := by
    rw [show u-p = -(p-u) by ring, Complex.sinh_neg]
  rw [hn] at h ⊢
  field_simp [ht, hpu] at h ⊢
  linear_combination h

theorem bethe_LB (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (p u : ℂ) (hpu : Complex.sinh (p-u) ≠ 0) :
    betheL t b n p * betheB t b n u =
      betheF t (p-u) • (betheB t b n u * betheL t b n p) +
      betheG t (u-p) • (betheB t b n p * betheL t b n u) := by
  ext q r
  have h := congrArg (fun M : Matrix PairSpin PairSpin ℂ => M (1,0) (1,1))
    (bethe_finite_RTT t ht b n p u q r)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    hyperbolicR, sixMatrix, forwardRows, reverseRows] at h
  norm_num at h
  change (betheB t b n p * betheL t b n u) q r +
      (Complex.sinh (p-u) / Complex.sinh t) * (betheL t b n p * betheB t b n u) q r =
    (betheB t b n u * betheL t b n p) q r * (Complex.sinh (p-u+t) / Complex.sinh t) at h
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  generalize (betheL t b n p * betheB t b n u) q r = X at h ⊢
  generalize (betheB t b n u * betheL t b n p) q r = Y at h ⊢
  generalize (betheB t b n p * betheL t b n u) q r = Z at h ⊢
  unfold betheF betheG
  rw [show u-p = -(p-u) by ring, Complex.sinh_neg]
  field_simp [ht, hpu] at h ⊢
  linear_combination h

theorem bethe_CB (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (p u : ℂ) (hpu : Complex.sinh (p-u) ≠ 0) :
    betheC t b n p * betheB t b n u - betheB t b n u * betheC t b n p =
      betheG t (p-u) •
        (betheA t b n u * betheL t b n p - betheA t b n p * betheL t b n u) := by
  ext q r
  have h := congrArg (fun M : Matrix PairSpin PairSpin ℂ => M (1,0) (0,1))
    (bethe_finite_RTT t ht b n p u q r)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    hyperbolicR, sixMatrix, forwardRows, reverseRows] at h
  norm_num at h
  change (betheA t b n p * betheL t b n u) q r +
      (Complex.sinh (p-u) / Complex.sinh t) * (betheC t b n p * betheB t b n u) q r =
    (betheB t b n u * betheC t b n p) q r * (Complex.sinh (p-u) / Complex.sinh t) +
      (betheA t b n u * betheL t b n p) q r at h
  simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
  generalize (betheC t b n p * betheB t b n u) q r = X at h ⊢
  generalize (betheB t b n u * betheC t b n p) q r = Y at h ⊢
  generalize (betheA t b n p * betheL t b n u) q r = Z at h ⊢
  generalize (betheA t b n u * betheL t b n p) q r = W at h ⊢
  unfold betheG
  field_simp [ht, hpu] at h ⊢
  linear_combination h

theorem bethe_BB_raw (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (p u : ℂ) (q r : RowSpins n) :
    Complex.sinh (p-u+t) * (betheB t b n p * betheB t b n u) q r =
      Complex.sinh (p-u+t) * (betheB t b n u * betheB t b n p) q r := by
  have h := congrArg (fun M : Matrix PairSpin PairSpin ℂ => M (0,0) (1,1))
    (bethe_finite_RTT t ht b n p u q r)
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Fin.sum_univ_two,
    hyperbolicR, sixMatrix, forwardRows, reverseRows] at h
  norm_num at h
  change (Complex.sinh (p-u+t) / Complex.sinh t) *
      (betheB t b n p * betheB t b n u) q r =
    (betheB t b n u * betheB t b n p) q r * (Complex.sinh (p-u+t) / Complex.sinh t) at h
  generalize (betheB t b n p * betheB t b n u) q r = X at h ⊢
  generalize (betheB t b n u * betheB t b n p) q r = Y at h ⊢
  field_simp [ht] at h
  linear_combination h

theorem betheBlock_analytic (t : ℂ) (b : ℕ → ℂ) (n : ℕ)
    (a c : Fin 2) (q r : RowSpins n) (z : ℂ) :
    AnalyticAt ℂ (fun x => betheBlock t b n x a c q r) z := by
  have hlocal : ∀ b : ℂ, ∀ i j : PairSpin,
      AnalyticAt ℂ (fun x => hyperbolicR t (x-b-t/2) i j) z := by
    intro b i j
    have ha : AnalyticAt ℂ (fun x : ℂ => x-b-t/2) z :=
      (analyticAt_id.sub analyticAt_const).sub analyticAt_const
    unfold hyperbolicR sixMatrix
    split_ifs
    · exact (Complex.analyticAt_sinh.comp (ha.add analyticAt_const)).div_const
    · exact (Complex.analyticAt_sinh.comp ha).div_const
    · exact analyticAt_const
    · exact analyticAt_const
  unfold betheBlock
  induction n generalizing b a c with
  | zero => exact analyticAt_const
  | succ n ih =>
    simp only [rowBlock]
    apply Finset.analyticAt_fun_sum
    intro d hd
    exact (hlocal (b 0) _ _).mul (ih (fun j => b (j+1)) d c q.2 r.2)

/-- Creation entries commute for all complex arguments, including zeros of
 the scalar prefactor in the direct RTT component. -/
theorem bethe_BB (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ)
    (n : ℕ) (p u : ℂ) : Commute (betheB t b n p) (betheB t b n u) := by
  change betheB t b n p * betheB t b n u = betheB t b n u * betheB t b n p
  ext q r
  have hn : Complex.sinh (p-p+t) ≠ 0 := by simpa using ht
  have hc : Continuous (fun z : ℂ => Complex.sinh (p-z+t)) :=
    Complex.continuous_sinh.comp ((continuous_const.sub continuous_id).add continuous_const)
  have he : ∀ᶠ z in 𝓝 p, Complex.sinh (p-z+t) ≠ 0 :=
    hc.continuousAt.eventually_ne hn
  have hf : (fun z : ℂ => (betheB t b n p * betheB t b n z) q r) =
      (fun z : ℂ => (betheB t b n z * betheB t b n p) q r) := by
    apply AnalyticOnNhd.eq_of_eventuallyEq (𝕜 := ℂ) (z₀ := p)
    · intro z hz
      simp only [Matrix.mul_apply]
      apply Finset.analyticAt_fun_sum
      intro d hd
      exact analyticAt_const.mul (betheBlock_analytic t b n 0 1 d r z)
    · intro z hz
      simp only [Matrix.mul_apply]
      apply Finset.analyticAt_fun_sum
      intro d hd
      exact (betheBlock_analytic t b n 0 1 q d z).mul analyticAt_const
    · exact he.mono (fun z hz => mul_left_cancel₀ hz (bethe_BB_raw t ht b n p z q r))
  exact congrFun hf u

end SixVertex
