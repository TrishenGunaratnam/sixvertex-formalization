import SixVertex.MatrixPositivePowers

namespace SixVertex
noncomputable section

/-- A nonnegative matrix with positive diagonal cannot have a nonpositive
eigenvalue with a strictly positive real eigenvector. -/
theorem positive_eigenvalue_of_nonnegative_diagonal {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Matrix V V ℝ) (hB : ∀ i j,0≤B i j) (hd : ∀ i,0<B i i)
    (v : V → ℝ) (hv : ∀ i,0<v i) (tau : ℝ) (heig : B.mulVec v=tau • v) : 0<tau := by
  classical
  let i : V := Classical.choice inferInstance
  have hs : 0<∑ j : V,B i j*v j :=
    Finset.sum_pos' (fun j _ => mul_nonneg (hB i j) (hv j).le)
      ⟨i,Finset.mem_univ i,mul_pos (hd i) (hv i)⟩
  have he := congrFun heig i
  change (∑ j : V,B i j*v j)=tau*v i at he
  rw [he] at hs
  by_contra ht
  have hnonpos : tau≤0 := le_of_not_gt ht
  have hp := mul_nonpos_of_nonpos_of_nonneg hnonpos (hv i).le
  exact (not_lt_of_ge hp) hs

/-- A complex eigenvalue attached to a positive real eigenvector of a
real matrix is real,and the corresponding real eigen-equation holds. -/
theorem positive_real_eigenvector_complex_root_real {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Matrix V V ℝ) (v : V → ℝ) (hv : ∀ i,0<v i) (tau : ℂ)
    (heig : (B.map Complex.ofReal).mulVec (fun i => (v i : ℂ))=tau • (fun i => (v i : ℂ))) :
    tau=(tau.re : ℂ) ∧ B.mulVec v=tau.re • v := by
  classical
  constructor
  · apply Complex.ext
    · rfl
    · let i : V := Classical.choice inferInstance
      have h := congrArg Complex.im (congrFun heig i)
      simp only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
        Complex.im_sum,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,
        zero_add,add_zero,Finset.sum_const_zero] at h
      exact (mul_eq_zero.mp h.symm).resolve_right (hv i).ne'
  · funext i
    have h := congrArg Complex.re (congrFun heig i)
    simpa only [Matrix.mulVec,dotProduct,Matrix.map_apply,Pi.smul_apply,smul_eq_mul,
      Complex.re_sum,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,mul_zero,zero_mul,sub_zero] using h

/-- A positive real eigenvector bounds the modulus of every complex
eigenvalue of a nonnegative matrix. The proof uses the maximal weighted
coordinate norm;no Perron theorem is assumed. -/
theorem positive_eigenvector_bounds_complex_eigenvalues {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Matrix V V ℝ) (hB : ∀ i j,0≤B i j) (v : V → ℝ) (hv : ∀ i,0<v i)
    (tau : ℝ) (heig : B.mulVec v=tau • v) (mu : ℂ) (w : V → ℂ) (hw : w≠0)
    (hwe : (B.map Complex.ofReal).mulVec w=mu • w) : ‖mu‖≤tau := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ (fun j => ‖w j‖/v j) Finset.univ_nonempty
  let m : ℝ := ‖w i‖/v i
  have hwi : 0<‖w i‖ := by
    by_contra hn
    have hi0 : ‖w i‖=0 := le_antisymm (le_of_not_gt hn) (norm_nonneg _)
    apply hw
    funext j
    apply norm_eq_zero.mp
    have hh := hmax j (Finset.mem_univ j)
    rw [hi0,zero_div] at hh
    apply le_antisymm _ (norm_nonneg _)
    simpa using (div_le_iff₀ (hv j)).mp hh
  have hm (j : V) : ‖w j‖≤m*v j := (div_le_iff₀ (hv j)).mp (hmax j (Finset.mem_univ j))
  have hmi : m*v i=‖w i‖ := div_mul_cancel₀ _ (hv i).ne'
  have hwe_i := congrFun hwe i
  change (∑ j : V,(B i j : ℂ)*w j)=mu*w i at hwe_i
  have he_i := congrFun heig i
  change (∑ j : V,B i j*v j)=tau*v i at he_i
  have hbound : ‖mu‖*‖w i‖≤tau*‖w i‖ := by
    calc
      ‖mu‖*‖w i‖=‖∑ j : V,(B i j : ℂ)*w j‖ := by rw [← norm_mul,hwe_i]
      _ ≤ ∑ j : V,‖(B i j : ℂ)*w j‖ := norm_sum_le _ _
      _ = ∑ j : V,B i j*‖w j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hB i j)]
      _ ≤ ∑ j : V,B i j*(m*v j) :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hm j) (hB i j))
      _ = m*(∑ j : V,B i j*v j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = m*(tau*v i) := by rw [he_i]
      _ = tau*‖w i‖ := by calc
        _ = tau*(m*v i) := by ring
        _ = _ := by rw [hmi]
  exact (mul_le_mul_iff_left₀ hwi).mp (by simpa only [mul_comm] using hbound)

/-- A positive eigenvector of a nonnegative matrix with a connected
positive-entry graph spans its real eigenspace at that eigenvalue. -/
theorem positive_eigenvector_nonnegative_eigenspace_simple {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (B : Matrix V V ℝ) (hB : ∀ i j,0≤B i j) (G : SimpleGraph V) (hG : G.Preconnected)
    (hedge : ∀ i j,G.Adj i j → 0<B i j) (v : V → ℝ) (hv : ∀ i,0<v i)
    (tau : ℝ) (heig : B.mulVec v=tau • v) (w : V → ℝ) (hw : B.mulVec w=tau • w) :
    ∃ c : ℝ,w=c • v := by
  have hneg (f : V → ℝ) (hf : B.mulVec f=tau • f) : (-B).mulVec f=(-tau) • f := by
    funext i
    have h := congrArg Neg.neg (congrFun hf i)
    simpa only [Matrix.mulVec,dotProduct,Matrix.neg_apply,neg_mul,Finset.sum_neg_distrib,
      Pi.smul_apply,smul_eq_mul] using h
  apply positive_eigenvector_eigenspace_simple (-B) _ G hG _ v hv (-tau) (hneg v heig) w (hneg w hw)
  · intro i j _
    exact neg_nonpos.mpr (hB i j)
  · intro i j h
    exact neg_neg_of_pos (hedge i j h)

end
end SixVertex
