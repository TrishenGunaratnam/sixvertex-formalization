import SixVertex.MatrixAbsoluteEnergy

namespace SixVertex
noncomputable section
open Metric Module.End

/-- A finite real Hermitian matrix with nonpositive off-diagonals and a
connected strict-negative-entry graph has a strictly positive simple
ground state. The lower energy bound certifies that it is the minimum. -/
theorem exists_positive_simple_ground_state {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : Matrix V V ℝ) (hherm : A.IsHermitian) (hA : ∀ i j,i≠j → A i j≤0)
    (G : SimpleGraph V) (hG : G.Preconnected) (hedge : ∀ i j,G.Adj i j → A i j<0) :
    ∃ (mu : ℝ) (v : V → ℝ), (∀ i,0<v i) ∧ A.mulVec v=mu • v ∧
      (∀ w : V → ℝ,mu*(∑ i : V,(w i)^2)≤realMatrixEnergy A w) ∧
      (∀ w : V → ℝ,A.mulVec w=mu • w → ∃ c : ℝ,w=c • v) := by
  let E := EuclideanSpace ℝ V
  have hsym : A.toEuclideanLin.IsSymmetric := Matrix.isSymmetric_toEuclideanLin_iff.mpr hherm
  let T := hsym.toSelfAdjoint
  have henergy (x : E) : T.val.reApplyInnerSelf x=realMatrixEnergy A (fun i => x i) := by
    change inner ℝ (A.toEuclideanLin x) x=realMatrixEnergy A (fun i => x i)
    exact (realMatrixEnergy_eq_inner A x).symm
  obtain ⟨x,hx⟩ : ∃ x : E,x≠0 := exists_ne 0
  have hr : 0<‖x‖ := norm_pos_iff.mpr hx
  have hcompact : IsCompact (sphere (0 : E) ‖x‖) := isCompact_sphere _ _
  have hnonempty : (sphere (0 : E) ‖x‖).Nonempty := ⟨x,by simp⟩
  obtain ⟨x₀,hx₀,hmin⟩ := hcompact.exists_isMinOn hnonempty T.val.reApplyInnerSelf_continuous.continuousOn
  have hnorm : ‖x₀‖=‖x‖ := by simpa using hx₀
  let v₀ : E := realAbsVector x₀
  have hvnorm : ‖v₀‖=‖x‖ := (realAbsVector_norm x₀).trans hnorm
  have hvne : v₀≠0 := by
    intro h
    have hh := hvnorm
    rw [h,norm_zero] at hh
    exact hr.ne' hh.symm
  have hminabs : IsMinOn T.val.reApplyInnerSelf (sphere (0 : E) ‖v₀‖) v₀ := by
    intro y hy
    calc
      T.val.reApplyInnerSelf v₀≤T.val.reApplyInnerSelf x₀ := by
        rw [henergy,henergy]
        exact realMatrixEnergy_abs_le A hA (fun i => x₀ i)
      _ ≤ T.val.reApplyInnerSelf y := hmin (by simpa only [hvnorm] using hy)
  let mu : ℝ := ⨅ z : {z : E // z≠0},T.val.rayleighQuotient z
  have hev := T.prop.hasEigenvector_of_isMinOn hvne hminabs
  have heig : A.mulVec (fun i => v₀ i)=mu • (fun i => v₀ i) := by
    have he := hev.apply_eq_smul
    funext i
    exact congrArg (fun z : E => z i) he
  have hvnonneg (i : V) : 0≤v₀ i := abs_nonneg _
  have hvfun : (fun i => v₀ i)≠0 := by
    intro h
    apply hvne
    ext i
    exact congrFun h i
  have hvpos := nonnegative_eigenvector_strictly_positive A hA G hG hedge
    (fun i => v₀ i) hvnonneg hvfun mu heig
  refine ⟨mu,(fun i => v₀ i),hvpos,heig,?_,?_⟩
  · intro w
    by_cases hw : w=0
    · subst w
      simp [realMatrixEnergy]
    · let y : E := WithLp.toLp 2 w
      have hy : y≠0 := by
        intro h
        apply hw
        funext i
        exact congrArg (fun z : E => z i) h
      have hb : BddBelow (Set.range (fun z : {z : E // z≠0} => T.val.rayleighQuotient z)) := by
        refine ⟨-‖T.val‖,?_⟩
        rintro a ⟨z,rfl⟩
        exact (abs_le.mp (T.val.rayleighQuotient_le_norm z)).1
      have hmu : mu≤T.val.rayleighQuotient y := ciInf_le hb ⟨y,hy⟩
      have hden : 0<‖y‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hy)
      have hl := (le_div_iff₀ hden).mp hmu
      change mu*‖y‖^2≤T.val.reApplyInnerSelf y at hl
      rw [henergy,EuclideanSpace.real_norm_sq_eq] at hl
      exact hl
  · intro w hw
    exact positive_eigenvector_eigenspace_simple A hA G hG hedge (fun i => v₀ i) hvpos mu heig w hw

end
end SixVertex
