import SixVertex.GroundStateTransferLine

namespace SixVertex
noncomputable section

theorem nonnegative_matrix_pow {V : Type*} [Fintype V] [DecidableEq V]
    (B : Matrix V V ℝ) (hB : ∀ i j,0≤B i j) (k : ℕ) (i j : V) :
    0≤(B^k) i j := by
  induction k generalizing i j with
  | zero => simp only [pow_zero,Matrix.one_apply];split_ifs <;> norm_num
  | succ k ih =>
    rw [pow_succ,Matrix.mul_apply]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (ih i l) (hB l j))

theorem positive_matrix_power_entry_step {V : Type*} [Fintype V] [DecidableEq V]
    (B : Matrix V V ℝ) (hB : ∀ i j,0≤B i j) (hdiag : ∀ i,0<B i i)
    (k : ℕ) (i j : V) (h : 0<(B^k) i j) : 0<(B^(k+1)) i j := by
  rw [pow_succ,Matrix.mul_apply]
  exact Finset.sum_pos' (fun l _ => mul_nonneg (nonnegative_matrix_pow B hB k i l) (hB l j))
    ⟨j,Finset.mem_univ j,mul_pos h (hdiag j)⟩

theorem positive_matrix_power_entry_of_le {V : Type*} [Fintype V] [DecidableEq V]
    (B : Matrix V V ℝ) (hB : ∀ i j,0≤B i j) (hdiag : ∀ i,0<B i i)
    (k m : ℕ) (i j : V) (hkm : k≤m) (h : 0<(B^k) i j) : 0<(B^m) i j := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le hkm
  clear hkm
  induction d with
  | zero => simpa using h
  | succ d ih =>
    exact positive_matrix_power_entry_step B hB hdiag (k+d) i j ih

/-- Every actual positive graph walk gives a positive matrix-power entry. -/
theorem graph_walk_matrix_power_pos {V : Type*} [Fintype V] [DecidableEq V]
    (B : Matrix V V ℝ) (hB : ∀ i j,0≤B i j) (G : SimpleGraph V)
    (hedge : ∀ i j,G.Adj i j → 0<B i j) {i j : V} (p : G.Walk i j) :
    0<(B^p.length) i j := by
  induction p with
  | nil => simp
  | @cons i j k h p ih =>
    rw [SimpleGraph.Walk.length_cons,pow_succ',Matrix.mul_apply]
    exact Finset.sum_pos' (fun l _ => mul_nonneg (hB i l) (nonnegative_matrix_pow B hB p.length l k))
      ⟨j,Finset.mem_univ j,mul_pos (hedge i j h) ih⟩

/-- A connected positive-entry graph and positive diagonal give one
strictly positive matrix power. The exponent is constructed from finitely
many actual graph walks;primitivity is not assumed. -/
theorem connected_nonnegative_matrix_has_positive_power {V : Type*} [Fintype V] [DecidableEq V]
    (B : Matrix V V ℝ) (hB : ∀ i j,0≤B i j) (hdiag : ∀ i,0<B i i)
    (G : SimpleGraph V) (hG : G.Preconnected) (hedge : ∀ i j,G.Adj i j → 0<B i j) :
    ∃ N : ℕ,0<N ∧ ∀ i j,0<(B^N) i j := by
  classical
  let path (i j : V) : G.Walk i j := Classical.choice (hG i j)
  let N : ℕ := 1+Finset.univ.sup (fun ij : V×V => (path ij.1 ij.2).length)
  refine ⟨N,by dsimp [N];omega,?_⟩
  intro i j
  have hN : (path i j).length≤N := by
    have h := Finset.le_sup (f:=fun ij : V×V => (path ij.1 ij.2).length) (Finset.mem_univ (i,j))
    change (path i j).length≤Finset.univ.sup (fun ij : V×V => (path ij.1 ij.2).length) at h
    dsimp [N]
    omega
  exact positive_matrix_power_entry_of_le B hB hdiag (path i j).length N i j hN
    (graph_walk_matrix_power_pos B hB G hedge (path i j))

end
end SixVertex
