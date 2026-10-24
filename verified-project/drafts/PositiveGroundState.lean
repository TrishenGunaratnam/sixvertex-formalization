import SixVertex.PhysicalHamiltonianSector
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

namespace SixVertex
noncomputable section

/-- A zero of a nonnegative real eigenvector propagates across every
strictly negative off-diagonal matrix entry. -/
theorem nonnegative_eigenvector_zero_neighbor {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : ∀ i j,i≠j → A i j≤0)
    (v : V → ℝ) (hv : ∀ i,0≤v i) (mu : ℝ) (heig : A.mulVec v=mu • v)
    (i j : V) (hi : v i=0) (hij : A i j<0) : v j=0 := by
  have hs := congrFun heig i
  change (∑ k : V,A i k*v k)=mu*v i at hs
  rw [hi,mul_zero] at hs
  have hall (k : V) : A i k*v k≤0 := by
    by_cases hki : k=i
    · rw [hki,hi,mul_zero]
    · exact mul_nonpos_of_nonpos_of_nonneg (hA i k (Ne.symm hki)) (hv k)
  have hz : A i j*v j=0 :=
    (Finset.sum_eq_zero_iff_of_nonpos (fun k _ => hall k)).mp hs j (Finset.mem_univ j)
  exact (mul_eq_zero.mp hz).resolve_left hij.ne

/-- On a connected strict-negative-entry graph,every nonzero
nonnegative real eigenvector is strictly positive at every vertex. -/
theorem nonnegative_eigenvector_strictly_positive {V : Type*} [Fintype V] [DecidableEq V]
    (A : Matrix V V ℝ) (hA : ∀ i j,i≠j → A i j≤0)
    (G : SimpleGraph V) (hG : G.Preconnected) (hedge : ∀ i j,G.Adj i j → A i j<0)
    (v : V → ℝ) (hv : ∀ i,0≤v i) (hvn : v≠0)
    (mu : ℝ) (heig : A.mulVec v=mu • v) : ∀ i,0<v i := by
  have propagate {i j : V} (h : G.Reachable i j) : v i=0 → v j=0 := by
    have hr := (G.reachable_iff_reflTransGen i j).mp h
    clear h
    induction hr with
    | refl => exact id
    | @tail b c hbc hcd ih =>
      intro hi
      exact nonnegative_eigenvector_zero_neighbor A hA v hv mu heig b c (ih hi) (hedge b c hcd)
  intro i
  by_contra hn
  have hi : v i=0 := le_antisymm (le_of_not_gt hn) (hv i)
  apply hvn
  funext j
  exact propagate (hG i j) hi


/-- A positive eigenvector on a connected strict-negative-entry graph
spans the whole real eigenspace at its eigenvalue. -/
theorem positive_eigenvector_eigenspace_simple {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (A : Matrix V V ℝ) (hA : ∀ i j,i≠j → A i j≤0)
    (G : SimpleGraph V) (hG : G.Preconnected) (hedge : ∀ i j,G.Adj i j → A i j<0)
    (v : V → ℝ) (hv : ∀ i,0<v i) (mu : ℝ) (hveig : A.mulVec v=mu • v)
    (w : V → ℝ) (hweig : A.mulVec w=mu • w) : ∃ c : ℝ,w=c • v := by
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ (fun j => w j/v j) Finset.univ_nonempty
  let c : ℝ := w i/v i
  let u : V → ℝ := c • v-w
  have hu (j : V) : 0≤u j := by
    have hh := hmax j (Finset.mem_univ j)
    have hw : w j≤c*v j := (div_le_iff₀ (hv j)).mp hh
    exact sub_nonneg.mpr hw
  have hui : u i=0 := by
    change (w i/v i)*v i-w i=0
    rw [div_mul_cancel₀ _ (hv i).ne',sub_self]
  have hueig : A.mulVec u=mu • u := by
    dsimp [u]
    rw [Matrix.mulVec_sub,Matrix.mulVec_smul,hveig,hweig]
    ext j
    simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  have hu0 : u=0 := by
    by_contra hne
    have hp := nonnegative_eigenvector_strictly_positive A hA G hG hedge u hu hne mu hueig i
    rw [hui] at hp
    exact (lt_irrefl 0) hp
  refine ⟨c,?_⟩
  funext j
  have hz := congrFun hu0 j
  change c*v j-w j=0 at hz
  exact (sub_eq_zero.mp hz).symm

end
end SixVertex
