import SixVertex.BetheWords

namespace SixVertex

open Filter Topology

/-- Lists retain the multiplicity of coincident spectral arguments. -/
noncomputable def betheListState (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (U : List ℂ) :
    Matrix (RowSpins n) (RowSpins n) ℂ :=
  (U.map (betheB t b n)).prod * vacuumProjector n

theorem betheListState_eq_finset (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : List ℂ) (hU : U.Nodup) :
    betheListState t b n U = betheState t ht b n U.toFinset := by
  rw [betheListState, betheState, creationProduct_list _ _ U hU]

theorem betheBlock_continuous (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (a c : Fin 2) :
    Continuous (fun x => betheBlock t b n x a c) := by
  apply continuous_matrix
  intro q r
  exact continuous_iff_continuousAt.mpr
    (fun z => (betheBlock_analytic t b n a c q r z).continuousAt)

theorem entryOperator_continuous (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (e : RowEntry) :
    Continuous (entryOperator t b n e) := by
  cases e <;> exact betheBlock_continuous t b n _ _

/-- Continuity of the full labelled product, allowing arbitrary collisions. -/
theorem betheListState_tendsto {J I : Type*} (r : Filter J)
    (t : ℂ) (b : ℕ → ℂ) (n : ℕ) (labels : List I)
    (u : J → I → ℂ) (u₀ : I → ℂ)
    (hu : ∀ i ∈ labels, Tendsto (fun ξ => u ξ i) r (𝓝 (u₀ i))) :
    Tendsto (fun ξ => betheListState t b n (labels.map (u ξ))) r
      (𝓝 (betheListState t b n (labels.map u₀))) := by
  induction labels with
  | nil => simpa [betheListState] using tendsto_const_nhds
  | cons i labels ih =>
    have hi := ((betheBlock_continuous t b n 0 1).tendsto (u₀ i)).comp
      (hu i (by simp))
    have htail := ih (fun j hj => hu j (List.mem_cons_of_mem _ hj))
    simpa only [betheListState, List.map_cons, List.prod_cons, mul_assoc, Function.comp_def, betheB] using hi.mul htail

/-- The COMPLETE displayed action sum has the correct limit at coincident
arguments. The limiting state is a labelled list, so repeated arguments
are retained. No limit of the individual summands is assumed. -/
theorem single_entry_coincident_limit {J I : Type*} (r : Filter J)
    (t : ℂ) (ht : Complex.sinh t ≠ 0) (b : ℕ → ℂ) (n : ℕ)
    (e : RowEntry) (labels : List I) (u : J → I → ℂ) (u₀ : I → ℂ)
    (v : J → ℂ) (v₀ : ℂ)
    (hu : ∀ i ∈ labels, Tendsto (fun ξ => u ξ i) r (𝓝 (u₀ i)))
    (hv : Tendsto v r (𝓝 v₀))
    (hgeneric : ∀ᶠ ξ in r, (labels.map (u ξ)).Nodup ∧
      v ξ ∉ (labels.map (u ξ)).toFinset ∧
      BetheRegular t (insert (v ξ) (labels.map (u ξ)).toFinset)) :
    Tendsto (fun ξ => weightedEval (betheState t ht b n)
      (entryTerms t b n e (v ξ) (labels.map (u ξ)).toFinset)) r
      (𝓝 (entryOperator t b n e v₀ * betheListState t b n (labels.map u₀))) := by
  have hactual := ((entryOperator_continuous t b n e).tendsto v₀ |>.comp hv).mul
    (betheListState_tendsto r t b n labels u u₀ hu)
  apply hactual.congr'
  filter_upwards [hgeneric] with ξ hξ
  rw [betheListState_eq_finset t ht b n _ hξ.1]
  exact entry_expansion t ht b n e (v ξ) _ hξ.2.1 hξ.2.2

end SixVertex
