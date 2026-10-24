import SixVertex.BetheConvention
import SixVertex.BetheLimits

/-!
# Lemma 2.3: Single-entry actions (`lem:finite-actions`)

The four action formulas, explicit finite-word paths and cardinality
conclusion are assembled below. `t = I * lambda`; the exact identification
with the manuscript's standard monodromy is `betheBlock_eq_standard`.

The finite matrices representing Bethe vectors have only their vacuum
column nonzero. Thus equality here is precisely equality of the usual
spin-space vectors, with an injective rank-one matrix representation.

Generic arguments are distinct and avoid every displayed sinh denominator.
The coincident clause proves convergence of the COMPLETE sum along any
regular labelled family; its limiting list preserves multiplicities.
-/

namespace SixVertex

open Filter Topology

structure SingleEntryActions (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) : Prop where
  creation : ∀ (U : Finset ℂ) (v : ℂ), v ∉ U →
    betheB t b n v * betheState t ht b n U = betheState t ht b n (insert v U)
  upper : ∀ (U : Finset ℂ) (v : ℂ), v ∉ U → BetheRegular t (insert v U) →
    betheA t b n v * betheState t ht b n U =
      ∑ p ∈ insert v U,
        (vacuumA t b p n * betheBeta t (v-p) *
          ∏ u ∈ (insert v U).erase p, betheF t (u-p)) •
        betheState t ht b n ((insert v U).erase p)
  lower : ∀ (U : Finset ℂ) (v : ℂ), v ∉ U → BetheRegular t (insert v U) →
    betheL t b n v * betheState t ht b n U =
      ∑ p ∈ insert v U,
        (vacuumL t b p n * betheBeta t (p-v) *
          ∏ u ∈ (insert v U).erase p, betheF t (p-u)) •
        betheState t ht b n ((insert v U).erase p)
  annihilation : ∀ (U : Finset ℂ) (v : ℂ), v ∉ U → BetheRegular t (insert v U) →
    betheC t b n v * betheState t ht b n U =
      ∑ p ∈ insert v U, ∑ q ∈ (insert v U).erase p,
        cActionWeight t b n (insert v U) v p q •
          betheState t ht b n (((insert v U).erase p).erase q)
  words : ∀ (w : List (RowEntry × ℂ)) (U : Finset ℂ), WordRegular t U w →
    wordOperator t b n w * betheState t ht b n U =
      weightedEval (betheState t ht b n) (wordTerms t b n w U)
  step_support : ∀ (e : RowEntry) (v : ℂ) (U : Finset ℂ) (z : ℂ × Finset ℂ),
    z ∈ entryTerms t b n e v U → z.2 ⊆ insert v U ∧ ((insert v U) \ z.2).card ≤ 2
  endpoint_cardinality : ∀ (w : List (RowEntry × ℂ)) (U : Finset ℂ) (z : ℂ × Finset ℂ),
    z ∈ wordTerms t b n w U → z.2.card = U.card →
      (U \ z.2).card = (z.2 \ U).card ∧ (z.2 \ U).card ≤ w.length
  coincident : ∀ (J I : Type) (r : Filter J) (e : RowEntry) (labels : List I)
    (u : J → I → ℂ) (u₀ : I → ℂ) (v : J → ℂ) (v₀ : ℂ),
    (∀ i ∈ labels, Tendsto (fun ξ => u ξ i) r (𝓝 (u₀ i))) →
    Tendsto v r (𝓝 v₀) →
    (∀ᶠ ξ in r, (labels.map (u ξ)).Nodup ∧
      v ξ ∉ (labels.map (u ξ)).toFinset ∧
      BetheRegular t (insert (v ξ) (labels.map (u ξ)).toFinset)) →
    Tendsto (fun ξ => weightedEval (betheState t ht b n)
      (entryTerms t b n e (v ξ) (labels.map (u ξ)).toFinset)) r
      (𝓝 (entryOperator t b n e v₀ * betheListState t b n (labels.map u₀)))

/-- The complete generic statement, strengthened to every finite chain
length and arbitrary complex inhomogeneities. -/
theorem single_entry_actions_complex (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) : SingleEntryActions t ht b n := by
  refine ⟨bethe_B_action t ht b n, bethe_A_action t ht b n,
    bethe_L_action t ht b n, bethe_C_action t ht b n,
    word_expansion t ht b n, ?_, word_path_cardinality t b n, ?_⟩
  · intro e v U z hz
    exact ⟨entryTerms_support t b n e v U z hz, entryTerms_remove_bound t b n e v U z hz⟩
  · intro J I r e labels u u₀ v v₀ hu hv hgeneric
    exact single_entry_coincident_limit r t ht b n e labels u u₀ v v₀ hu hv hgeneric

/-- Section 2, Lemma 2.3, in the paper's real-parameter conventions. -/
theorem single_entry_actions (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (n : ℕ) :
    SingleEntryActions (Complex.I * (lam : ℂ)) (physical_deformation_ne_zero lam h0 hpi)
      (fun j => (b j : ℂ)) n :=
  single_entry_actions_complex _ _ _ _

/-- The usual vector obtained from the vacuum column of its rank-one matrix. -/
noncomputable def betheVector (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) : RowSpins n → ℂ :=
  fun q => betheState t ht b n U q (plusSpins n)

theorem betheState_column (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (U : Finset ℂ) (q r : RowSpins n) :
    betheState t ht b n U q r = if r = plusSpins n then betheVector t ht b n U q else 0 := by
  simp [betheVector, betheState, mul_vacuumProjector]

/-- The assembled action identity in the ordinary spin-vector representation. -/
theorem single_entry_vector (t : ℂ) (ht : Complex.sinh t ≠ 0)
    (b : ℕ → ℂ) (n : ℕ) (e : RowEntry) (U : Finset ℂ) (v : ℂ)
    (hv : v ∉ U) (hreg : BetheRegular t (insert v U)) :
    (entryOperator t b n e v).mulVec (betheVector t ht b n U) =
      weightedEval (betheVector t ht b n) (entryTerms t b n e v U) := by
  have h := entry_expansion t ht b n e v U hv hreg
  have hc : ∀ T : List (ℂ × Finset ℂ), ∀ q : RowSpins n,
      weightedEval (betheState t ht b n) T q (plusSpins n) =
        weightedEval (betheVector t ht b n) T q := by
    intro T q
    induction T with
    | nil => rfl
    | cons z T ih =>
      simp only [weightedEval, List.map_cons, List.sum_cons, Matrix.add_apply,
        Matrix.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at ih ⊢
      rw [ih]
      rfl
  ext q
  change (entryOperator t b n e v * betheState t ht b n U) q (plusSpins n) = _
  rw [h, hc]

end SixVertex
