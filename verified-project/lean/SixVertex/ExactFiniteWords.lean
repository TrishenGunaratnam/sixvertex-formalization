import SixVertex.EndpointDeterminants
import SixVertex.HistoryRealization

namespace SixVertex

/-- Precisely the generic finite domain used by the displayed path quotient.
No limiting or thermodynamic assertion is contained in this domain. -/
structure FiniteWordDomain {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (k : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (S : Finset ℂ)
    (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ)) : Prop where
  roots : rootSet Y ⊆ S
  endpoints : EndpointGeneric lam b (2*k) Y hY S
  arguments : ∀ ev ∈ w, ev.2 ∈ S
  regular : BetheRegular (Complex.I*lam) S
  vacuum : ∀ p ∈ S, vacuumA (Complex.I*lam) (fun j => (b j : ℂ)) p (2*k) ≠ 0
  fresh : MarkedWordRegular (Complex.I*lam) (rootSet Y) w
  generic : ∀ ev ∈ w, ev.2 ∉ rootSet Y ∧ ∀ y ∈ rootSet Y, Complex.sinh (ev.2-y) ≠ 0
  normalization : (w.map (fun ev => 1+setBetheQ (Complex.I*lam)
    (fun j => (b j : ℂ)) (2*k) (rootSet Y) ev.2)).prod ≠ 0

/-- The path certificate retains the actual ordered removals and their
row arguments. The mixed factor contains no interaction of two originals. -/
structure PathHistoryCertificate (t : ℂ) (b : ℕ → ℂ) (L n : ℕ) (Y : Finset ℂ)
    (z : ℂ × Finset ℂ) (h : List RemovalEvent) : Prop where
  valid : RemovalHistory.Valid Y Y h
  endpoint : historyEndpoint Y h = z.2
  weight : z.1 = historyProduct (fun V e => e.relativeParity n V) Y h *
    historyProduct (fun _ e => e.beta t Y) Y h *
    historyProduct (fun V e => e.oldPairs t Y V) Y h *
    historyProduct (fun V e => e.mixed t b L Y V) Y h
  original_once : (originalRemovals Y h).Nodup
  missing : (originalRemovals Y h).toFinset = Y \ z.2
  pair_count : historyPairCount Y Y h = (Y \ z.2).card.choose 2
  beta_roots : (originalBetaFactors t Y h).map Prod.fst = originalRemovals Y h
  beta_product : ((originalBetaFactors t Y h).map Prod.snd).prod =
    historyProduct (fun _ e => e.beta t Y) Y h
  beta_explicit : ∀ q ∈ originalBetaFactors t Y h,
    ∃ v, q.2 = betheBeta t (v-q.1) ∨ q.2 = betheBeta t (q.1-v)

theorem relativeCorrection_path_certificate {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (S : Finset ℂ) (hY : rootSet Y ⊆ S)
    (w : List (RowEntry × ℂ)) (hw : ∀ ev ∈ w, ev.2 ∈ S ∧ ev.2 ∉ rootSet Y)
    (hreg : BetheRegular (Complex.I*lam) S) (hfresh : WordRegular (Complex.I*lam) (rootSet Y) w)
    (z : ℂ × Finset ℂ) (hz : z ∈ relativeCorrectionWords lam b L Y w (rootSet Y)) :
    ∃ h, PathHistoryCertificate (Complex.I*lam) (fun j => (b j : ℂ)) L n (rootSet Y) z h := by
  obtain ⟨h,hh,he,hwgt⟩ := relativeCorrection_history_exists lam b L Y S (rootSet Y) hY hY w hw hreg hfresh z hz
  refine ⟨h,hh,he,?_,originalRemovals_nodup _ _ h hh,?_,?_,
    originalBetaFactors_roots _ _ h,originalBetaFactors_product _ _ _ h,originalBetaFactors_explicit _ _ h⟩
  · rw [hwgt,history_gamma_factorization _ _ _ _ _ h hh]
    ring
  · have hm := history_missing_endpoint (rootSet Y) (rootSet Y) h hh
    simpa [he] using hm.symm
  · have hc := history_pair_count (rootSet Y) (rootSet Y) h hh
    simpa [he] using hc

theorem unit_entry_word_selection {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (k : ℕ)
    (Y : Fin n → ℝ) (w : List (RowEntry × ℂ))
    (h : (w.map (fun ev => entryCharge ev.1)).sum ≠ 0) :
    inner ℂ (physicalUnitBetheVector lam b (2*k) Y)
      (hilbertMatrixAction (2*k) (normalizedPhysicalWord lam b (2*k) Y w)
        (physicalUnitBetheVector lam b (2*k) Y)) = 0 := by
  simp only [physicalUnitBetheVector,normalizeSpinVector,hilbertMatrixAction_smul,
    inner_smul_left,inner_smul_right,
    normalizedPhysicalWord_expectation_zero lam b k Y w h,mul_zero]

theorem finite_word_deleted_slots_bound {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (L : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) (w : List (RowEntry × ℂ))
    (z : ℂ × Finset ℂ) (hz : z ∈ relativeCorrectionWords lam b L Y w (rootSet Y))
    (hcard : z.2.card = n) :
    (deletedSlots Y z.2).card = (z.2 \ rootSet Y).card ∧ (deletedSlots Y z.2).card ≤ w.length := by
  have hs := relativeCorrection_path_cardinality lam b L Y w z hz (by rw [rootSet_card Y hY,hcard])
  rw [replacement_cardinality Y hY z.2 hcard]
  exact ⟨rfl,hs.2⟩

/-- All clauses of Corollary 2.6, including the full determinant expectation,
spin selection, replacement slots, bounded minors, diagonal parity, reciprocal
original-root pairs and their explicit beta factors. -/
structure ExactFiniteWordExpansion {n : ℕ} (lam : ℝ) (b : ℕ → ℝ) (k : ℕ)
    (Y : Fin n → ℝ) (hY : Function.Injective Y) : Prop where
  marked_sum : ∀ (S : Finset ℂ) (w : List (Matrix (Fin 2) (Fin 2) ℂ × ℂ)),
    FiniteWordDomain lam b k Y hY S w →
    inner ℂ (physicalUnitBetheVector lam b (2*k) Y)
      (hilbertMatrixAction (2*k) (normalizedMarkedWord lam b (2*k) Y w)
        (physicalUnitBetheVector lam b (2*k) Y)) =
      ((markedWordChoices w).map (fun z => z.1 *
        weightedEval (endpointDeterminantAmplitude lam b (2*k) Y hY z.2)
          (relativeCorrectionWords lam b (2*k) Y z.2 (rootSet Y)))).sum
  selection : ∀ w : List (RowEntry × ℂ), (w.map (fun ev => entryCharge ev.1)).sum ≠ 0 →
    inner ℂ (physicalUnitBetheVector lam b (2*k) Y)
      (hilbertMatrixAction (2*k) (normalizedPhysicalWord lam b (2*k) Y w)
        (physicalUnitBetheVector lam b (2*k) Y)) = 0
  replacement : ∀ T : Finset ℂ, T.card = n → ∃ V : Fin n → ℂ,
    Function.Injective V ∧ (∀ j, j ∉ deletedSlots Y T → V j = (Y j : ℂ)) ∧
      (∀ j, j ∈ deletedSlots Y T → V j ∈ T \ rootSet Y) ∧ Finset.univ.image V = T
  bounded_minor : ∀ (w : List (RowEntry × ℂ)) (z : ℂ × Finset ℂ),
    z ∈ relativeCorrectionWords lam b (2*k) Y w (rootSet Y) → z.2.card = n →
    (deletedSlots Y z.2).card = (z.2 \ rootSet Y).card ∧ (deletedSlots Y z.2).card ≤ w.length
  diagonal_parity : ∀ (w : List (RowEntry × ℂ)) (U : Finset ℂ), U.card = n →
    WordRegular (Complex.I*lam) U w → (∀ ev ∈ w, ev.1 = .A ∨ ev.1 = .L) →
    relativeCorrectionWords lam b (2*k) Y w U =
      correctionWordTerms (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) (rootSet Y) w U
  parity_exponent : ∀ a : ℕ, (-1 : ℂ)^a/(-1 : ℂ)^n = (-1 : ℂ)^((a : ℤ)-(n : ℤ))
  histories : ∀ (S : Finset ℂ), rootSet Y ⊆ S → ∀ (w : List (RowEntry × ℂ)),
    (∀ ev ∈ w, ev.2 ∈ S ∧ ev.2 ∉ rootSet Y) → BetheRegular (Complex.I*lam) S →
    WordRegular (Complex.I*lam) (rootSet Y) w → ∀ (z : ℂ × Finset ℂ),
    z ∈ relativeCorrectionWords lam b (2*k) Y w (rootSet Y) →
    ∃ h, PathHistoryCertificate (Complex.I*lam) (fun j => (b j : ℂ)) (2*k) n (rootSet Y) z h

/-- Corollary 2.6, relative only to the authorized Slavnov identity.
Every genericity hypothesis is an explicit finite nonzero-denominator condition. -/
theorem exact_finite_word_expansion {n : ℕ} (lam : ℝ) (h0 : 0 < lam) (hpi : lam < Real.pi)
    (b : ℕ → ℝ) (k : ℕ) (Y : Fin n → ℝ) (hY : Function.Injective Y)
    (hShell : OnShell lam b (2*k) Y 0) (hSlavnov : SlavnovIdentity lam b (2*k) Y 0)
    (hdet : (gaudinMatrix lam b (2*k) Y).det ≠ 0)
    (hpos : ∀ j, 0 < countingSlope lam b (2*k) Y (Y j)) :
    ExactFiniteWordExpansion lam b k Y hY := by
  refine ⟨?_,unit_entry_word_selection lam b k Y,replacement_slots_exist Y hY,
    finite_word_deleted_slots_bound lam b (2*k) Y hY,diagonal_relative_corrections lam b (2*k) Y,
    fun a => relativeParity_eq_zpow a n,relativeCorrection_path_certificate lam b (2*k) Y⟩
  intro S w hd
  exact exact_marked_word_determinant_sum lam h0 hpi b k Y hY hShell hSlavnov hdet hpos S hd.roots hd.endpoints
    w hd.arguments hd.regular hd.vacuum hd.fresh hd.generic hd.normalization

end SixVertex
