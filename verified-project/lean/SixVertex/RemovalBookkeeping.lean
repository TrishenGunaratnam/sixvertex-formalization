import SixVertex.RemovalHistories

namespace SixVertex

noncomputable def originalRemovals (Y : Finset ℂ) : List RemovalEvent → List ℂ := by
  classical
  exact fun h => h.flatMap (fun e => match e with
    | .insert _ => []
    | .upper _ p | .lower _ p => if p ∈ Y then [p] else [])

theorem originalRemovals_supported (Y U : Finset ℂ) (h : List RemovalEvent)
    (hh : RemovalHistory.Valid Y U h) : ∀ p ∈ originalRemovals Y h, p ∈ Y ∧ p ∈ U := by
  classical
  induction h generalizing U with
  | nil => simp [originalRemovals]
  | cons e h ih =>
    have ht := ih (e.next U) hh.2
    cases e with
    | insert v =>
      simp only [originalRemovals,List.flatMap_cons,List.nil_append]
      intro p hp
      have hm := ht p hp
      refine ⟨hm.1,?_⟩
      have hn : p ≠ v := by intro he; subst p; exact hh.1.1 hm.1
      exact (Finset.mem_insert.mp hm.2).resolve_left hn
    | upper v q =>
      by_cases hq : q ∈ Y
      · simp only [originalRemovals,List.flatMap_cons,hq,ite_true,List.singleton_append,List.mem_cons]
        intro p hp
        rcases hp with rfl | hp
        · exact ⟨hq,hh.1⟩
        · exact ⟨(ht p hp).1,Finset.mem_of_mem_erase (ht p hp).2⟩
      · simp only [originalRemovals,List.flatMap_cons,hq,ite_false,List.nil_append]
        intro p hp
        exact ⟨(ht p hp).1,Finset.mem_of_mem_erase (ht p hp).2⟩
    | lower v q =>
      by_cases hq : q ∈ Y
      · simp only [originalRemovals,List.flatMap_cons,hq,ite_true,List.singleton_append,List.mem_cons]
        intro p hp
        rcases hp with rfl | hp
        · exact ⟨hq,hh.1⟩
        · exact ⟨(ht p hp).1,Finset.mem_of_mem_erase (ht p hp).2⟩
      · simp only [originalRemovals,List.flatMap_cons,hq,ite_false,List.nil_append]
        intro p hp
        exact ⟨(ht p hp).1,Finset.mem_of_mem_erase (ht p hp).2⟩

/-- Original roots can be removed at most once, because inserted row
arguments never belong to the original root set. -/
theorem originalRemovals_nodup (Y U : Finset ℂ) (h : List RemovalEvent)
    (hh : RemovalHistory.Valid Y U h) : (originalRemovals Y h).Nodup := by
  classical
  induction h generalizing U with
  | nil => simp [originalRemovals]
  | cons e h ih =>
    have ht := ih (e.next U) hh.2
    cases e with
    | insert v => simpa [originalRemovals] using ht
    | upper v p =>
      by_cases hp : p ∈ Y
      · simp only [originalRemovals,List.flatMap_cons,hp,ite_true,List.singleton_append,List.nodup_cons]
        exact ⟨fun hm => Finset.notMem_erase p U
          (originalRemovals_supported Y _ h hh.2 p hm).2,ht⟩
      · simpa [originalRemovals,hp] using ht
    | lower v p =>
      by_cases hp : p ∈ Y
      · simp only [originalRemovals,List.flatMap_cons,hp,ite_true,List.singleton_append,List.nodup_cons]
        exact ⟨fun hm => Finset.notMem_erase p U
          (originalRemovals_supported Y _ h hh.2 p hm).2,ht⟩
      · simpa [originalRemovals,hp] using ht

theorem missing_insert_new (Y U : Finset ℂ) (v : ℂ) (hv : v ∉ Y) :
    Y \ insert v U = Y \ U := by
  classical
  ext x
  by_cases hx : x = v
  · subst x; simp [hv]
  · simp [Finset.mem_sdiff,hx]

theorem missing_erase_original (Y U : Finset ℂ) (p : ℂ) (hp : p ∈ Y) :
    Y \ U.erase p = insert p (Y \ U) := by
  classical
  ext x
  by_cases hx : x = p
  · subst x; simp [hp]
  · simp [Finset.mem_sdiff,hx]

theorem missing_erase_added (Y U : Finset ℂ) (p : ℂ) (hp : p ∉ Y) :
    Y \ U.erase p = Y \ U := by
  classical
  ext x
  by_cases hx : x = p
  · subst x; simp [hp]
  · simp [Finset.mem_sdiff,hx]

/-- At every prefix, the missing originals are exactly those previously
removed. This determines which reciprocal pair factors can occur later. -/
theorem history_missing_endpoint (Y U : Finset ℂ) (h : List RemovalEvent)
    (hh : RemovalHistory.Valid Y U h) :
    Y \ historyEndpoint U h = (Y \ U) ∪ (originalRemovals Y h).toFinset := by
  classical
  induction h generalizing U with
  | nil => simp [historyEndpoint,originalRemovals]
  | cons e h ih =>
    rw [historyEndpoint,ih (e.next U) hh.2]
    cases e with
    | insert v => simp [RemovalEvent.next,missing_insert_new Y U v hh.1.1,originalRemovals]
    | upper v p =>
      by_cases hp : p ∈ Y
      · simp [RemovalEvent.next,missing_erase_original Y U p hp,originalRemovals,hp,
          Finset.union_insert,Finset.insert_union]
      · simp [RemovalEvent.next,missing_erase_added Y U p hp,originalRemovals,hp]
    | lower v p =>
      by_cases hp : p ∈ Y
      · simp [RemovalEvent.next,missing_erase_original Y U p hp,originalRemovals,hp,
          Finset.union_insert,Finset.insert_union]
      · simp [RemovalEvent.next,missing_erase_added Y U p hp,originalRemovals,hp]

noncomputable def RemovalEvent.oldPairCount (Y U : Finset ℂ) : RemovalEvent → ℕ := by
  classical
  exact fun e => match e with
    | .insert _ => 0
    | .upper _ p | .lower _ p => if p ∈ Y then (Y \ U).card else 0

noncomputable def historyPairCount (Y : Finset ℂ) : Finset ℂ → List RemovalEvent → ℕ
  | _, [] => 0
  | U, e::h => e.oldPairCount Y U + historyPairCount Y (e.next U) h

/-- Each newly removed original meets every previously removed original
once. The reciprocal-factor count is exactly the number of such pairs. -/
theorem history_pair_count (Y U : Finset ℂ) (h : List RemovalEvent)
    (hh : RemovalHistory.Valid Y U h) :
    historyPairCount Y U h + (Y \ U).card.choose 2 =
      (Y \ historyEndpoint U h).card.choose 2 := by
  classical
  induction h generalizing U with
  | nil => simp [historyPairCount,historyEndpoint]
  | cons e h ih =>
    have ht := ih (e.next U) hh.2
    cases e with
    | insert v =>
      simpa [historyPairCount,RemovalEvent.oldPairCount,historyEndpoint,RemovalEvent.next,
        missing_insert_new Y U v hh.1.1] using ht
    | upper v p =>
      by_cases hp : p ∈ Y
      · have hn : p ∉ Y \ U := fun hm => (Finset.mem_sdiff.mp hm).2 hh.1
        have hc : (Y \ U.erase p).card = (Y \ U).card+1 := by
          rw [missing_erase_original Y U p hp,Finset.card_insert_of_notMem hn]
        simp only [RemovalEvent.next,hc,Nat.choose_succ_succ',Nat.choose_one_right,Nat.reduceAdd] at ht
        simp only [historyPairCount,RemovalEvent.oldPairCount,hp,ite_true,historyEndpoint,RemovalEvent.next]
        omega
      · simpa [historyPairCount,RemovalEvent.oldPairCount,hp,historyEndpoint,RemovalEvent.next,
          missing_erase_added Y U p hp] using ht
    | lower v p =>
      by_cases hp : p ∈ Y
      · have hn : p ∉ Y \ U := fun hm => (Finset.mem_sdiff.mp hm).2 hh.1
        have hc : (Y \ U.erase p).card = (Y \ U).card+1 := by
          rw [missing_erase_original Y U p hp,Finset.card_insert_of_notMem hn]
        simp only [RemovalEvent.next,hc,Nat.choose_succ_succ',Nat.choose_one_right,Nat.reduceAdd] at ht
        simp only [historyPairCount,RemovalEvent.oldPairCount,hp,ite_true,historyEndpoint,RemovalEvent.next]
        omega
      · simpa [historyPairCount,RemovalEvent.oldPairCount,hp,historyEndpoint,RemovalEvent.next,
          missing_erase_added Y U p hp] using ht

/-- Original-root labels paired with their explicit row-argument beta factor. -/
noncomputable def originalBetaFactors (t : ℂ) (Y : Finset ℂ) : List RemovalEvent → List (ℂ × ℂ) := by
  classical
  exact fun h => h.flatMap (fun e => match e with
    | .insert _ => []
    | .upper v p => if p ∈ Y then [(p,betheBeta t (v-p))] else []
    | .lower v p => if p ∈ Y then [(p,betheBeta t (p-v))] else [])

theorem originalBetaFactors_roots (t : ℂ) (Y : Finset ℂ) (h : List RemovalEvent) :
    (originalBetaFactors t Y h).map Prod.fst = originalRemovals Y h := by
  classical
  induction h with
  | nil => rfl
  | cons e h ih =>
    simp only [originalBetaFactors,originalRemovals] at ih
    cases e with
    | insert v => simpa [originalBetaFactors,originalRemovals] using ih
    | upper v p => by_cases hp : p ∈ Y <;> simp [originalBetaFactors,originalRemovals,hp,ih]
    | lower v p => by_cases hp : p ∈ Y <;> simp [originalBetaFactors,originalRemovals,hp,ih]

theorem originalBetaFactors_product (t : ℂ) (Y U : Finset ℂ) (h : List RemovalEvent) :
    ((originalBetaFactors t Y h).map Prod.snd).prod = historyProduct (fun _ e => e.beta t Y) U h := by
  classical
  induction h generalizing U with
  | nil => simp [originalBetaFactors,historyProduct]
  | cons e h ih =>
    simp only [originalBetaFactors,RemovalEvent.beta] at ih
    cases e with
    | insert v => simpa [originalBetaFactors,historyProduct,RemovalEvent.beta,RemovalEvent.next] using ih (insert v U)
    | upper v p =>
      by_cases hp : p ∈ Y <;> simp [originalBetaFactors,historyProduct,RemovalEvent.beta,RemovalEvent.next,hp,ih (U.erase p)]
    | lower v p =>
      by_cases hp : p ∈ Y <;> simp [originalBetaFactors,historyProduct,RemovalEvent.beta,RemovalEvent.next,hp,ih (U.erase p)]

theorem originalBetaFactors_explicit (t : ℂ) (Y : Finset ℂ) (h : List RemovalEvent)
    (z : ℂ × ℂ) (hz : z ∈ originalBetaFactors t Y h) :
    ∃ v : ℂ, z.2 = betheBeta t (v-z.1) ∨ z.2 = betheBeta t (z.1-v) := by
  classical
  obtain ⟨e,he,hz⟩ := List.mem_flatMap.mp hz
  cases e with
  | insert v => simp at hz
  | upper v p =>
    by_cases hp : p ∈ Y
    · simp only [hp,ite_true,List.mem_singleton] at hz
      subst z
      exact ⟨v,Or.inl rfl⟩
    · simp [hp] at hz
  | lower v p =>
    by_cases hp : p ∈ Y
    · simp only [hp,ite_true,List.mem_singleton] at hz
      subst z
      exact ⟨v,Or.inr rfl⟩
    · simp [hp] at hz

end SixVertex
