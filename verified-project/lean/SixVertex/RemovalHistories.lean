import SixVertex.PathDeterminants

namespace SixVertex

/-- Adding one retained argument multiplies the upper quotient by its f factor. -/
theorem upperPathQuotient_insert (t : ℂ) (Y T S : Finset ℂ) (p q : ℂ)
    (hY : Y ⊆ S) (hT : T ⊆ S) (hp : p ∈ S) (hq : q ∈ S)
    (hpT : p ∉ T) (hqT : q ∉ T) (hpq : p ≠ q) (hreg : BetheRegular t S) :
    upperPathQuotient t Y (insert q T) p = betheF t (q-p)*upperPathQuotient t Y T p := by
  have hb := upper_path_quotient t Y T S p hY hT hp hpT hreg
  have hi := upper_path_quotient t Y (insert q T) S p hY (Finset.insert_subset hq hT) hp
    (by simp [hpq,hpT]) hreg
  have hn : (∏ y ∈ Y.erase p, betheF t (y-p)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun y hy => betheF_regular_ne hreg y (hY (Finset.mem_of_mem_erase hy))
      p hp (Finset.ne_of_mem_erase hy))
  rw [Finset.prod_insert hqT] at hi
  apply mul_left_cancel₀ hn
  calc
    _ = betheF t (q-p)*(∏ x ∈ T,betheF t (x-p)) := hi
    _ = betheF t (q-p)*((∏ y ∈ Y.erase p,betheF t (y-p))*upperPathQuotient t Y T p) := by rw [hb]
    _ = _ := by ring

/-- The ordered C correction equals an upper removal followed by a lower
removal at the same row argument. This includes its extra f factor exactly. -/
theorem doublePathCorrection_sequential (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y E S : Finset ℂ)
    (p q v : ℂ) (hY : Y ⊆ S) (hE : E ⊆ S) (hp : p ∈ E) (hq : q ∈ E.erase p)
    (hreg : BetheRegular t S) :
    doublePathCorrection t b L Y ((E.erase p).erase q) v p q =
      upperPathCorrection t Y (E.erase p) v p *
        lowerPathCorrection t b L Y ((E.erase p).erase q) v q := by
  have he : insert q ((E.erase p).erase q) = E.erase p := Finset.insert_erase hq
  have hi := upperPathQuotient_insert t Y ((E.erase p).erase q) S p q hY
    (((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)).trans hE)
    (hE hp) (hE (Finset.mem_of_mem_erase hq))
    (fun h => Finset.notMem_erase p E (Finset.mem_of_mem_erase h)) (Finset.notMem_erase _ _)
    (Finset.ne_of_mem_erase hq).symm hreg
  rw [he] at hi
  unfold doublePathCorrection upperPathCorrection lowerPathCorrection
  rw [hi]
  ring

inductive RemovalEvent where
  | insert (v : ℂ)
  | upper (v p : ℂ)
  | lower (v p : ℂ)

noncomputable def RemovalEvent.next (e : RemovalEvent) (U : Finset ℂ) : Finset ℂ := by
  classical
  exact match e with
  | .insert v => Insert.insert v U
  | .upper _ p | .lower _ p => U.erase p

def RemovalEvent.Valid (Y U : Finset ℂ) : RemovalEvent → Prop
  | .insert v => v ∉ Y ∧ v ∉ U
  | .upper _ p | .lower _ p => p ∈ U

noncomputable def RemovalEvent.gamma (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y U : Finset ℂ) : RemovalEvent → ℂ
  | .insert _ => 1
  | .upper v p => upperPathCorrection t Y (U.erase p) v p
  | .lower v p => lowerPathCorrection t b L Y (U.erase p) v p

noncomputable def RemovalEvent.beta (t : ℂ) (Y : Finset ℂ) : RemovalEvent → ℂ := by
  classical
  exact fun e => match e with
  | .insert _ => 1
  | .upper v p => if p ∈ Y then betheBeta t (v-p) else 1
  | .lower v p => if p ∈ Y then betheBeta t (p-v) else 1

noncomputable def RemovalEvent.oldPairs (t : ℂ) (Y U : Finset ℂ) : RemovalEvent → ℂ := by
  classical
  exact fun e => match e with
  | .insert _ => 1
  | .upper _ p => if p ∈ Y then ∏ r ∈ Y \ U, (betheF t (r-p))⁻¹ else 1
  | .lower _ p => if p ∈ Y then ∏ r ∈ Y \ U, (betheF t (p-r))⁻¹ else 1

/-- Remaining factors involve an added argument; no pair of original roots
occurs here. For an original removal only the added-root numerator remains. -/
noncomputable def RemovalEvent.mixed (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y U : Finset ℂ) : RemovalEvent → ℂ := by
  classical
  exact fun e => match e with
  | .insert _ => 1
  | .upper v p => if p ∈ Y then ∏ u ∈ U.erase p \ Y, betheF t (u-p)
      else upperPathCorrection t Y (U.erase p) v p
  | .lower v p => if p ∈ Y then ∏ u ∈ U.erase p \ Y, betheF t (p-u)
      else lowerPathCorrection t b L Y (U.erase p) v p

theorem RemovalEvent.gamma_factorization (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y U : Finset ℂ)
    (e : RemovalEvent) (he : e.Valid Y U) :
    e.gamma t b L Y U = e.beta t Y * e.oldPairs t Y U * e.mixed t b L Y U := by
  classical
  cases e with
  | insert v => simp [gamma,beta,oldPairs,mixed]
  | upper v p =>
    have hE : Insert.insert p (U.erase p) = U := Finset.insert_erase he
    by_cases hp : p ∈ Y
    · simp only [gamma,beta,oldPairs,mixed,hp,ite_true,upperPathCorrection,upperPathQuotient,hE,
        Finset.prod_inv_distrib,div_eq_mul_inv]
      ring
    · simp [gamma,beta,oldPairs,mixed,hp]
  | lower v p =>
    have hE : Insert.insert p (U.erase p) = U := Finset.insert_erase he
    by_cases hp : p ∈ Y
    · simp only [gamma,beta,oldPairs,mixed,hp,ite_true,lowerPathCorrection,lowerPathQuotient,hE,
        pathChi,Finset.prod_inv_distrib,div_eq_mul_inv]
      ring
    · simp [gamma,beta,oldPairs,mixed,hp]

def RemovalHistory.Valid (Y : Finset ℂ) : Finset ℂ → List RemovalEvent → Prop
  | _, [] => True
  | U, e::h => e.Valid Y U ∧ RemovalHistory.Valid Y (e.next U) h

noncomputable def historyProduct (f : Finset ℂ → RemovalEvent → ℂ) :
    Finset ℂ → List RemovalEvent → ℂ
  | _, [] => 1
  | U, e::h => f U e * historyProduct f (e.next U) h

noncomputable def historyEndpoint : Finset ℂ → List RemovalEvent → Finset ℂ
  | U, [] => U
  | U, e::h => historyEndpoint (e.next U) h

/-- Across the whole history, each original removal supplies its beta and
all interactions between original roots remain reciprocal f factors. -/
theorem history_gamma_factorization (t : ℂ) (b : ℕ → ℂ) (L : ℕ) (Y U : Finset ℂ)
    (h : List RemovalEvent) (hh : RemovalHistory.Valid Y U h) :
    historyProduct (fun V e => e.gamma t b L Y V) U h =
      historyProduct (fun _ e => e.beta t Y) U h *
      historyProduct (fun V e => e.oldPairs t Y V) U h *
      historyProduct (fun V e => e.mixed t b L Y V) U h := by
  induction h generalizing U with
  | nil => simp [historyProduct]
  | cons e h ih =>
    simp only [historyProduct]
    rw [e.gamma_factorization t b L Y U hh.1, ih (e.next U) hh.2]
    ring

end SixVertex
