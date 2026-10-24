import SixVertex.SpinAdjacentCoordinates
import Mathlib.Order.Fin.Tuple

namespace SixVertex
noncomputable section

/-- Appending a value larger than every earlier value preserves strict order. -/
theorem strictMono_snoc_of_lt {m : ℕ} {A : Type*} [LinearOrder A]
    (f : Fin m → A) (hf : StrictMono f) (b : A) (hb : ∀ i,f i<b) :
    StrictMono (@Fin.snoc m (fun _ => A) f b) := by
  intro i j hij
  by_cases hj : j=Fin.last m
  · subst j
    have hi : i.val<m := hij
    let ii : Fin m := ⟨i.val,hi⟩
    rw [show i=ii.castSucc by apply Fin.ext;rfl,Fin.snoc_castSucc,Fin.snoc_last]
    exact hb ii
  · have hjm : j.val<m := by
      have hjval : j.val≠m := by intro h;exact hj (Fin.ext h)
      omega
    have him : i.val<m := by have hval : i.val<j.val := hij;omega
    let ii : Fin m := ⟨i.val,him⟩
    let jj : Fin m := ⟨j.val,hjm⟩
    rw [show i=ii.castSucc by apply Fin.ext;rfl,
      show j=jj.castSucc by apply Fin.ext;rfl,Fin.snoc_castSucc,Fin.snoc_castSucc]
    exact hf (show ii<jj from hij)

/-- A left hop from site zero to the empty final site removes the first
occupied coordinate and appends the final site to the ordered list. -/
theorem occupiedIndex_wrap_left (length m : ℕ)
    (q : ParticleConfigurations (length+1) (m+1))
    (ha : occupiedIndex q 0=0)
    (hb : rowSpinAt (length+1) q.val (Fin.last length)=0) :
    (fun i => occupiedIndex (swapSpinSites q 0 (Fin.last length)) i)=
      @Fin.snoc m (fun _ => Fin (length+1)) (fun j => occupiedIndex q j.succ) (Fin.last length) := by
  let r := swapSpinSites q 0 (Fin.last length)
  let g := @Fin.snoc m (fun _ => Fin (length+1)) (fun j => occupiedIndex q j.succ) (Fin.last length)
  have hm : StrictMono g := by
    apply strictMono_snoc_of_lt
    · intro i j hij
      apply (occupiedIndex q).strictMono
      simpa using hij
    · intro i
      exact Fin.lt_last_iff_ne_last.mpr (occupiedIndex_ne_hole q (Fin.last length) hb i.succ)
  have hmem (i : Fin (m+1)) : g i ∈ occupiedSites (length+1) r.val := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · dsimp only [g,r]
      rw [Fin.snoc_last,rowSpinAt_swapSpinSites,Equiv.swap_apply_right,← ha]
      exact occupiedIndex_occupied q 0
    · dsimp only [g,r]
      rw [Fin.snoc_castSucc]
      have h0 : occupiedIndex q j.succ≠0 := by
        rw [← ha]
        exact fun h => (Fin.succ_ne_zero j) ((occupiedIndex q).injective h)
      rw [rowSpinAt_swapSpinSites,Equiv.swap_apply_of_ne_of_ne h0
        (occupiedIndex_ne_hole q (Fin.last length) hb j.succ)]
      exact occupiedIndex_occupied q j.succ
  exact (Finset.orderEmbOfFin_unique ((occupiedSites_card (length+1) r.val).trans r.property) hmem hm).symm

/-- The exact integer coordinate map for that physical boundary exchange. -/
theorem occupiedCoordinates_wrap_left (length m : ℕ)
    (q : ParticleConfigurations (length+1) (m+1))
    (ha : occupiedIndex q 0=0)
    (hb : rowSpinAt (length+1) q.val (Fin.last length)=0) :
    occupiedCoordinates (swapSpinSites q 0 (Fin.last length))=
      @Fin.snoc m (fun _ => ℤ) (fun j => occupiedCoordinates q j.succ) (length : ℤ) := by
  funext i
  rw [occupiedCoordinates_eq_index]
  rw [congrFun (occupiedIndex_wrap_left length m q ha hb) i]
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simp only [Fin.snoc_castSucc,occupiedCoordinates_eq_index]

end
end SixVertex
