import SixVertex.BetheCharge
import Mathlib.Logic.Relation

namespace SixVertex

/-- A physical nearest-neighbor hop exchanges opposite spins at one
adjacent pair; arbitrary earlier spins are retained. -/
inductive AdjacentSpinSwap : (L : ℕ) → RowSpins L → RowSpins L → Prop
  | head (L : ℕ) (a b : Fin 2) (t : RowSpins L) (h : a≠b) :
      AdjacentSpinSwap (L+2) (a,b,t) (b,a,t)
  | tail (L : ℕ) (a : Fin 2) {q r : RowSpins L} (h : AdjacentSpinSwap L q r) :
      AdjacentSpinSwap (L+1) (a,q) (a,r)

def SpinSwapReach (L : ℕ) : RowSpins L → RowSpins L → Prop :=
  Relation.ReflTransGen (AdjacentSpinSwap L)

theorem adjacentSpinSwap_symm {L : ℕ} {q r : RowSpins L}
    (h : AdjacentSpinSwap L q r) : AdjacentSpinSwap L r q := by
  induction h with
  | head L a b t h => exact .head L b a t h.symm
  | tail L a h ih => exact .tail L a ih

theorem adjacentSpinSwap_minusCount {L : ℕ} {q r : RowSpins L}
    (h : AdjacentSpinSwap L q r) : minusCount L q=minusCount L r := by
  induction h with
  | head L a b t h => simp only [minusCount]; omega
  | tail L a h ih => simp only [minusCount]; omega

theorem spinSwapReach_symm {L : ℕ} {q r : RowSpins L}
    (h : SpinSwapReach L q r) : SpinSwapReach L r q := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact (Relation.ReflTransGen.single (adjacentSpinSwap_symm h₂)).trans ih

theorem spinSwapReach_minusCount {L : ℕ} {q r : RowSpins L}
    (h : SpinSwapReach L q r) : minusCount L q=minusCount L r := by
  induction h with
  | refl => rfl
  | tail h₁ h₂ ih => exact ih.trans (adjacentSpinSwap_minusCount h₂)

/-- A path in a tail remains a physical path when a leading spin is fixed. -/
theorem spinSwapReach_prepend {L : ℕ} (a : Fin 2) {q r : RowSpins L}
    (h : SpinSwapReach L q r) : SpinSwapReach (L+1) (a,q) (a,r) := by
  induction h with
  | refl => exact .refl
  | tail h₁ h₂ ih => exact ih.tail (.tail L a h₂)

/-- Any occupied spin can be moved to the first site by actual adjacent
particle-hole exchanges. -/
theorem exists_spinSwapReach_one_front (n : ℕ) (q : RowSpins (n+1))
    (hq : 0<minusCount (n+1) q) :
    ∃ r : RowSpins n,SpinSwapReach (n+1) q (1,r) := by
  induction n with
  | zero =>
    rcases q with ⟨a,t⟩
    cases t
    fin_cases a
    · simp [minusCount] at hq
    · exact ⟨(),.refl⟩
  | succ n ih =>
    rcases q with ⟨a,t⟩
    fin_cases a
    · have ht : 0<minusCount (n+1) t := by simpa only [minusCount,Fin.val_zero,zero_add] using hq
      obtain ⟨r,hr⟩ := ih t ht
      refine ⟨(0,r),?_⟩
      exact (spinSwapReach_prepend 0 hr).tail (.head n 0 1 r (by decide))
    · exact ⟨t,.refl⟩

/-- Every two basis configurations in the same particle sector are
connected by physical nearest-neighbor hops. Even the open-chain bonds
suffice,so this also proves connectivity after the periodic bond is added. -/
theorem spinSwapReach_of_minusCount_eq (L : ℕ) (q r : RowSpins L)
    (h : minusCount L q=minusCount L r) : SpinSwapReach L q r := by
  induction L with
  | zero => cases q;cases r;exact .refl
  | succ L ih =>
    rcases q with ⟨a,qt⟩
    rcases r with ⟨b,rt⟩
    fin_cases a <;> fin_cases b
    · apply spinSwapReach_prepend 0
      apply ih
      simpa only [minusCount,Fin.val_zero,zero_add] using h
    · have hpos : 0<minusCount (L+1) (0,qt) := by
        simp only [minusCount] at h ⊢
        omega
      obtain ⟨t,ht⟩ := exists_spinSwapReach_one_front L (0,qt) hpos
      have hc := spinSwapReach_minusCount ht
      have htail : minusCount L t=minusCount L rt := by
        simp only [minusCount] at h hc
        omega
      exact ht.trans (spinSwapReach_prepend 1 (ih t rt htail))
    · have hpos : 0<minusCount (L+1) (0,rt) := by
        simp only [minusCount] at h ⊢
        omega
      obtain ⟨t,ht⟩ := exists_spinSwapReach_one_front L (0,rt) hpos
      have hc := spinSwapReach_minusCount ht
      have htail : minusCount L qt=minusCount L t := by
        simp only [minusCount] at h hc
        omega
      exact (spinSwapReach_prepend 1 (ih qt t htail)).trans (spinSwapReach_symm ht)
    · apply spinSwapReach_prepend 1
      apply ih
      simp only [minusCount] at h
      omega

end SixVertex
