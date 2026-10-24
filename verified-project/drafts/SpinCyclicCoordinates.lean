import SixVertex.SpinSitePermutation
import Mathlib.Logic.Equiv.Fin.Rotate

namespace SixVertex
noncomputable section

/-- Appending the physical last spin agrees exactly with the finite site tuple. -/
theorem rowSpinAt_appendSpin (n : ℕ) (q : RowSpins n) (a : Fin 2) :
    rowSpinAt (n+1) (appendSpin n q a)=Fin.snoc (rowSpinAt n q) a := by
  induction n with
  | zero =>
    cases q
    funext i
    have hi : i=0 := by apply Fin.ext;omega
    subst i
    rfl
  | succ n ih =>
    change @Fin.cons (n+1) (fun _ => Fin 2) q.1 (rowSpinAt (n+1) (appendSpin n q.2 a))=
      @Fin.snoc (n+1) (fun _ => Fin 2) (@Fin.cons n (fun _ => Fin 2) q.1 (rowSpinAt n q.2)) a
    rw [ih]
    exact Fin.cons_snoc_eq_snoc_cons q.1 (rowSpinAt n q.2) a

/-- The actual physical translation is precisely rotation of the finite
site bits,including its periodic endpoint. -/
theorem rowSpinAt_cyclicSpinTranslation (n : ℕ) (q : RowSpins (n+1)) :
    rowSpinAt (n+1) (cyclicSpinTranslation n q)=
      fun i => rowSpinAt (n+1) q (finRotate (n+1) i) := by
  change rowSpinAt (n+1) (appendSpin n q.2 q.1)=_
  rw [rowSpinAt_appendSpin]
  exact Fin.snoc_eq_cons_rotate _ _

theorem cyclicSpinTranslation_eq_permuteSpinSites (n : ℕ) (q : RowSpins (n+1)) :
    cyclicSpinTranslation n q=permuteSpinSites (n+1) (finRotate (n+1)) q := by
  apply (rowSpinSitesEquiv (n+1)).injective
  exact (rowSpinAt_cyclicSpinTranslation n q).trans
    (rowSpinAt_permuteSpinSites (n+1) (finRotate (n+1)) q).symm

/-- All physical translation powers rotate the same actual sites. -/
theorem rowSpinAt_cyclicSpinTranslation_pow (n k : ℕ) (q : RowSpins (n+1)) :
    rowSpinAt (n+1) (((cyclicSpinTranslation n)^k) q)=
      fun i => rowSpinAt (n+1) q (((finRotate (n+1))^k) i) := by
  induction k generalizing q with
  | zero => simp
  | succ k ih =>
    rw [pow_succ']
    change rowSpinAt (n+1) (cyclicSpinTranslation n (((cyclicSpinTranslation n)^k) q))=_
    rw [rowSpinAt_cyclicSpinTranslation,ih]
    funext i
    rw [pow_succ]
    rfl

end
end SixVertex
