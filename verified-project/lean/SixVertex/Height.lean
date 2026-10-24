import SixVertex.Finite

/-!
Local height consistency in the paper's convention: the face to the left of
an arrow has height one more than the face to its right. This proves the
one-vertex integrability condition. Global path independence on a simply
connected domain and torus winding sectors remain separate obligations.
-/

namespace SixVertex

def spin (b : Bool) : Int := if b then 1 else -1

@[simp] theorem spin_false : spin false = -1 := rfl
@[simp] theorem spin_true : spin true = 1 := rfl

@[simp] theorem spin_reverse (b : Bool) : spin (!b) = -spin b := by
  cases b <;> decide

/-- Height change from the southwest face to the northeast face via northwest. -/
def northwestRoute (v : Vertex) : Int := spin v.west - spin v.north

/-- The same height change, via the southeast face. -/
def southeastRoute (v : Vertex) : Int := -spin v.south + spin v.east

/-- The ice rule is exactly equality of the two elementary dual routes. -/
theorem ice_iff_height_routes (v : Vertex) :
    Ice v ↔ northwestRoute v = southeastRoute v := by
  rcases v with ⟨w, e, s, n⟩
  cases w <;> cases e <;> cases s <;> cases n <;> decide

/-- Counterclockwise height circulation around a primal vertex. -/
def heightCurl (v : Vertex) : Int :=
  -spin v.south + spin v.east + spin v.north - spin v.west

theorem ice_iff_zero_heightCurl (v : Vertex) : Ice v ↔ heightCurl v = 0 := by
  rcases v with ⟨w, e, s, n⟩
  cases w <;> cases e <;> cases s <;> cases n <;> decide

/-- Four adjacent face heights, with a chosen southwest additive constant. -/
structure LocalHeight where
  southwest : Int
  southeast : Int
  northwest : Int
  northeast : Int
  deriving DecidableEq, Repr

def LocalHeight.Realizes (h : LocalHeight) (v : Vertex) : Prop :=
  h.northwest - h.southwest = spin v.west ∧
  h.northeast - h.southeast = spin v.east ∧
  h.southwest - h.southeast = spin v.south ∧
  h.northwest - h.northeast = spin v.north

def localHeight (v : Vertex) (anchor : Int) : LocalHeight :=
  ⟨anchor, anchor - spin v.south, anchor + spin v.west,
    anchor + northwestRoute v⟩

theorem localHeight_realizes (v : Vertex) (hv : Ice v) (anchor : Int) :
    (localHeight v anchor).Realizes v := by
  have hr := (ice_iff_height_routes v).mp hv
  simp only [northwestRoute, southeastRoute] at hr
  simp only [LocalHeight.Realizes, localHeight, northwestRoute]
  omega

theorem realizes_implies_ice (h : LocalHeight) (v : Vertex)
    (hv : h.Realizes v) : Ice v := by
  apply (ice_iff_height_routes v).mpr
  simp only [LocalHeight.Realizes] at hv
  simp only [northwestRoute, southeastRoute]
  omega

theorem localHeight_unique (h : LocalHeight) (v : Vertex)
    (hv : h.Realizes v) : h = localHeight v h.southwest := by
  rcases h with ⟨sw, se, nw, ne⟩
  rcases hv with ⟨h1, h2, h3, h4⟩
  dsimp at h1 h2 h3 h4
  change LocalHeight.mk sw se nw ne =
    LocalHeight.mk sw (sw - spin v.south) (sw + spin v.west)
      (sw + (spin v.west - spin v.north))
  congr 1 <;> omega

end SixVertex
