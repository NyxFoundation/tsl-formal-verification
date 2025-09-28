import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
-- (no big-operators import needed; we use `Finset.univ.sum` explicitly)

import TopSingleLayer.Def01

/-!
# Definition 03: Hypercube Layers

Vertices are `Fin v → Fin w`. Using the `Fin` (0..w-1) encoding, the
layer index of a vertex `x` is defined as

  `∑ i, (w - 1) - (x i).val`

which matches the paper's `v·w - ∑ x_i` in the 1..w convention.
-/

namespace TopSingleLayer

-- no special notation needed

/-- The layer of a vertex: sum over coordinates of the distance to `Fin.last`.
This is a natural number in `0..v*(w-1)`. -/
def hypercubeLayer (w v : Nat) (x : hypercubeVertices w v) : Nat :=
  (Finset.univ : Finset (Fin v)).sum (fun i => (w - 1) - (x i).val)

/-- The `d`-th layer as a set of vertices. -/
def layerSet (w v : Nat) (d : Nat) : Set (hypercubeVertices w v) :=
  { x | hypercubeLayer w v x = d }

end TopSingleLayer
