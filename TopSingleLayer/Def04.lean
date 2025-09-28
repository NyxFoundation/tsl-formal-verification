import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Interval
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Order.Interval.Finset.Nat

import TopSingleLayer.Def01
import TopSingleLayer.Def03

/-!
# Definition 04: Sizes of Hypercube Layers

Layer sizes are defined as the cardinality of each layer `L_d = {x | layer x = d}`.
We also provide the summed size over a closed interval of layer indices.
-/

namespace TopSingleLayer

/-- Finite instance for the hypercube vertex type `[w]^v`. -/
instance instFintypeHypercubeVertices (w v : Nat) :
    Fintype (hypercubeVertices w v) := by
  dsimp [hypercubeVertices]
  infer_instance

/-- Size of the `d`-th layer: `|{ x ∈ [w]^v | hypercubeLayer w v x = d }|`. -/
def layerSize (w v : Nat) (d : Nat) : Nat :=
  Fintype.card { x : hypercubeVertices w v // hypercubeLayer w v x = d }

/-- Sum of layer sizes over the closed interval `d ∈ [d₁, d₂]` (inclusive). -/
def layerSizeSum (w v : Nat) (d₁ d₂ : Nat) : Nat :=
  (Finset.Icc d₁ d₂).sum (fun d => layerSize w v d)

end TopSingleLayer
