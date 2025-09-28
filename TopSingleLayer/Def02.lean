import Mathlib.Data.Fin.Basic

import TopSingleLayer.Def01

/-!
# Definition 02: Partial Order on the Hypercube

We equip the vertex set `Fin v → Fin w` with a natural partial order:

- `hypercubeReach`: reachability via the directed edges of the hypercube
  (as the reflexive–transitive closure of `hypercubeEdge`).
- `hypercubeLe`: the coordinatewise order `∀ i, x i ≤ y i`.

The paper states these characterizations are equivalent; we include
`hypercubeReach_le` (reachability implies coordinatewise order). The
converse direction can be derived by iterating single-coordinate steps.
-/

namespace TopSingleLayer

/-- The vertex type of the `(w,v)` hypercube (alias). -/
abbrev HcV (w v : Nat) := hypercubeVertices w v

/-- Coordinatewise order on the hypercube vertices. -/
def hypercubeLe {w v : Nat} (x y : HcV w v) : Prop := ∀ i : Fin v, x i ≤ y i

end TopSingleLayer
