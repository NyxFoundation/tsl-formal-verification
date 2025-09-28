import Mathlib.Data.Fin.Basic

/-!
# Definition 01: Hypercube

This file defines the hypercube `([w]^v, edge)`:

- Vertices: `Fin v → Fin w`
- Directed edge `x ⟶ y` iff there exists an index `i : Fin v` such that
  the `i`-th coordinate increases by exactly one and all other coordinates
  remain unchanged.

The representation follows the spec in `def01_hypercube.md`.
-/

namespace TopSingleLayer

/-- The vertex type of the `(w,v)` hypercube: functions from `Fin v` to `Fin w`.
This corresponds to `[w]^v` in the paper. -/
def hypercubeVertices (w : Nat) (v : Nat) : Type := Fin v → Fin w

/-- The directed edge relation on the `(w,v)` hypercube.
There is an edge from `x` to `y` iff some coordinate increases by one
and all other coordinates stay the same. -/
def hypercubeEdge {w : Nat} {v : Nat}
    (x : hypercubeVertices w v) (y : hypercubeVertices w v) : Prop :=
  ∃ (i : Fin v),
    (y i).val = (x i).val + 1 ∧
    ∀ (j : Fin v), j ≠ i → y j = x j

end TopSingleLayer
