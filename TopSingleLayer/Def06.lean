import TopSingleLayer.Def02
import TopSingleLayer.Def05

/-!
# Definition 06: Incomparability

An encoding `f : M × R → [w]^v` is incomparable if any two distinct
outputs in its image are incomparable with respect to the coordinatewise
order `hypercubeLe`.
-/

namespace TopSingleLayer

/-- Two vertices are incomparable (w.r.t. `hypercubeLe`) if neither is
coordinatewise ≤ the other. -/
def incomparablePair {w v : Nat} (x y : HcV w v) : Prop :=
  x ≠ y ∧ ¬ hypercubeLe x y ∧ ¬ hypercubeLe y x

/-- The image (code) of an encoding contains only pairwise-incomparable
vertices. -/
def incomparableEncoding {w v : Nat} {M R : Type}
    (f : encodingFunction w v M R) : Prop :=
  ∀ {x y : HcV w v},
    x ∈ codeOfEncoding f → y ∈ codeOfEncoding f → x ≠ y →
      (¬ hypercubeLe x y ∧ ¬ hypercubeLe y x)

end TopSingleLayer
