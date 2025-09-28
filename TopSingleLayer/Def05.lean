import TopSingleLayer.Def02

/-!
# Definition 05: Encoding Function

This file formalizes encoding functions whose codomain is the
vertex set of the `(w,v)` hypercube `Fin v → Fin w`.

- `encodingFunction w v M R := M × R → Fin v → Fin w`
- Deterministic encodings are `M → Fin v → Fin w` and embed via `Unit`.
- `codeOfEncoding f` is the image (set of outputs) of an encoding `f`.
-/

namespace TopSingleLayer

/-- An encoding function with domain `M`, seed space `R`, and codomain `[w]^v`. -/
abbrev encodingFunction (w : Nat) (v : Nat) (M : Type) (R : Type) : Type :=
  M × R → HcV w v

/-- A deterministic encoding has no seed: a function `M → [w]^v`. -/
abbrev detEncoding (w : Nat) (v : Nat) (M : Type) : Type :=
  M → HcV w v

/-- Embed a deterministic encoding as an encoding with `Unit` seed. -/
def detToEncoding {w : Nat} {v : Nat} {M : Type}
    (g : detEncoding w v M) : encodingFunction w v M Unit :=
  fun (p : M × Unit) => g p.fst

/-- The image (set of outputs) of an encoding `f : M × R → [w]^v`. -/
def codeOfEncoding {w : Nat} {v : Nat} {M : Type} {R : Type}
    (f : encodingFunction w v M R) : Set (HcV w v) :=
  { x | ∃ (m : M) (r : R), f (m, r) = x }

end TopSingleLayer
