import TopSingleLayer.Def03
import TopSingleLayer.Def04
import TopSingleLayer.Def05

/-!
# Definition 08: Top Single Layer (TSL) encoding

This module specifies the Top Single Layer encoding.
The construction maps every input to a single layer
`d₀` of the `(w,v)`-hypercube via a postprocessing map `psi` applied to
the output of a (random-oracle-like) function `H`.

We keep the distributional assumptions abstract and capture the core
structure as data with properties ensuring:

- a chosen target layer index `d₀` (typically with large size), and
- all outputs lie in that layer.

From these, we define the concrete encoding function
`topSingleLayerEncoding := fun (m,r) => psi (H (m,r))` and record its
"single-layer" property.
-/

namespace TopSingleLayer

/-- The threshold used in the TSL specification: `2^lambda`. -/
def tslThreshold (lambda : Nat) : Nat := Nat.pow 2 lambda

/-- Indices of layers whose size is at least the threshold `2^λ`. -/
def tslTargetLayerSet (w v : Nat) (lambda : Nat) : Set Nat :=
  { d | layerSize w v d ≥ tslThreshold lambda }

/-- Parameters for the Top Single Layer (TSL) construction.

Fields:
- `lambda`: security parameter (appears in the size predicate).
- `d0`: chosen target layer index.
- `H`: a preprocessing map (e.g. a random oracle) from inputs to
  integers.
- `psi`: postprocessing into hypercube vertices `[w]^v`.

Assumptions:
- `d0HasSize`: the chosen layer has size at least `2^lambda`.
- `psiIntoLayer`: every output of `psi` lies in the single layer `d0`.

The distributional uniformity of `psi` over layer `d0` is intentionally
left abstract here and can be added as a separate hypothesis when
needed. -/
structure TslParams (w v : Nat) (M R X : Type) : Type where
  lambda : Nat
  d0 : Nat
  H : M × R → X
  psi : X → HcV w v
  d0HasSize : layerSize w v d0 ≥ tslThreshold lambda
  psiIntoLayer : ∀ (z : X), hypercubeLayer w v (psi z) = d0

/-- The Top Single Layer encoding associated to a choice of parameters. -/
def topSingleLayerEncoding {w v : Nat} {M R X : Type}
    (P : TslParams w v M R X) : encodingFunction w v M R :=
  fun (p : M × R) => P.psi (P.H p)

/-- All outputs of the TSL encoding lie in the target layer `d0` (as an
equality on the layer index). -/
theorem topSingleLayerEncoding_layer_eq {w v : Nat} {M R X : Type}
    (P : TslParams w v M R X) (m : M) (r : R) :
    hypercubeLayer w v (topSingleLayerEncoding P (m, r)) = P.d0 := by
  -- by definition and the `psiIntoLayer` assumption
  dsimp [topSingleLayerEncoding]
  simpa using P.psiIntoLayer (P.H (m, r))

/-- All outputs of the TSL encoding are elements of the single layer set
`L_{d0}`. -/
theorem topSingleLayerEncoding_mem_layerSet {w v : Nat} {M R X : Type}
    (P : TslParams w v M R X) (m : M) (r : R) :
    topSingleLayerEncoding P (m, r) ∈ layerSet w v P.d0 := by
  -- rewrite membership to the defining equality of `layerSet`.
  dsimp [layerSet]
  exact topSingleLayerEncoding_layer_eq (w:=w) (v:=v) (M:=M) (R:=R) P m r

/-- The code (image) of the TSL encoding is contained in the single
layer `L_{d0}`. -/
theorem topSingleLayerEncoding_code_subset {w v : Nat} {M R X : Type}
    (P : TslParams w v M R X) :
    {x : HcV w v | x ∈ codeOfEncoding (topSingleLayerEncoding P)} ⊆
      layerSet w v P.d0 := by
  intro x hx
  rcases hx with ⟨m, r, hx⟩
  -- map the witness through the layer equality
  subst hx
  -- choose the same witnesses to show membership in `layerSet`
  have := topSingleLayerEncoding_layer_eq (w:=w) (v:=v) (M:=M) (R:=R) P m r
  dsimp [layerSet]
  simpa using this

end TopSingleLayer
