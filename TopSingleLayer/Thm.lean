import TopSingleLayer.Def06
import TopSingleLayer.Def08
import TopSingleLayer.Lem01
import TopSingleLayer.Lem02
import VCVio

/-!
# Theorem: TSL encoding is incomparable and TCR-bounded

This module proves the two headline properties of the Top Single Layer
encoding (TSL):

- Incomparability: the image of the encoding consists of pairwise
  incomparable vertices (by reduction to Lemma 01 on a single layer).
- Target-collision resistance: instantiate the generic postprocessed
  random-oracle bound (Lemma 02) with the TSL parameters.
-/

namespace TopSingleLayer

set_option autoImplicit false


/-- The TSL encoding has a code contained in a single layer `L_{d0}`;
any two distinct outputs are incomparable (coordinatewise). -/
theorem tsl_incomparable
    {w v : Nat} {M R X : Type}
    (P : TslParams w v M R X) :
    incomparableEncoding (w:=w) (v:=v) (M:=M) (R:=R)
      (topSingleLayerEncoding P) := by
  intro x y hx hy hxy
  -- Map code-membership into the target layer `L_{d0}`.
  have hxL : x ∈ layerSet w v P.d0 := by
    exact (topSingleLayerEncoding_code_subset (w:=w) (v:=v) (M:=M) (R:=R) P) hx
  have hyL : y ∈ layerSet w v P.d0 := by
    exact (topSingleLayerEncoding_code_subset (w:=w) (v:=v) (M:=M) (R:=R) P) hy
  -- Apply Lemma 01 instantiated to the common layer `d0`.
  simpa using
    (same_layer_vertices_are_incomparable (w:=w) (v:=v) (d:=P.d0)
      (x:=x) (y:=y) hxL hyL hxy)

/-- VCVio-style target-collision bound for the TSL encoding in the ROM.
We instantiate the cached random-oracle bound (Lemma 02, VCVio variant)
with the TSL postprocessing `psi`. The pre-hash domain `X` is assumed to
be uniformly samplable via `SelectableType X` (used by the ROM). -/
theorem tsl_tcr_bound
  {w v : Nat} {M R X : Type}
  [Fintype R] [DecidableEq (M × R)] [DecidableEq X]
  [OracleComp.SelectableType X] [OracleComp.SelectableType R]
  (P : TslParams w v M R X)
  (μhat : HcV w v → Real)
  (A : VCTCRAdversary M R X) :
  let t := A.qChoose + A.qRespond
  ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) P.psi A]).toReal ≤
    (t : Real) / (Fintype.card R : Real) +
    (t : Real) * ((Finset.univ : Finset (HcV w v)).sum (fun y => (μhat y) * (μhat y))) := by
  classical
  -- Directly reuse the generic VCVio ROM lemma with `ψ := P.psi`.
  simpa using
    (post_processed_ro_tc_bound (w:=w) (v:=v)
      (M:=M) (R:=R) (X:=X) (ψ:=P.psi) (μhat:=μhat) (A:=A))

end TopSingleLayer
