import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import VCVio
import VCVio.OracleComp.QueryTracking.CachingOracle

import TopSingleLayer.Def04
import TopSingleLayer.Def07
import TopSingleLayer.Def09
import TopSingleLayer.Lem03

/-!
# Lemma 02: Target-Collision Bound for Postprocessed Random Oracles

This module states (without proof) a TCR bound for encodings obtained by
postprocessing the output of a pre-hash `H : M × R → X` with a function
`ψ : X → [w]^v`. The statement is phrased using the abstract TCR notion
from `Def07` with a `Real`-valued advantage and
an arbitrary probability functional `Pr : (R → Prop) → ℝ`.

The numerical bound matches the shape in the paper: for any query bound
`t`, the advantage is bounded by `t / |R| + t * (∑_y μ̂(y)^2)`, where
`μ̂ : [w]^v → ℝ` is an (abstract) mass function describing the output
distribution of `ψ` on uniform inputs.
-/

namespace TopSingleLayer

set_option autoImplicit false

/-!
## VCVio-based variant (ROM with caching random oracle)

Below we restate the same target-collision bound in the VCVio style,
modeling the pre-hash as a random oracle using a cached uniform
simulation. This is a statement-only stub that compiles against VCVio,
and can be filled in later.
-/

open OracleSpec OracleComp

/-- Postprocessed ROM TCR bound using VCVio semantics (statement only).

For any adversary `A` that makes at most `qChoose` queries before
seeing `r`, and at most `qRespond` after receiving `r`, the success
probability of `TCRGameROM ψ A` is bounded by

  (qChoose + qRespond)/|R| + (qChoose + qRespond) * ∑_y μ̂(y)^2.

This is a placeholder; the proof is omitted. -/
lemma post_processed_ro_tc_bound
    {w v : Nat} {M R X : Type}
    [Fintype R] [DecidableEq (M × R)] [DecidableEq X]
    [SelectableType X] [SelectableType R]
    (ψ : X → HcV w v)
    (μhat : HcV w v → Real)
    (A : VCTCRAdversary M R X) :
    let t := A.qChoose + A.qRespond
    ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal ≤
      (t : Real) / (Fintype.card R : Real) +
      (t : Real) * ((Finset.univ : Finset (HcV w v)).sum (fun y => (μhat y) * (μhat y))) := by
  -- Reduce to the SIL lemma `post_processed_ro_tc_bound_main` (LEM03).
  exact post_processed_ro_tc_bound_main (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ μhat A

end TopSingleLayer
