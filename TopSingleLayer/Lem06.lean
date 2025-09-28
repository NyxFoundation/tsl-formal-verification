import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import VCVio
import VCVio.OracleComp.QueryTracking.CachingOracle

import TopSingleLayer.Def02
import TopSingleLayer.Def04
import TopSingleLayer.Def09

/-!
# Lemma 06: Core Pair-Collision Bound for Postprocessed Random Oracles

Statement-only SIL that mirrors the target LEM04 statement. This allows
the target lemma to be proved by delegation while we postpone the core
probabilistic argument to a future round.
-/

namespace TopSingleLayer

set_option autoImplicit false

open OracleSpec OracleComp

/-- Core pair-collision contribution bound in the VCVio ROM.

This mirrors the statement used by `Lem04.lean` and is left as a
statement-only SIL (proof postponed). -/
lemma postprocessed_ro_pair_collision_probability_core
    {w v : Nat} {M R X : Type}
    [Fintype R] [DecidableEq (M × R)] [DecidableEq X]
    [SelectableType X] [SelectableType R]
    (ψ : X → HcV w v)
    (μhat : HcV w v → Real)
    (A : VCTCRAdversary M R X) :
    let t := A.qChoose + A.qRespond
    ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal ≤
      (t : Real) * ((Finset.univ : Finset (HcV w v)).sum (fun y => (μhat y) * (μhat y))) := by
  sorry

end TopSingleLayer
