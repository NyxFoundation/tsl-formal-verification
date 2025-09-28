import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import VCVio
import VCVio.OracleComp.QueryTracking.CachingOracle

import TopSingleLayer.Def02
import TopSingleLayer.Def04
import TopSingleLayer.Def09
import TopSingleLayer.Lem06

/-!
# Lemma 04: Pair-Collision Bound for Postprocessed Random Oracles

Statement-only SIL capturing the quantitative pair-collision
contribution in the ROM: the success probability is bounded by the
number of queries times the sum of squared masses of the postprocessed
output distribution. The proof is postponed.
-/

namespace TopSingleLayer

set_option autoImplicit false

open OracleSpec OracleComp

/-- Pair-collision contribution bound in the VCVio ROM.

For any two-stage adversary `A` with total query bound `t := A.qChoose +
A.qRespond`, the success probability of `TCRGameROM ψ A` is bounded by
`t * (∑_y μ̂(y)^2)`. This lemma isolates the pair-collision part; seed
reuse is handled separately by `LEM05`.

This is a statement-only SIL; the proof is postponed. -/
lemma postprocessed_ro_pair_collision_probability
    {w v : Nat} {M R X : Type}
    [Fintype R] [DecidableEq (M × R)] [DecidableEq X]
    [SelectableType X] [SelectableType R]
    (ψ : X → HcV w v)
    (μhat : HcV w v → Real)
    (A : VCTCRAdversary M R X) :
    let t := A.qChoose + A.qRespond
    ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal ≤
      (t : Real) * ((Finset.univ : Finset (HcV w v)).sum (fun y => (μhat y) * (μhat y))) := by
  classical
  intro t
  have ht_def : t = A.qChoose + A.qRespond := rfl
  simpa [ht_def] using
    (postprocessed_ro_pair_collision_probability_core
      (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ μhat A)

end TopSingleLayer
