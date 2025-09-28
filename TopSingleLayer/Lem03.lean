import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import VCVio
import VCVio.OracleComp.QueryTracking.CachingOracle

import TopSingleLayer.Def04
import TopSingleLayer.Def09
import TopSingleLayer.Lem05
import TopSingleLayer.Lem04

/-!
# Lemma 03: Postprocessed ROM Pair-Collision Probability

This lemma packages the quantitative target-collision bound for the
postprocessed random-oracle model into a single statement. It is used as
an intermediate step by `Lem02.lean`. The proof is deferred.
-/

namespace TopSingleLayer

set_option autoImplicit false

open OracleSpec OracleComp

/-- Postprocessed ROM TCR bound using VCVio semantics (statement only).

For any adversary `A` that makes at most `qChoose` queries before
seeing `r`, and at most `qRespond` after receiving `r`, the success
probability of `TCRGameROM ψ A` is bounded by

  (qChoose + qRespond)/|R| + (qChoose + qRespond) * ∑_y μ̂(y)^2.

This is a statement-only SIL; the proof is postponed. -/
lemma post_processed_ro_tc_bound_main
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
  classical
  intro t
  -- Seed-reuse bound (LEM05) with `qChoose`, then monotone in `t = qChoose + qRespond`.
  have h_seed_qc :
      ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal ≤
        ((A.qChoose : Real) / (Fintype.card R : Real) +
         ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal) := by
    simpa using
      (seed_reuse_bound_rom (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A)
  -- Monotonicity to replace `qChoose/|R|` by `t/|R|`.
  have ht_def : t = A.qChoose + A.qRespond := rfl
  have h_le_cast : (A.qChoose : Real) ≤ (t : Real) := by
    -- `qChoose ≤ qChoose + qRespond` in `ℝ`.
    have hnat : A.qChoose ≤ A.qChoose + A.qRespond := Nat.le_add_right _ _
    simpa [ht_def] using (show (A.qChoose : Real) ≤ (A.qChoose + A.qRespond : Nat) from
      (by exact_mod_cast hnat))
  have hR_nonneg : 0 ≤ (Fintype.card R : Real) := by
    exact_mod_cast (Nat.zero_le (Fintype.card R))
  have h_div_mono :
      (A.qChoose : Real) / (Fintype.card R : Real) ≤
      (t : Real) / (Fintype.card R : Real) := by
    exact div_le_div_of_nonneg_right h_le_cast hR_nonneg
  have h_seed_t :
      ((A.qChoose : Real) / (Fintype.card R : Real) +
        ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal)
        ≤ ((t : Real) / (Fintype.card R : Real) +
           ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal) := by
    exact add_le_add_right h_div_mono _
  have h_seed :
      ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal ≤
      ((t : Real) / (Fintype.card R : Real) +
       ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal) :=
    le_trans h_seed_qc h_seed_t
  -- Pair-collision contribution (LEM04): `P ≤ t * ∑ μ̂^2`.
  have h_pair :
      ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal ≤
      (t : Real) * ((Finset.univ : Finset (HcV w v)).sum (fun y => (μhat y) * (μhat y))) := by
    simpa [ht_def] using
      (postprocessed_ro_pair_collision_probability
        (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ μhat A)
  -- Add `(t/|R|)` to both sides of the pair-collision bound and chain.
  have h_add :
      ((t : Real) / (Fintype.card R : Real) +
        ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal) ≤
      ((t : Real) / (Fintype.card R : Real) +
        (t : Real) * ((Finset.univ : Finset (HcV w v)).sum (fun y => (μhat y) * (μhat y)))) := by
    exact add_le_add_left h_pair _
  -- Final chaining: `P ≤ t/|R| + P ≤ t/|R| + t * ∑ μ̂^2`.
  exact le_trans h_seed h_add

end TopSingleLayer
