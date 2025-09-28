import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Defs

import VCVio
import VCVio.OracleComp.QueryTracking.CachingOracle

import TopSingleLayer.Def02

/-!
# Definition 09: ROM game and adversary for postprocessed pre-hash

This module factors out the VCVio-based random-oracle model artifacts
used across lemmas, so propositions can import a single place for the
game and adversary definitions without creating cyclic dependencies.
-/

namespace TopSingleLayer

set_option autoImplicit false

open OracleSpec OracleComp

/-- Convenience alias: the oracle spec for a single pre-hash oracle
`H : M × R → X` (modeled as a random oracle). -/
abbrev PreHashSpec (M R X : Type _) : OracleSpec PUnit := (M × R) →ₒ X

/-- Two-stage TCR adversary interacting with the pre-hash oracle in VCVio. -/
structure VCTCRAdversary (M R X : Type _) : Type _ where
  /-- First phase: outputs a target message. -/
  choose  : OracleComp (PreHashSpec M R X) M
  /-- Second phase: given a seed `r`, outputs a new message and seed. -/
  respond : R → OracleComp (PreHashSpec M R X) (M × R)
  /-- Query bound for phase 1 (pre-challenge). -/
  qChoose : Nat
  /-- Query bound for phase 2 (post-challenge). -/
  qRespond : Nat
  /-- Proof that `qChoose` bounds the number of oracle queries in `choose`. -/
  choose_qb  : OracleComp.IsQueryBound choose (fun _ => qChoose)
  /-- Proof that `qRespond` bounds the number of oracle queries in `respond r`. -/
  respond_qb : ∀ r, OracleComp.IsQueryBound (respond r) (fun _ => qRespond)

/-- TCR game in the ROM using VCVio’s cached random oracle.
Returns `()` on success and `failure` otherwise (so `[= () | …]` is the
success probability). The postprocessing `ψ` maps hash outputs to
hypercube vertices. -/
noncomputable def TCRGameROM
    {w v : Nat} {M R X : Type}
    [DecidableEq (M × R)] [DecidableEq X]
    [SelectableType X] [SelectableType R]
    (ψ : X → HcV w v)
    (A : VCTCRAdversary M R X) : ProbComp Unit := by
  classical
  -- Random oracle for the single pre-hash oracle `(M × R) →ₒ X` with caching.
  let so : QueryImpl (PreHashSpec M R X)
      (StateT (PreHashSpec M R X).QueryCache (ProbComp)) :=
    randomOracle
  -- Run phase 1 under the random oracle with an empty cache.
  let s0 : (PreHashSpec M R X).QueryCache := (∅)
  -- Using do-notation in ProbComp to thread the state explicitly.
  exact do
    let (m, s1) ← (simulateQ so A.choose).run s0
    let r ← $ᵗ R
    let ((m', r'), s2) ← (simulateQ so (A.respond r)).run s1
    -- Evaluate the two hash points under the same cache to preserve ROM consistency.
    let (x1, s3) ← (simulateQ so (OracleComp.lift (OracleSpec.query PUnit.unit (m, r)))).run s2
    let (x2, _s4) ← (simulateQ so (OracleComp.lift (OracleSpec.query PUnit.unit (m', r')))).run s3
    let y1 := ψ x1; let y2 := ψ x2
    guard (y1 = y2 ∧ m' ≠ m)
    pure ()

end TopSingleLayer
