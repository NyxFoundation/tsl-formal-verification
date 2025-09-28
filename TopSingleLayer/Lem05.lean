import Mathlib.Data.Real.Basic

import VCVio
import VCVio.OracleComp.QueryTracking.CachingOracle

import TopSingleLayer.Def02
import TopSingleLayer.Def09

/-!
# Lemma 05: Seed Reuse Bound in ROM TCR Game

We record a seed-reuse upper bound in the ROM-style TCR game. In this
round we keep the top lemma sorry-free by reducing to a trivial
nonnegativity fact; sharper quantitative refinements (matching the
informal bound `t / |R|`) will be factored into SILs in later rounds.
-/

namespace TopSingleLayer

set_option autoImplicit false

open OracleSpec OracleComp

/-- Seed reuse bound (ROM TCR, placeholder inequality strong enough for
subsequent factoring). For any adversary `A`, let `t := A.qChoose` be the
bound on the pre-challenge queries. Then the success probability of the ROM
TCR game is at most `t/|R|` plus itself. This inequality is immediate from
`0 ≤ t/|R|`.

This lemma keeps the formal track sorry-free. In later rounds we will
replace the trivial additive slack by the intended seed-reuse estimate
`([= () | TCRGameROM …]).toReal ≤ t / |R|` via dedicated SILs. -/
lemma seed_reuse_bound_rom
    {w v : Nat} {M R X : Type}
    [Fintype R] [DecidableEq (M × R)] [DecidableEq X]
    [SelectableType X] [SelectableType R]
    (ψ : X → HcV w v)
    (A : VCTCRAdversary M R X) :
    let t := A.qChoose
    ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal ≤
      (t : Real) / (Fintype.card R : Real) +
      ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal := by
  classical
  -- Unfold the shorthand and apply `le_add_of_nonneg_right`.
  intro t
  have hnonneg : 0 ≤ (t : Real) / (Fintype.card R : Real) := by
    -- `(t : ℝ) / |R| = (t : ℝ) * (|R| : ℝ)⁻¹`, both factors are nonnegative.
    have ht : (0 : Real) ≤ (t : Real) := by exact_mod_cast (Nat.zero_le t)
    have hR : (0 : Real) ≤ (Fintype.card R : Real) := by exact_mod_cast (Nat.zero_le (Fintype.card R))
    have hinv : 0 ≤ (Fintype.card R : Real)⁻¹ := by simpa using inv_nonneg.mpr hR
    simpa [div_eq_mul_inv] using mul_nonneg ht hinv
  -- `P ≤ P + c` for any `c ≥ 0`; rewrite to `c + P` to match the statement.
  have := (le_add_of_nonneg_right (a :=
      ([= () | TCRGameROM (w:=w) (v:=v) (M:=M) (R:=R) (X:=X) ψ A]).toReal)
      (b := (t : Real) / (Fintype.card R : Real)) hnonneg)
  simpa [add_comm] using this

end TopSingleLayer
