import Mathlib.Algebra.Order.BigOperators.Group.Finset
import TopSingleLayer.Def02
import TopSingleLayer.Def03

/-!
# Lemma 01: Vertices on the Same Layer are Incomparable

If two distinct vertices lie in the same layer `L_d` of the `(w,v)`
hypercube, then they are incomparable with respect to the coordinatewise
order `hypercubeLe`.

This follows the statement in `lem01.md`.
-/

namespace TopSingleLayer

set_option autoImplicit false

/-- Any two distinct vertices in the same layer `L_d` are incomparable
with respect to the coordinatewise order `hypercubeLe`. -/
lemma same_layer_vertices_are_incomparable
    {w v d : Nat} {x y : HcV w v}
    (hx : x ∈ layerSet w v d) (hy : y ∈ layerSet w v d)
    (hxy : x ≠ y) :
    (¬ hypercubeLe (w:=w) (v:=v) x y ∧ ¬ hypercubeLe (w:=w) (v:=v) y x) := by
  classical
  have hx' : hypercubeLayer w v x = d := by simpa [layerSet] using hx
  have hy' : hypercubeLayer w v y = d := by simpa [layerSet] using hy
  -- A useful identity: for any z, the layer-sum plus the value-sum equals
  -- the constant sum of (w - 1) over all coordinates.
  have sum_const_eq_x :
      (Finset.univ : Finset (Fin v)).sum (fun i => (w - 1) - (x i).val)
        + (Finset.univ : Finset (Fin v)).sum (fun i => (x i).val)
        = (Finset.univ : Finset (Fin v)).sum (fun _ => (w - 1)) := by
    -- pointwise: ((w-1) - (x i).val) + (x i).val = (w - 1)
    have hx_bound : ∀ i : Fin v, (x i).val ≤ w - 1 := by
      intro i; exact Nat.le_pred_of_lt (x i).isLt
    have hpoint : ∀ i : Fin v, ((w - 1) - (x i).val) + (x i).val = (w - 1) := by
      intro i; simp [Nat.sub_add_cancel (hx_bound i)]
    calc
      _ = (Finset.univ : Finset (Fin v)).sum (fun i => ((w - 1) - (x i).val) + (x i).val) := by
        simp [Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]
      _ = (Finset.univ : Finset (Fin v)).sum (fun _ => (w - 1)) := by
        refine Finset.sum_congr rfl ?_
        intro i _; simp [hpoint i]
  have sum_const_eq_y :
      (Finset.univ : Finset (Fin v)).sum (fun i => (w - 1) - (y i).val)
        + (Finset.univ : Finset (Fin v)).sum (fun i => (y i).val)
        = (Finset.univ : Finset (Fin v)).sum (fun _ => (w - 1)) := by
    have hy_bound : ∀ i : Fin v, (y i).val ≤ w - 1 := by
      intro i; exact Nat.le_pred_of_lt (y i).isLt
    have hpoint : ∀ i : Fin v, ((w - 1) - (y i).val) + (y i).val = (w - 1) := by
      intro i; simp [Nat.sub_add_cancel (hy_bound i)]
    calc
      _ = (Finset.univ : Finset (Fin v)).sum (fun i => ((w - 1) - (y i).val) + (y i).val) := by
        simp [Finset.sum_add_distrib, add_comm, add_left_comm, add_assoc]
      _ = (Finset.univ : Finset (Fin v)).sum (fun _ => (w - 1)) := by
        refine Finset.sum_congr rfl ?_
        intro i _; simp [hpoint i]
  -- From hx' and hy', deduce equality of the coordinate sums of x and y.
  have sum_vals_eq :
      (Finset.univ : Finset (Fin v)).sum (fun i => (x i).val) =
      (Finset.univ : Finset (Fin v)).sum (fun i => (y i).val) := by
    -- Replace layer sums by d using hx' and hy'.
    have hx_rew :
        (Finset.univ : Finset (Fin v)).sum (fun i => (w - 1) - (x i).val) = d := by
      simpa [hypercubeLayer] using hx'
    have hy_rew :
        (Finset.univ : Finset (Fin v)).sum (fun i => (w - 1) - (y i).val) = d := by
      simpa [hypercubeLayer] using hy'
    -- Prepare the two equalities with `d` on the left and cancel.
    have hx_eq : d + (Finset.univ).sum (fun i => (x i).val)
        = (Finset.univ : Finset (Fin v)).sum (fun _ => (w - 1)) := by
      simpa [hx_rew] using sum_const_eq_x
    have hy_eq : d + (Finset.univ).sum (fun i => (y i).val)
        = (Finset.univ : Finset (Fin v)).sum (fun _ => (w - 1)) := by
      simpa [hy_rew] using sum_const_eq_y
    have := hx_eq.trans (hy_eq.symm)
    exact Nat.add_left_cancel this
  refine And.intro ?left ?right
  · -- show ¬ x ≤ y using the equality of sums and existence of a strict coord
    intro hxyLe
    -- There must be a strictly increasing coordinate; otherwise x = y.
    have h_exists_lt : ∃ i : Fin v, (x i).val < (y i).val := by
      by_contra hnone
      have hall_eq : ∀ i : Fin v, (x i).val = (y i).val := by
        intro i
        obtain hlt | heq := lt_or_eq_of_le (by simpa using (hxyLe i))
        · exact False.elim (hnone ⟨i, by simpa using hlt⟩)
        · exact congrArg Fin.val heq
      -- extensionality on coordinates
      apply hxy
      funext i
      -- Fin equality from equal values via `Fin.ext`
      apply Fin.ext
      simp [hall_eq i]
    rcases h_exists_lt with ⟨i0, hi0⟩
    -- Pointwise ≤ and a single strict coordinate force a strict sum inequality.
    have hsum_lt :
        (Finset.univ : Finset (Fin v)).sum (fun i => (x i).val) <
        (Finset.univ : Finset (Fin v)).sum (fun i => (y i).val) := by
      refine Finset.sum_lt_sum ?hle ?hlt
      · intro i _; simpa using (hxyLe i)
      · exact ⟨i0, by simp, hi0⟩
    -- Contradiction with the equality of sums derived from the layer equality.
    have : False := by simpa [sum_vals_eq] using hsum_lt
    exact this.elim
  · -- symmetric direction: ¬ y ≤ x
    intro hyxLe
    have h_exists_lt : ∃ i : Fin v, (y i).val < (x i).val := by
      by_contra hnone
      have hall_eq : ∀ i : Fin v, (y i).val = (x i).val := by
        intro i
        obtain hlt | heq := lt_or_eq_of_le (by simpa using (hyxLe i))
        · exact False.elim (hnone ⟨i, by simpa using hlt⟩)
        · exact congrArg Fin.val heq
      apply hxy
      funext i
      apply Fin.ext
      simp [hall_eq i]
    rcases h_exists_lt with ⟨i0, hi0⟩
    have hsum_lt :
        (Finset.univ : Finset (Fin v)).sum (fun i => (y i).val) <
        (Finset.univ : Finset (Fin v)).sum (fun i => (x i).val) := by
      refine Finset.sum_lt_sum ?hle' ?hlt'
      · intro i _; simpa using (hyxLe i)
      · exact ⟨i0, by simp, hi0⟩
    -- This contradicts `sum_vals_eq`.
    have : False := by simpa [sum_vals_eq] using hsum_lt
    exact this.elim

end TopSingleLayer
