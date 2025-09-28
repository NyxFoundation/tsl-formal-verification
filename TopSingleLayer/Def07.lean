import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import TopSingleLayer.Def05

/-!
# Definition 07: Target Collision Resistance (TCR)

This module formalizes the two-stage target-collision resistance game
for encodings `f : M × R → [w]^v` and the corresponding ε-security
statement.

- An adversary runs in two phases: it first outputs a target message and
  internal state, then receives a random seed `r : R` and outputs a new
  message and seed. It succeeds if it finds a target collision
  `f(m,r) = f(m*,r*)` with `m* ≠ m`.
- We keep the runtime bound abstract as a numeric field on the adversary
  and leave the probability/operator over `R` abstract via a functional
  parameter `Pr : (R → Prop) → β` (intended as the uniform probability
  on `R`) and an abstract comparison relation `le : β → β → Prop`.
- Deterministic encodings are available via `detToEncoding` (see
  `Def05`).
-/

namespace TopSingleLayer

/- A two-stage adversary for the TCR game over message space `M` and
seed space `R`. The internal state is modeled implicitly by allowing the
second-stage function to close over the first-stage randomness. The
field `time` is an abstract running-time measure used in the security
statement. -/
structure TCRAdversary (M R : Type) : Type where
  /-- First stage: outputs a target message. -/
  choose : M
  /-- Second stage: given a seed `r`, outputs a new message and seed. -/
  respond : R → M × R
  /-- An abstract runtime cost used to state `time ≤ t`. -/
  time : Nat

/-- Success predicate of the TCR game for a fixed seed `r : R`.
The adversary succeeds if it outputs a distinct message `m* ≠ m` such
that `f(m,r) = f(m*,r*)`. -/
def tcrSuccess {w v : Nat} {M R : Type}
    (f : encodingFunction w v M R)
    (A : TCRAdversary M R) (r : R) : Prop :=
  let m  := A.choose
  let mr' := A.respond r
  let m'  := mr'.fst
  let r'  := mr'.snd
  f (m, r) = f (m', r') ∧ m' ≠ m

/-- Target-collision advantage, abstractly measured by a functional
`Pr` that maps predicates over `R` to some ordered codomain `β`.
Intended interpretation: `Pr S` is the probability (under uniform `R`)
that `S r` holds. -/
def tcrAdvantage {w v : Nat} {M R : Type} {β : Type}
    (f : encodingFunction w v M R)
    (A : TCRAdversary M R)
  (Pr : (R → Prop) → β) : β :=
  Pr (tcrSuccess f A)

/-- ε-security with respect to Target Collision Resistance (TCR).
For every time bound `t` and adversary `A` with `A.time ≤ t`, the
target-collision advantage is at most `ε t`. The probability operator
`Pr` is intended to be uniform sampling over `R`. -/
def tcrSecure {w v : Nat} {M R : Type} {β : Type}
    (f : encodingFunction w v M R)
    (ε : Nat → β)
    (Pr : (R → Prop) → β)
    (le : β → β → Prop) : Prop :=
  ∀ (t : Nat) (A : TCRAdversary M R), A.time ≤ t →
    le (tcrAdvantage (w:=w) (v:=v) f A Pr) (ε t)

/-!
## Example instantiation: uniform counting on finite `R`

For finite seed spaces `R`, one common concrete choice is to measure the
success set by its cardinality (uniform counting). This yields a
`Nat`-valued advantage. If you prefer probabilities in `[0,1]`, you can
compare counts to `ε(t) * |R|` externally.
-/

namespace Examples

open Classical

/-- Uniform counting functional on a finite seed space `R`.
Given a predicate `p : R → Prop`, returns `|{ r ∈ R | p r }|`. -/
noncomputable def uniformCountPr {R : Type} [Fintype R] (p : R → Prop) : Nat := by
  classical
  letI := Classical.decPred p
  exact (Finset.univ.filter (fun r => p r)).card

/-- `Nat`-valued TCR advantage using uniform counting over `R`. -/
noncomputable def tcrAdvantageCount {w v : Nat} {M R : Type} [Fintype R]
    (f : encodingFunction w v M R)
    (A : TCRAdversary M R) : Nat :=
  tcrAdvantage (β := Nat) f A (uniformCountPr)

/-- `Nat`-valued ε-security: bounds the number of successful seeds. -/
def tcrSecureCount {w v : Nat} {M R : Type} [Fintype R]
    (f : encodingFunction w v M R)
    (ε : Nat → Nat) : Prop :=
  tcrSecure (β := Nat) f ε (uniformCountPr) (· ≤ ·)

end Examples

end TopSingleLayer
