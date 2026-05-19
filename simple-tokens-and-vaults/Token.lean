import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Order

/-!
# Token model

A minimal token contract: a balance map and a total-supply counter,
with three operations — `transferFrom`, `mint`, and `burn`.

The headline correctness property is the **ledger invariant**: total
supply equals the sum of all balances. We bundle the three operations
into a single `step` function and prove the invariant is preserved
by every action in one statement.

## How to read this file

The state, the three operations, the invariant, and the `Action` /
`step` definitions at the top are the reader-facing parts. The
single headline theorem statement — `step_preserves_invariant` —
lives at the very bottom.

Everything in between, in the "## Helper lemmas — skip on a first
read" section, is technical machinery: per-operation preservation
lemmas and balance-lookup lemmas used downstream by the vault model.
You don't need to read any of it.
-/

namespace ERC20

/-- Account addresses. -/
abbrev Addr := ℕ

/-! ## State

A balance map plus a separate total-supply counter. `→₀` is mathlib's
notation for a finitely-supported function — a function that is zero
on all but finitely many inputs, which is the natural model for a
balance map (most accounts hold nothing). -/

structure State where
  balances    : Addr →₀ ℕ
  totalSupply : ℕ

/-- The empty state: no balances, zero total supply. -/
def init : State where
  balances    := 0
  totalSupply := 0

/-- An account's current balance. -/
def balanceOf (s : State) (addr : Addr) : ℕ := s.balances addr

/-! ## Operations

Three operations: `transferFrom` and `burn` fail when the source has
insufficient balance; `mint` always succeeds. Failure is encoded as
`none` in `Option State` — no exceptions, no reverts, just the
post-state or its absence. -/

/-- Transfer `amount` tokens from `sender` to `receiver`. Fails if
the sender's balance is insufficient. -/
noncomputable def transferFrom (s : State) (sender receiver : Addr) (amount : ℕ) :
    Option State :=
  if s.balances sender < amount then none
  else
    let b := s.balances.update sender (s.balances sender - amount)
    some ⟨b.update receiver (b receiver + amount), s.totalSupply⟩

/-- Mint `amount` tokens to `recipient`. -/
noncomputable def mint (s : State) (recipient : Addr) (amount : ℕ) : State where
  balances    := s.balances + Finsupp.single recipient amount
  totalSupply := s.totalSupply + amount

/-- Burn `amount` tokens held by `holder`. Fails if the holder's
balance is insufficient. -/
noncomputable def burn (s : State) (holder : Addr) (amount : ℕ) : Option State :=
  if s.balances holder < amount then none
  else
    some ⟨s.balances.update holder (s.balances holder - amount),
          s.totalSupply - amount⟩

/-! ## Invariant

The headline correctness property: total supply equals the sum of all
balances. -/

/-- Sum of every account's balance. -/
noncomputable def sumBalances (s : State) : ℕ :=
  s.balances.sum fun _ v => v

/-- The fundamental ledger invariant. -/
def Invariant (s : State) : Prop :=
  s.totalSupply = sumBalances s

/-! ## Action and `step`

We bundle the three operations into a single `Action` enum and
dispatch them through `step : Action → State → Option State`. This
lets the headline theorem cover every operation in one statement. -/

inductive Action where
  | transferFrom (sender receiver : Addr) (amount : ℕ)
  | mint         (recipient : Addr) (amount : ℕ)
  | burn         (holder : Addr) (amount : ℕ)

noncomputable def step (a : Action) (s : State) : Option State :=
  match a with
  | .transferFrom u v amt => transferFrom s u v amt
  | .mint r amt           => some (mint s r amt)
  | .burn h amt           => burn s h amt

/-! ## Helper lemmas — skip on a first read

Two groups:

* The `transferFrom_balances_*` family describes exactly how
  `transferFrom` changes each account's balance — used downstream
  by the vault's price-monotonicity proof.
* The per-operation `*_preserves_invariant` lemmas show that each
  primitive preserves the ledger invariant. They feed
  `step_preserves_invariant` at the bottom of the file. -/

lemma transferFrom_balances_receiver {s s' : State} {sender receiver : Addr}
    {amount : ℕ} (h : sender ≠ receiver)
    (ht : transferFrom s sender receiver amount = some s') :
    s'.balances receiver = s.balances receiver + amount := by
  unfold transferFrom at ht
  split at ht
  · cases ht
  · simp only [Option.some.injEq] at ht
    subst ht
    simp [Finsupp.update_apply, Ne.symm h]

lemma transferFrom_balances_sender_ge {s s' : State} {sender receiver : Addr}
    {amount : ℕ} (ht : transferFrom s sender receiver amount = some s') :
    s.balances sender - amount ≤ s'.balances sender := by
  unfold transferFrom at ht
  split at ht
  · cases ht
  · next hcond =>
    simp only [not_lt] at hcond
    simp only [Option.some.injEq] at ht
    subst ht
    by_cases h : sender = receiver
    · subst h
      simp [Finsupp.update_apply]
    · rw [Finsupp.update_apply, if_neg h,
          Finsupp.update_apply, if_pos rfl]

lemma transferFrom_balances_sender_eq {s s' : State} {sender receiver : Addr}
    {amount : ℕ} (h : sender ≠ receiver)
    (ht : transferFrom s sender receiver amount = some s') :
    s'.balances sender = s.balances sender - amount := by
  unfold transferFrom at ht
  split at ht
  · cases ht
  · simp only [Option.some.injEq] at ht
    subst ht
    rw [Finsupp.update_apply, if_neg h, Finsupp.update_apply, if_pos rfl]

lemma transferFrom_balances_other {s s' : State} {sender receiver : Addr}
    {amount : ℕ} {u : Addr} (hu_s : u ≠ sender) (hu_r : u ≠ receiver)
    (ht : transferFrom s sender receiver amount = some s') :
    s'.balances u = s.balances u := by
  unfold transferFrom at ht
  split at ht
  · cases ht
  · simp only [Option.some.injEq] at ht
    subst ht
    rw [Finsupp.update_apply, if_neg hu_r, Finsupp.update_apply, if_neg hu_s]

lemma transferFrom_preserves_totalSupply {s s' : State} {sender receiver : Addr}
    {amount : ℕ} (ht : transferFrom s sender receiver amount = some s') :
    s'.totalSupply = s.totalSupply := by
  unfold transferFrom at ht
  split at ht
  · cases ht
  · simp only [Option.some.injEq] at ht; subst ht; rfl

/-- A self-transfer (`sender = receiver`) leaves every balance
unchanged. -/
lemma transferFrom_self_balances {s s' : State} {addr : Addr} {amount : ℕ}
    (ht : transferFrom s addr addr amount = some s') (u : Addr) :
    s'.balances u = s.balances u := by
  unfold transferFrom at ht
  split at ht
  · cases ht
  · next hcond =>
    simp only [not_lt] at hcond
    simp only [Option.some.injEq] at ht
    subst ht
    by_cases hu : u = addr
    · subst hu
      rw [Finsupp.update_apply, if_pos rfl, Finsupp.update_apply, if_pos rfl]
      omega
    · rw [Finsupp.update_apply, if_neg hu, Finsupp.update_apply, if_neg hu]

/-- The empty state satisfies the invariant. -/
lemma init_invariant : Invariant init := by
  simp [Invariant, init, sumBalances]

/-- `transferFrom` preserves the invariant. -/
lemma transferFrom_preserves_invariant {s s' : State}
    {sender receiver : Addr} {amount : ℕ}
    (h : Invariant s) (ht : transferFrom s sender receiver amount = some s') :
    Invariant s' := by
  unfold transferFrom at ht
  split at ht
  · cases ht
  · next hcond =>
    simp only [not_lt] at hcond
    simp only [Option.some.injEq] at ht
    subst ht
    simp only [Invariant, sumBalances] at *
    have h2 := Finsupp.sum_update_add s.balances sender (s.balances sender - amount)
      (fun _ v => v) (fun _ => rfl) (fun _ _ _ => rfl)
    set b := s.balances.update sender (s.balances sender - amount)
    have h1 := Finsupp.sum_update_add b receiver (b receiver + amount)
      (fun _ v => v) (fun _ => rfl) (fun _ _ _ => rfl)
    dsimp only at h1 h2
    have hA : b.sum (fun _ v => v) + amount = s.balances.sum (fun _ v => v) := by
      have eq : b.sum (fun _ v => v) + amount + s.balances sender =
                s.balances.sum (fun _ v => v) + s.balances sender := by
        rw [Nat.add_right_comm, h2, Nat.add_assoc, Nat.sub_add_cancel hcond]
      exact Nat.add_right_cancel eq
    have hB : (b.update receiver (b receiver + amount)).sum (fun _ v => v) =
              b.sum (fun _ v => v) + amount := by
      have eq : (b.update receiver (b receiver + amount)).sum (fun _ v => v) + b receiver =
                b.sum (fun _ v => v) + amount + b receiver := by
        rw [h1, Nat.add_assoc, Nat.add_comm (b receiver) amount]
      exact Nat.add_right_cancel eq
    rw [hB, hA, h]

/-- `mint` preserves the invariant. -/
lemma mint_preserves_invariant {s : State} {recipient : Addr} {amount : ℕ}
    (h : Invariant s) : Invariant (mint s recipient amount) := by
  simp only [Invariant, mint, sumBalances] at *
  rw [Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl)]
  rw [Finsupp.sum_single_index rfl, h]

/-- `burn` preserves the invariant. -/
lemma burn_preserves_invariant {s s' : State} {holder : Addr} {amount : ℕ}
    (h : Invariant s) (hb : burn s holder amount = some s') :
    Invariant s' := by
  unfold burn at hb
  split at hb
  · cases hb
  · next hcond =>
    simp only [not_lt] at hcond
    simp only [Option.some.injEq] at hb
    subst hb
    simp only [Invariant, sumBalances] at *
    have h1 := Finsupp.sum_update_add s.balances holder (s.balances holder - amount)
      (fun _ v => v) (fun _ => rfl) (fun _ _ _ => rfl)
    dsimp only at h1
    have hA : (s.balances.update holder (s.balances holder - amount)).sum (fun _ v => v)
                + amount = s.balances.sum (fun _ v => v) := by
      have eq : (s.balances.update holder (s.balances holder - amount)).sum (fun _ v => v)
                  + amount + s.balances holder =
                s.balances.sum (fun _ v => v) + s.balances holder := by
        rw [Nat.add_right_comm, h1, Nat.add_assoc, Nat.sub_add_cancel hcond]
      exact Nat.add_right_cancel eq
    rw [h]; omega

/-! ## Headline theorem -/

/-- Every `Action` preserves the ledger invariant. -/
theorem step_preserves_invariant {a : Action} {s s' : State}
    (h : Invariant s) (hstep : step a s = some s') : Invariant s' := by
  cases a with
  | transferFrom u v amt =>
    simp only [step] at hstep
    exact transferFrom_preserves_invariant h hstep
  | mint r amt =>
    simp only [step, Option.some.injEq] at hstep
    subst hstep
    exact mint_preserves_invariant h
  | burn b amt =>
    simp only [step] at hstep
    exact burn_preserves_invariant h hstep

end ERC20
