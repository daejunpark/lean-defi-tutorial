import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Token

/-!
# Vault (naive): the version that breaks

A first attempt at a vault model. Same shape as `Vault.lean`, but the
conversion formulas use the textbook `T = 0 → 1:1` fallback when the
vault is empty.

That fallback is the entire story of this file. It's fine for the
very first depositor, but the vault can also reach an **orphan-asset
state** where `T = 0` and `B > 0` — a withdrawal that ceiling-rounds
the burnt vault tokens to zero while leaving residual assets behind.
From that state, the same 1:1 fallback resets the vault-token price
from "infinite" to a finite ratio. That is exactly a vault-token-price
*decrease*, violating `VaultTokenPriceLE`.

This is the algebraic defect behind the classic donation-style
inflation attack. The fix — adding strictly positive virtual offsets
so `T + vT > 0` and `B + vA > 0` unconditionally — lives in
`Vault.lean`.

## How to read this file

The state, the conversion formulas (with the bad `T = 0` branch
spelled out), the operations, and the two headline theorem
*statements* — `withdraw_can_create_orphan` and
`deposit_orphan_violates_VaultTokenPriceLE` — are the parts worth
reading. Their proof bodies are technical; safe to skip.

## Counter-example trace

From the empty state with Alice holding 8 asset tokens, the four-step
trace

    deposit (alice, 7) → profit 1 → withdraw (alice, 7) → deposit (alice, 5)

walks through:

| step                        | vault balance `B` | vault-token supply `T` |
|-----------------------------|-------------------|------------------------|
| initial                     | 0                 | 0                      |
| after `deposit (alice, 7)`  | 7                 | 7                      |
| after `profit  1`           | 8                 | 7                      |
| after `withdraw(alice, 7)`  | 1                 | 0   ← orphan!          |
| after `deposit (alice, 5)`  | 6                 | 5                      |

The last step violates `VaultTokenPriceLE`: the orphan state has
"infinite" vault-token price (`B/T = 1/0`), and the fresh deposit
drops it to `6/5`. The two theorems below capture this in two parts:
the orphan state is reachable from a successful withdraw, and from
there `deposit` violates the price invariant.
-/

namespace ERC4626Naive

abbrev Addr := ERC20.Addr

/-- The vault contract's own address. Any concrete deployment fixes
it; everything below is independent of the choice. -/
axiom vault : Addr

/-! ## State

A vault token plus the asset token. The vault's escrowed asset
holding is read straight off the asset token's ledger (`vaultAssets`
below), so there is no separate `totalAssets` field. -/

structure State where
  vaultToken : ERC20.State
  assetToken : ERC20.State

/-- The vault's escrowed asset holding. -/
noncomputable def vaultAssets (s : State) : ℕ := s.assetToken.balances vault

/-! ## Conversion formulas — the naive `T = 0` fallback

These four functions convert between assets and vault tokens. Each
one checks `totalSupply = 0` and falls back to a 1:1 (or 0:0) rate.
That's fine for the very first depositor, but it's also what fires
again whenever the vault reaches the orphan state — overwriting the
price the vault's history implied. -/

/-- Vault tokens issued for `assets` deposited. -/
noncomputable def vaultTokenFor (s : State) (assets : ℕ) : ℕ :=
  if s.vaultToken.totalSupply = 0 then assets   -- empty vault: 1:1
  else assets * s.vaultToken.totalSupply / vaultAssets s

/-- Assets paid out for `tokens` redeemed. -/
noncomputable def assetFor (s : State) (tokens : ℕ) : ℕ :=
  if s.vaultToken.totalSupply = 0 then 0
  else tokens * vaultAssets s / s.vaultToken.totalSupply

/-- Asset cost to mint `tokens` vault tokens (rounded up). -/
noncomputable def mintCost (s : State) (tokens : ℕ) : ℕ :=
  if s.vaultToken.totalSupply = 0 then tokens
  else (tokens * vaultAssets s + s.vaultToken.totalSupply - 1)
       / s.vaultToken.totalSupply

/-- Vault tokens burnt to withdraw `assets` (rounded up). -/
noncomputable def withdrawCost (s : State) (assets : ℕ) : ℕ :=
  if s.vaultToken.totalSupply = 0 then assets
  else (assets * s.vaultToken.totalSupply + vaultAssets s - 1)
       / vaultAssets s

/-! ## Operations

Four user operations (`deposit`, `mint`, `withdraw`, `redeem`) plus
two external events: `profit` for asset balance growing (yield,
donation, accidental transfer — all modeled uniformly as a direct
mint into the vault's asset balance) and `loss` for asset balance
shrinking (strategy loss, bad debt — modeled as a direct burn).
Entry operations reject `user = vault`. -/

noncomputable def deposit (s : State) (user : Addr) (assets : ℕ) :
    Option State :=
  if user = vault then none
  else
    match ERC20.transferFrom s.assetToken user vault assets with
    | none => none
    | some assetToken' =>
      some
        { vaultToken := ERC20.mint s.vaultToken user (vaultTokenFor s assets),
          assetToken := assetToken' }

noncomputable def mint (s : State) (user : Addr) (tokens : ℕ) :
    Option State :=
  if user = vault then none
  else
    match ERC20.transferFrom s.assetToken user vault (mintCost s tokens) with
    | none => none
    | some assetToken' =>
      some
        { vaultToken := ERC20.mint s.vaultToken user tokens,
          assetToken := assetToken' }

noncomputable def redeem (s : State) (user : Addr) (tokens : ℕ) :
    Option State :=
  match ERC20.burn s.vaultToken user tokens with
  | none => none
  | some vaultToken' =>
    match ERC20.transferFrom s.assetToken vault user (assetFor s tokens) with
    | none => none
    | some assetToken' =>
      some { vaultToken := vaultToken', assetToken := assetToken' }

noncomputable def withdraw (s : State) (user : Addr) (assets : ℕ) :
    Option State :=
  match ERC20.burn s.vaultToken user (withdrawCost s assets) with
  | none => none
  | some vaultToken' =>
    match ERC20.transferFrom s.assetToken vault user assets with
    | none => none
    | some assetToken' =>
      some { vaultToken := vaultToken', assetToken := assetToken' }

/-- Asset balance grows: yield, donation, accidental transfer all
look the same. Modeled as a direct mint into the vault's asset
balance for simplicity. -/
noncomputable def profit (s : State) (amount : ℕ) : State :=
  { s with assetToken := ERC20.mint s.assetToken vault amount }

/-- Asset balance shrinks: strategy loss, bad debt, write-off.
Modeled as a direct burn from the vault's asset balance for the
same simplification reason as `profit`. -/
noncomputable def loss (s : State) (amount : ℕ) : Option State :=
  match ERC20.burn s.assetToken vault amount with
  | none => none
  | some assetToken' =>
    some { s with assetToken := assetToken' }

/-! ## Action and `step` -/

inductive Action where
  | deposit  (user : Addr) (amount : ℕ)
  | mint     (user : Addr) (tokens : ℕ)
  | withdraw (user : Addr) (amount : ℕ)
  | redeem   (user : Addr) (tokens : ℕ)
  | profit   (amount : ℕ)
  | loss     (amount : ℕ)

noncomputable def step (a : Action) (s : State) : Option State :=
  match a with
  | .deposit u amt  => deposit s u amt
  | .mint u tk      => mint s u tk
  | .withdraw u amt => withdraw s u amt
  | .redeem u tk    => redeem s u tk
  | .profit amt     => some (profit s amt)
  | .loss amt       => loss s amt

/-! ## Vault-token price

`VaultTokenPriceLE s s'` says the vault-token price did not decrease
from `s` to `s'`. Reading the price as `B / T`, that is `B / T ≤
B' / T'`; written without division (to stay in `ℕ`) as cross-
multiplication. -/

def VaultTokenPriceLE (s s' : State) : Prop :=
  vaultAssets s * s'.vaultToken.totalSupply
  ≤ vaultAssets s' * s.vaultToken.totalSupply

/-! ## The headline counter-example

A two-part demonstration that `step` does *not* preserve
`VaultTokenPriceLE`:

1. `withdraw_can_create_orphan` — a withdraw can land in the orphan
   state `(T = 0, B > 0)`.
2. `deposit_orphan_violates_VaultTokenPriceLE` — from any orphan
   state, a successful `deposit` of a positive amount breaks
   `VaultTokenPriceLE`.

The theorem *statements* below are the reader-facing content; the
proof bodies that follow each are technical and can be skipped. -/

/-- From any state with `T = 7` and `B = 8`, a successful
`withdraw (alice, 7)` lands in the orphan state `(T = 0, B = 1)`.
This is the concrete shape of step 3 in the trace at the top of the
file: `withdrawCost` evaluates to `⌈7·7 / 8⌉ = 7`, the seven vault
tokens burn down to zero, and the seven released assets leave one
behind. -/
theorem withdraw_can_create_orphan
    {s s' : State} {alice : Addr}
    (hT : s.vaultToken.totalSupply = 7)
    (hB : vaultAssets s = 8)
    (hAliceVault : alice ≠ vault)
    (hw : withdraw s alice 7 = some s') :
    s'.vaultToken.totalSupply = 0 ∧ 0 < vaultAssets s' := by
  unfold withdraw at hw
  -- The withdrawCost evaluates to `⌈7·7 / 8⌉ = 7`.
  have hcost : withdrawCost s 7 = 7 := by
    unfold withdrawCost
    rw [if_neg (by rw [hT]; decide), hT, hB]
  rw [hcost] at hw
  split at hw
  · simp at hw
  case _ vaultToken' hburn =>
    split at hw
    · simp at hw
    case _ assetToken' htr =>
      simp only [Option.some.injEq] at hw
      subst hw
      refine ⟨?_, ?_⟩
      · -- post-state totalSupply = 7 - 7 = 0
        show vaultToken'.totalSupply = 0
        unfold ERC20.burn at hburn
        split at hburn
        · simp at hburn
        · simp only [Option.some.injEq] at hburn
          rw [← hburn]
          show s.vaultToken.totalSupply - 7 = 0
          omega
      · -- post-state vault balance = 8 - 7 = 1 > 0
        show 0 < assetToken'.balances vault
        have h := ERC20.transferFrom_balances_sender_eq (Ne.symm hAliceVault) htr
        rw [h]
        show 0 < s.assetToken.balances vault - 7
        unfold vaultAssets at hB
        omega

/-- The headline result: from any orphan-asset state (`T = 0`,
`B > 0`), a successful `deposit` of a positive amount breaks
`VaultTokenPriceLE`.

This is the mathematical content of the inflation-attack
precondition. The orphan state has effectively infinite vault-token
price; the naive `vaultTokenFor` fallback fires (`vaultTokenFor s d
= d` regardless of `B`), so post-state `T' = d` while `B'` grows by
the full `d` — collapsing the price to a finite ratio. -/
theorem deposit_orphan_violates_VaultTokenPriceLE
    {s s' : State} {user : Addr} {d : ℕ}
    (h_T : s.vaultToken.totalSupply = 0)
    (h_B : 0 < vaultAssets s)
    (h_d : 0 < d)
    (hd : deposit s user d = some s') :
    ¬ VaultTokenPriceLE s s' := by
  unfold deposit at hd
  split at hd
  · simp at hd
  case _ huv =>
    split at hd
    · simp at hd
    case _ assetToken' htr =>
      simp only [Option.some.injEq] at hd
      subst hd
      -- `vaultTokenFor` falls back to the identity via the `T = 0` branch.
      have hk : vaultTokenFor s d = d := by
        unfold vaultTokenFor; rw [if_pos h_T]
      have hT' : (ERC20.mint s.vaultToken user d).totalSupply = d := by
        show s.vaultToken.totalSupply + d = d
        omega
      have hB' : assetToken'.balances vault = vaultAssets s + d :=
        ERC20.transferFrom_balances_receiver huv htr
      -- VaultTokenPriceLE would require `B · d ≤ (B + d) · 0 = 0`,
      -- contradicting `B · d > 0` from `B > 0, d > 0`.
      intro hLE
      unfold VaultTokenPriceLE at hLE
      rw [hk] at hLE
      change vaultAssets s * (ERC20.mint s.vaultToken user d).totalSupply
              ≤ vaultAssets ⟨ERC20.mint s.vaultToken user d, assetToken'⟩
                * s.vaultToken.totalSupply at hLE
      rw [hT', h_T] at hLE
      show False
      have : vaultAssets s * d > 0 := Nat.mul_pos h_B h_d
      simp at hLE
      omega

end ERC4626Naive
