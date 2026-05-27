import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Token

/-!
# Vault: virtual offsets

The working vault. Same shape as `VaultNaive.lean`, but with small
strictly-positive constants — `vT` (virtual tokens) and `vA` (virtual
assets) — added as **offsets** to the conversion formulas:

    vaultTokenFor s d  = d * (T + vT) / (B + vA)             -- floor
    assetFor s k       = k * (B + vA) / (T + vT)             -- floor
    mintCost s k       = ⌈k * (B + vA) / (T + vT)⌉           -- ceil
    withdrawCost s d   = ⌈d * (T + vT) / (B + vA)⌉           -- ceil

where `T = vaultToken.totalSupply` and `B = vaultAssets s`. Because
`T + vT > 0` and `B + vA > 0` unconditionally, the empty-vault `T = 0`
fallback that broke the naive model is unreachable.

## How to read this file

The state, the conversion formulas, the operations, the `Action` /
`step` definitions, and the `VaultTokenPriceLE` definition are the
parts worth reading. The two headline theorem *statements* live at
the very bottom:

* `step_preserves_VaultTokenPriceLE` — every non-`loss` action
  preserves the vault-token price.
* `loss_decreases_VaultTokenPriceLE` — `loss` is the only action that
  can violate it (and, with a positive amount, always does).

Everything in the "## Helper lemmas — skip on a first read" section
in the middle is technical proof machinery — bounds, extraction
lemmas, per-operation preservation lemmas — that the headline
theorems are built on. You don't need to read any of it.
-/

namespace ERC4626

abbrev Addr := ERC20.Addr

/-! ## Axioms: virtual offsets and the vault address

Both offsets and the vault's own address are abstract — any concrete
deployment instantiates them. The strict-positivity axioms are the
load-bearing facts that rule out the naive `T = 0` edge case. -/

axiom virtualAssets : ℕ
axiom virtualTokens : ℕ
axiom virtualAssets_pos : 0 < virtualAssets
axiom virtualTokens_pos : 0 < virtualTokens

/-- The vault contract's own address (the escrow). -/
axiom vault : ERC20.Addr

/-! ## State -/

/-- The vault state: the vault's own token plus the underlying asset
token. The vault's escrowed asset holding is read straight off the
asset token's ledger (`vaultAssets` below); no separate
`totalAssets` field. -/
structure State where
  vaultToken : ERC20.State
  assetToken : ERC20.State

/-- The vault's escrowed asset holding. -/
noncomputable def vaultAssets (s : State) : ℕ := s.assetToken.balances vault

/-! ## Conversion formulas

Every formula offsets both numerator and denominator with `vT`/`vA`.
With both strictly positive, the divisions never hit zero. -/

/-- Ceiling division. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

/-- Vault tokens issued for `assets` deposited. -/
noncomputable def vaultTokenFor (s : State) (assets : ℕ) : ℕ :=
  assets * (s.vaultToken.totalSupply + virtualTokens)
    / (vaultAssets s + virtualAssets)

/-- Assets paid out for `tokens` redeemed. -/
noncomputable def assetFor (s : State) (tokens : ℕ) : ℕ :=
  tokens * (vaultAssets s + virtualAssets)
    / (s.vaultToken.totalSupply + virtualTokens)

/-- Asset cost to mint `tokens` vault tokens (rounded up). -/
noncomputable def mintCost (s : State) (tokens : ℕ) : ℕ :=
  ceilDiv (tokens * (vaultAssets s + virtualAssets))
          (s.vaultToken.totalSupply + virtualTokens)

/-- Vault tokens burnt to withdraw `assets` (rounded up). -/
noncomputable def withdrawCost (s : State) (assets : ℕ) : ℕ :=
  ceilDiv (assets * (s.vaultToken.totalSupply + virtualTokens))
          (vaultAssets s + virtualAssets)

/-! ## Operations

Four user operations (`deposit`, `mint`, `withdraw`, `redeem`) plus
two external events: `profit` for asset transfers *into* the vault
without minting vault tokens (yield, donation, accidental transfer)
and `loss` for transfers *out* without burning (strategy loss,
bad debt).

Entry operations (`deposit`, `mint`) reject `user = vault`: a vault
self-deposit would be balance-neutral on the asset side while still
minting vault tokens, breaking price preservation. Real ERC-4626
contracts have the same restriction implicitly via `msg.sender`. -/

/-- Deposit `assets` and receive vault tokens. Returns the new state
together with the number of vault tokens minted (= `vaultTokenFor s
assets`). -/
noncomputable def deposit (s : State) (user : Addr) (assets : ℕ) :
    Option (State × ℕ) :=
  if user = vault then none
  else
    match ERC20.transferFrom s.assetToken user vault assets with
    | none => none
    | some assetToken' =>
      some
        ({ vaultToken := ERC20.mint s.vaultToken user (vaultTokenFor s assets),
           assetToken := assetToken' },
         vaultTokenFor s assets)

/-- Mint `tokens` vault tokens and pay the required assets. Returns
the new state together with the asset cost (= `mintCost s tokens`). -/
noncomputable def mint (s : State) (user : Addr) (tokens : ℕ) :
    Option (State × ℕ) :=
  if user = vault then none
  else
    match ERC20.transferFrom s.assetToken user vault (mintCost s tokens) with
    | none => none
    | some assetToken' =>
      some
        ({ vaultToken := ERC20.mint s.vaultToken user tokens,
           assetToken := assetToken' },
         mintCost s tokens)

/-- Redeem `tokens` vault tokens for assets. Returns the new state
together with the assets paid out (= `assetFor s tokens`). -/
noncomputable def redeem (s : State) (user : Addr) (tokens : ℕ) :
    Option (State × ℕ) :=
  match ERC20.burn s.vaultToken user tokens with
  | none => none
  | some vaultToken' =>
    match ERC20.transferFrom s.assetToken vault user (assetFor s tokens) with
    | none => none
    | some assetToken' =>
      some ({ vaultToken := vaultToken', assetToken := assetToken' },
            assetFor s tokens)

/-- Withdraw `assets` by burning the required vault tokens. Returns
the new state together with the vault tokens burnt
(= `withdrawCost s assets`). -/
noncomputable def withdraw (s : State) (user : Addr) (assets : ℕ) :
    Option (State × ℕ) :=
  match ERC20.burn s.vaultToken user (withdrawCost s assets) with
  | none => none
  | some vaultToken' =>
    match ERC20.transferFrom s.assetToken vault user assets with
    | none => none
    | some assetToken' =>
      some ({ vaultToken := vaultToken', assetToken := assetToken' },
            withdrawCost s assets)

/-- Asset tokens flow *into* the vault without minting vault tokens.
Yield, donation, or accidental transfer all look the same to the
vault — we model this as a direct mint into the vault's asset
balance, rather than tracking a source address. A modeling
simplification that keeps the state machine focused on the
accounting that matters for vault-token pricing. -/
noncomputable def profit (s : State) (amount : ℕ) : State :=
  { s with assetToken := ERC20.mint s.assetToken vault amount }

/-- Asset tokens flow *out* of the vault without burning vault tokens
— a strategy loss, bad debt, or any other write-off. The only action
that can decrease the vault-token price. Modeled as a direct burn
from the vault's asset balance, for the same simplification reason
as `profit`. Fails when the vault doesn't hold enough assets. -/
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

/-- `a.noLoss` is the predicate that holds for every action except
`loss`. The headline preservation theorem is stated under this
precondition. -/
def Action.noLoss : Action → Prop
  | .loss _ => False
  | _       => True

noncomputable def step (a : Action) (s : State) : Option State :=
  match a with
  | .deposit u amt   => (deposit s u amt).map Prod.fst
  | .mint u tk       => (mint s u tk).map Prod.fst
  | .withdraw u amt  => (withdraw s u amt).map Prod.fst
  | .redeem u tk     => (redeem s u tk).map Prod.fst
  | .profit amt      => some (profit s amt)
  | .loss amt        => loss s amt

/-! ## Vault-token price

`VaultTokenPriceLE s s'` says the vault-token price did not decrease
from `s` to `s'`. Reading the price as `(B + vA) / (T + vT)`, that
is `pre_price ≤ post_price`; written without division (to stay in
`ℕ`) as cross-multiplication:

    (B + vA) (T' + vT) ≤ (B' + vA) (T + vT).
-/

def VaultTokenPriceLE (s s' : State) : Prop :=
  (vaultAssets s + virtualAssets) * (s'.vaultToken.totalSupply + virtualTokens)
  ≤ (vaultAssets s' + virtualAssets) * (s.vaultToken.totalSupply + virtualTokens)

theorem VaultTokenPriceLE.refl (s : State) : VaultTokenPriceLE s s := Nat.le_refl _

/-! ## Helper lemmas — skip on a first read

Everything below up to the "Headline theorems" section is technical
proof machinery: a ceiling-division bound, the four conversion-formula
bounds, per-operation extraction lemmas, and per-operation
preservation lemmas. None of it is reader-facing. Scroll to
"Headline theorems" at the bottom for the parts that matter. -/

lemma ceilDiv_mul_ge (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  rw [Nat.mul_comm]
  have h := Nat.div_add_mod (a + b - 1) b
  have hlt : (a + b - 1) % b < b := Nat.mod_lt _ hb
  omega

private lemma vaultTokenFor_bound (s : State) (d : ℕ) :
    vaultTokenFor s d * (vaultAssets s + virtualAssets)
    ≤ d * (s.vaultToken.totalSupply + virtualTokens) := by
  unfold vaultTokenFor
  exact Nat.div_mul_le_self _ _

private lemma assetFor_bound (s : State) (k : ℕ) :
    assetFor s k * (s.vaultToken.totalSupply + virtualTokens)
    ≤ k * (vaultAssets s + virtualAssets) := by
  unfold assetFor
  exact Nat.div_mul_le_self _ _

private lemma mintCost_bound (s : State) (k : ℕ) :
    k * (vaultAssets s + virtualAssets)
    ≤ mintCost s k * (s.vaultToken.totalSupply + virtualTokens) := by
  unfold mintCost
  exact ceilDiv_mul_ge _ (by have := virtualTokens_pos; omega)

private lemma withdrawCost_bound (s : State) (d : ℕ) :
    d * (s.vaultToken.totalSupply + virtualTokens)
    ≤ withdrawCost s d * (vaultAssets s + virtualAssets) := by
  unfold withdrawCost
  exact ceilDiv_mul_ge _ (by have := virtualAssets_pos; omega)

private lemma deposit_extract {s s' : State} {user : Addr} {d k : ℕ}
    (hd : deposit s user d = some (s', k)) :
    user ≠ vault ∧
    k = vaultTokenFor s d ∧
    s'.vaultToken.totalSupply = s.vaultToken.totalSupply + k ∧
    vaultAssets s' = vaultAssets s + d := by
  unfold deposit at hd
  split at hd
  · simp at hd
  case _ huv =>
    split at hd
    · simp at hd
    case _ assetToken' htransferFrom =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hs', hk⟩ := hd
      subst hs'
      refine ⟨huv, hk.symm, ?_, ?_⟩
      · show s.vaultToken.totalSupply + vaultTokenFor s d
              = s.vaultToken.totalSupply + k
        rw [hk]
      · show assetToken'.balances vault = s.assetToken.balances vault + d
        exact ERC20.transferFrom_balances_receiver huv htransferFrom

private lemma mint_extract {s s' : State} {user : Addr} {k d : ℕ}
    (hm : mint s user k = some (s', d)) :
    user ≠ vault ∧
    d = mintCost s k ∧
    s'.vaultToken.totalSupply = s.vaultToken.totalSupply + k ∧
    vaultAssets s' = vaultAssets s + d := by
  unfold mint at hm
  split at hm
  · simp at hm
  case _ huv =>
    split at hm
    · simp at hm
    case _ assetToken' htransferFrom =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨hs', hd⟩ := hm
      subst hs'
      refine ⟨huv, hd.symm, rfl, ?_⟩
      show assetToken'.balances vault = s.assetToken.balances vault + d
      have := ERC20.transferFrom_balances_receiver huv htransferFrom
      rw [hd] at this
      exact this

private lemma redeem_extract {s s' : State} {user : Addr} {k a : ℕ}
    (hr : redeem s user k = some (s', a)) :
    a = assetFor s k ∧
    k ≤ s.vaultToken.balances user ∧
    s'.vaultToken.totalSupply = s.vaultToken.totalSupply - k ∧
    (user = vault ∧ vaultAssets s' = vaultAssets s
     ∨ user ≠ vault ∧ vaultAssets s' = vaultAssets s - a) := by
  unfold redeem at hr
  split at hr
  · simp at hr
  case _ vaultToken' hburn =>
    split at hr
    · simp at hr
    case _ assetToken' htransferFrom =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨hs', ha⟩ := hr
      subst hs'
      have hkbal : k ≤ s.vaultToken.balances user := by
        unfold ERC20.burn at hburn
        split at hburn
        · simp at hburn
        · next h => simp only [not_lt] at h; exact h
      have hsup : vaultToken'.totalSupply = s.vaultToken.totalSupply - k := by
        unfold ERC20.burn at hburn
        split at hburn
        · simp at hburn
        · simp only [Option.some.injEq] at hburn; rw [← hburn]
      refine ⟨ha.symm, hkbal, hsup, ?_⟩
      by_cases huv : user = vault
      · left
        refine ⟨huv, ?_⟩
        show assetToken'.balances vault = s.assetToken.balances vault
        subst huv
        exact ERC20.transferFrom_self_balances htransferFrom vault
      · right
        refine ⟨huv, ?_⟩
        show assetToken'.balances vault = s.assetToken.balances vault - a
        have h := ERC20.transferFrom_balances_sender_eq (Ne.symm huv) htransferFrom
        rw [ha] at h
        exact h

private lemma withdraw_extract {s s' : State} {user : Addr} {d k : ℕ}
    (hw : withdraw s user d = some (s', k)) :
    k = withdrawCost s d ∧
    k ≤ s.vaultToken.balances user ∧
    s'.vaultToken.totalSupply = s.vaultToken.totalSupply - k ∧
    (user = vault ∧ vaultAssets s' = vaultAssets s
     ∨ user ≠ vault ∧ vaultAssets s' = vaultAssets s - d) := by
  unfold withdraw at hw
  split at hw
  · simp at hw
  case _ vaultToken' hburn =>
    split at hw
    · simp at hw
    case _ assetToken' htransferFrom =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hw
      obtain ⟨hs', hk⟩ := hw
      subst hs'
      have hkbal : withdrawCost s d ≤ s.vaultToken.balances user := by
        unfold ERC20.burn at hburn
        split at hburn
        · simp at hburn
        · next h => simp only [not_lt] at h; exact h
      have hsup : vaultToken'.totalSupply
                = s.vaultToken.totalSupply - withdrawCost s d := by
        unfold ERC20.burn at hburn
        split at hburn
        · simp at hburn
        · simp only [Option.some.injEq] at hburn; rw [← hburn]
      refine ⟨hk.symm, ?_, ?_, ?_⟩
      · rw [← hk]; exact hkbal
      · rw [← hk]; exact hsup
      · by_cases huv : user = vault
        · left
          refine ⟨huv, ?_⟩
          show assetToken'.balances vault = s.assetToken.balances vault
          subst huv
          exact ERC20.transferFrom_self_balances htransferFrom vault
        · right
          refine ⟨huv, ?_⟩
          show assetToken'.balances vault = s.assetToken.balances vault - d
          exact ERC20.transferFrom_balances_sender_eq (Ne.symm huv) htransferFrom

private lemma profit_extract (s : State) (d : ℕ) :
    (profit s d).vaultToken = s.vaultToken ∧
    vaultAssets (profit s d) = vaultAssets s + d := by
  refine ⟨rfl, ?_⟩
  show (ERC20.mint s.assetToken vault d).balances vault
       = s.assetToken.balances vault + d
  unfold ERC20.mint
  simp [Finsupp.add_apply, Finsupp.single_eq_same]

private lemma burn_total_le {s : ERC20.State} (h : ERC20.Invariant s) (u : ERC20.Addr) :
    s.balances u ≤ s.totalSupply := by
  unfold ERC20.Invariant ERC20.sumBalances at h
  rw [h]
  have he := Finsupp.sum_update_add s.balances u 0 (fun _ b => b)
    (fun _ => rfl) (fun _ _ _ => rfl)
  dsimp only at he
  omega

private lemma deposit_preserves_VaultTokenPriceLE
    {s s' : State} {user : Addr} {d k : ℕ}
    (hd : deposit s user d = some (s', k)) :
    VaultTokenPriceLE s s' := by
  obtain ⟨_, hk, htT, htA⟩ := deposit_extract hd
  unfold VaultTokenPriceLE
  set B := vaultAssets s
  set T := s.vaultToken.totalSupply
  rw [htT, htA]
  have hbound : k * (B + virtualAssets) ≤ d * (T + virtualTokens) := by
    rw [hk]; exact vaultTokenFor_bound s d
  have el :
      (B + virtualAssets) * (T + k + virtualTokens)
      = (B + virtualAssets) * (T + virtualTokens)
      + (B + virtualAssets) * k := by ring
  have er :
      (B + d + virtualAssets) * (T + virtualTokens)
      = (B + virtualAssets) * (T + virtualTokens)
      + d * (T + virtualTokens) := by ring
  have hcomm : (B + virtualAssets) * k = k * (B + virtualAssets) := by ring
  omega

private lemma mint_preserves_VaultTokenPriceLE
    {s s' : State} {user : Addr} {k d : ℕ}
    (hm : mint s user k = some (s', d)) :
    VaultTokenPriceLE s s' := by
  obtain ⟨_, hd, htT, htA⟩ := mint_extract hm
  unfold VaultTokenPriceLE
  set B := vaultAssets s
  set T := s.vaultToken.totalSupply
  rw [htT, htA]
  have hbound : k * (B + virtualAssets) ≤ d * (T + virtualTokens) := by
    rw [hd]; exact mintCost_bound s k
  have el :
      (B + virtualAssets) * (T + k + virtualTokens)
      = (B + virtualAssets) * (T + virtualTokens)
      + (B + virtualAssets) * k := by ring
  have er :
      (B + d + virtualAssets) * (T + virtualTokens)
      = (B + virtualAssets) * (T + virtualTokens)
      + d * (T + virtualTokens) := by ring
  have hcomm : (B + virtualAssets) * k = k * (B + virtualAssets) := by ring
  omega

private lemma redeem_preserves_VaultTokenPriceLE
    {s s' : State} {user : Addr} {k a : ℕ}
    (hvt : ERC20.Invariant s.vaultToken)
    (hr : redeem s user k = some (s', a)) :
    VaultTokenPriceLE s s' := by
  obtain ⟨ha, hkbal, htT, hcase⟩ := redeem_extract hr
  have hkT : k ≤ s.vaultToken.totalSupply :=
    le_trans hkbal (burn_total_le hvt user)
  unfold VaultTokenPriceLE
  set B := vaultAssets s
  set T := s.vaultToken.totalSupply
  rw [htT]
  rcases hcase with ⟨_, hVA⟩ | ⟨_, hVA⟩
  · rw [hVA]
    have : T - k + virtualTokens ≤ T + virtualTokens := by omega
    exact Nat.mul_le_mul_left _ this
  · rw [hVA]
    have hbound : a * (T + virtualTokens) ≤ k * (B + virtualAssets) := by
      rw [ha]; exact assetFor_bound s k
    have hassets : a ≤ B := by
      unfold redeem at hr
      split at hr
      · simp at hr
      case _ vaultToken' _ =>
        split at hr
        · simp at hr
        case _ assetToken' htr =>
          unfold ERC20.transferFrom at htr
          split at htr
          · simp at htr
          · next h =>
            simp only [not_lt] at h
            -- `h : assetFor s k ≤ s.assetToken.balances vault = B`.
            rw [ha]; exact h
    have el :
        (B + virtualAssets) * (T - k + virtualTokens)
        + (B + virtualAssets) * k
        = (B + virtualAssets) * (T + virtualTokens) := by
      rw [← Nat.mul_add]
      have : T - k + virtualTokens + k = T + virtualTokens := by omega
      rw [this]
    have er :
        (B - a + virtualAssets) * (T + virtualTokens)
        + a * (T + virtualTokens)
        = (B + virtualAssets) * (T + virtualTokens) := by
      rw [← Nat.add_mul]
      have : B - a + virtualAssets + a = B + virtualAssets := by omega
      rw [this]
    have hcomm : (B + virtualAssets) * k = k * (B + virtualAssets) := by ring
    omega

private lemma withdraw_preserves_VaultTokenPriceLE
    {s s' : State} {user : Addr} {d k : ℕ}
    (hvt : ERC20.Invariant s.vaultToken)
    (hw : withdraw s user d = some (s', k)) :
    VaultTokenPriceLE s s' := by
  obtain ⟨hk, hkbal, htT, hcase⟩ := withdraw_extract hw
  have hkT : k ≤ s.vaultToken.totalSupply :=
    le_trans hkbal (burn_total_le hvt user)
  unfold VaultTokenPriceLE
  set B := vaultAssets s
  set T := s.vaultToken.totalSupply
  rw [htT]
  rcases hcase with ⟨_, hVA⟩ | ⟨_, hVA⟩
  · rw [hVA]
    have : T - k + virtualTokens ≤ T + virtualTokens := by omega
    exact Nat.mul_le_mul_left _ this
  · rw [hVA]
    have hbound : d * (T + virtualTokens) ≤ k * (B + virtualAssets) := by
      rw [hk]; exact withdrawCost_bound s d
    have hassets : d ≤ B := by
      unfold withdraw at hw
      split at hw
      · simp at hw
      case _ vaultToken' _ =>
        split at hw
        · simp at hw
        case _ assetToken' htr =>
          unfold ERC20.transferFrom at htr
          split at htr
          · simp at htr
          · next h => simp only [not_lt] at h; exact h
    have el :
        (B + virtualAssets) * (T - k + virtualTokens)
        + (B + virtualAssets) * k
        = (B + virtualAssets) * (T + virtualTokens) := by
      rw [← Nat.mul_add]
      have : T - k + virtualTokens + k = T + virtualTokens := by omega
      rw [this]
    have er :
        (B - d + virtualAssets) * (T + virtualTokens)
        + d * (T + virtualTokens)
        = (B + virtualAssets) * (T + virtualTokens) := by
      rw [← Nat.add_mul]
      have : B - d + virtualAssets + d = B + virtualAssets := by omega
      rw [this]
    have hcomm : (B + virtualAssets) * k = k * (B + virtualAssets) := by ring
    omega

private lemma profit_preserves_VaultTokenPriceLE (s : State) (d : ℕ) :
    VaultTokenPriceLE s (profit s d) := by
  obtain ⟨hvt, hVA⟩ := profit_extract s d
  unfold VaultTokenPriceLE
  rw [show (profit s d).vaultToken.totalSupply = s.vaultToken.totalSupply
        from by rw [hvt], hVA]
  apply Nat.mul_le_mul_right
  omega

/-! ## Headline theorems -/

/-- Every action other than `loss` preserves the vault-token price.
The post-condition holds under the `vaultToken` ledger invariant so
that `redeem` and `withdraw` (which burn vault tokens) cannot
underflow their accounting. -/
theorem step_preserves_VaultTokenPriceLE
    {a : Action} {s s' : State}
    (hnl : a.noLoss)
    (hvt : ERC20.Invariant s.vaultToken)
    (hstep : step a s = some s') :
    VaultTokenPriceLE s s' := by
  cases a with
  | deposit u amt   =>
    change (deposit s u amt).map Prod.fst = some s' at hstep
    rw [Option.map_eq_some_iff] at hstep
    obtain ⟨⟨_, _⟩, hd, heq⟩ := hstep
    cases heq
    exact deposit_preserves_VaultTokenPriceLE hd
  | mint u tk       =>
    change (mint s u tk).map Prod.fst = some s' at hstep
    rw [Option.map_eq_some_iff] at hstep
    obtain ⟨⟨_, _⟩, hm, heq⟩ := hstep
    cases heq
    exact mint_preserves_VaultTokenPriceLE hm
  | withdraw u amt  =>
    change (withdraw s u amt).map Prod.fst = some s' at hstep
    rw [Option.map_eq_some_iff] at hstep
    obtain ⟨⟨_, _⟩, hw, heq⟩ := hstep
    cases heq
    exact withdraw_preserves_VaultTokenPriceLE hvt hw
  | redeem u tk     =>
    change (redeem s u tk).map Prod.fst = some s' at hstep
    rw [Option.map_eq_some_iff] at hstep
    obtain ⟨⟨_, _⟩, hr, heq⟩ := hstep
    cases heq
    exact redeem_preserves_VaultTokenPriceLE hvt hr
  | profit amt      =>
    simp only [step, Option.some.injEq] at hstep
    subst hstep
    exact profit_preserves_VaultTokenPriceLE s amt
  | loss amt        =>
    exact absurd hnl (by simp [Action.noLoss])

/-- A `loss` of a positive amount strictly decreases the vault-token
price — confirming that `loss` is the only action that can violate
`VaultTokenPriceLE`, and that it always does. -/
theorem loss_decreases_VaultTokenPriceLE
    {s s' : State} {amount : ℕ}
    (hamt : 0 < amount)
    (hl : loss s amount = some s') :
    ¬ VaultTokenPriceLE s s' := by
  unfold loss at hl
  split at hl
  · simp at hl
  case _ assetToken' hburn =>
    simp only [Option.some.injEq] at hl
    subst hl
    -- Read off the burn's effect on the vault's asset balance.
    have hle : amount ≤ s.assetToken.balances vault := by
      unfold ERC20.burn at hburn
      split at hburn
      · simp at hburn
      · next h => simp only [not_lt] at h; exact h
    have hB' : assetToken'.balances vault = s.assetToken.balances vault - amount := by
      unfold ERC20.burn at hburn
      split at hburn
      · simp at hburn
      · simp only [Option.some.injEq] at hburn
        rw [← hburn]
        simp [Finsupp.update_apply]
    intro hLE
    unfold VaultTokenPriceLE at hLE
    change (s.assetToken.balances vault + virtualAssets)
              * (s.vaultToken.totalSupply + virtualTokens)
            ≤ (assetToken'.balances vault + virtualAssets)
              * (s.vaultToken.totalSupply + virtualTokens) at hLE
    rw [hB'] at hLE
    have hT : 0 < s.vaultToken.totalSupply + virtualTokens := by
      have := virtualTokens_pos; omega
    have := Nat.le_of_mul_le_mul_right hLE hT
    omega

end ERC4626
