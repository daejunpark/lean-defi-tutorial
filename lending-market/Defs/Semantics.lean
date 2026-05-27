import Util.CeilDiv
import Defs.States

/-!
# Lending Market — Computational semantics

State-derived view functions, the per-user `Healthy` predicate, the
post-state helpers, every user operation, the environment action
`accrueInterest`, the liquidation operations, and the `Action` /
`step` action machinery.

Everything here is either:

- a *view*: state → derived value (`debtOf`, `supplyShareFor`, …)
- a *predicate*: state → Prop (`Healthy`, `HealthyOnState`)
- a *transition*: world → option world (the user/env operations)
- the *step* combinator over `Action`

State *shape* is in `States.lean`.  State *invariants* are in
`Invariants.lean`.  Region/budget *side conditions* are in
`Predicates.lean`.
-/

namespace Market

open Util (ceilDiv ceilDiv_mul_ge le_ceilDiv)

/-! ### Conversion formulas (operate on `State`) -/

noncomputable def supplyShareFor (s : State) (assets : ℕ) : ℕ :=
  assets * (s.supplyShares.totalSupply + virtualSupplyShares)
    / (s.totalSupplyAssets + virtualSupplyAssets)

noncomputable def supplyAssetFor (s : State) (shares : ℕ) : ℕ :=
  shares * (s.totalSupplyAssets + virtualSupplyAssets)
    / (s.supplyShares.totalSupply + virtualSupplyShares)

noncomputable def borrowShareFor (s : State) (assets : ℕ) : ℕ :=
  ceilDiv (assets * (s.debtShares.totalSupply + virtualBorrowShares))
          (s.totalBorrowAssets + virtualBorrowAssets)

noncomputable def repayCost (s : State) (shares : ℕ) : ℕ :=
  ceilDiv (shares * (s.totalBorrowAssets + virtualBorrowAssets))
          (s.debtShares.totalSupply + virtualBorrowShares)

noncomputable def debtOf (s : State) (user : Addr) : ℕ :=
  repayCost s (s.debtShares.balances user)

/-- ℚ-shadow of `debtOf` (the user's pro-rata share of total borrowed
assets, *without* the ceilDiv rounding): the natural rational quantity
the downstream `ℚ`-form spec predicates compare against collateral
value.  Related to the ℕ-valued `debtOf` by
`(debtOf s u : ℚ) - 1 < debtOf_q s u ≤ (debtOf s u : ℚ)` (one wei of
ceilDiv slack at the loan-asset scale). -/
noncomputable def debtOf_q (s : State) (u : Addr) : ℚ :=
  (s.debtShares.balances u : ℚ)
    * ((s.totalBorrowAssets : ℚ) + virtualBorrowAssets)
    / ((s.debtShares.totalSupply : ℚ) + virtualBorrowShares)

/-! ### Health predicate (Morpho's two-floor form)

Mirror of Morpho's `_isHealthy`:

```solidity
borrowed  = toAssetsUp(borrowShares, TBA, TBS);                  // ceil
maxBorrow = collateral.mulDivDown(price, ORACLE_PRICE_SCALE)     // floor /10^36
                      .wMulDown(lltv);                           // floor /10^18
return maxBorrow ≥ borrowed;
```

In the typed `Fixed` library both Morpho rounding steps are
`Fixed.mulFloor _ _ 0` — the first divides by `ORACLE_PRICE_SCALE = 10^36`
(price's scale), the second by `WAD = 10^18` (lltv's scale). -/

/-- State-level form of the health check, parameterized by the oracle
price.  This is the shape used by op-guards (which need to evaluate
the predicate on a post-op state under the *current* oracle price).

The comparison `debtAsFixed ≤ maxBorrow` happens *inside* `Fixed 0` —
both sides are scale-tagged, so a misuse like "compare debt to a
`Fixed 36` raw price" is a compile-time type error. -/
def HealthyOnState (s : State) (price : OraclePrice) (user : Addr) : Prop :=
  let collValue : Fixed 0 :=
    Fixed.mulFloorAt (Fixed.ofNat (s.collateral user)) price 0
  let maxBorrow : Fixed 0 := Fixed.mulFloorAt collValue lltv 0
  let debtAsFixed : Fixed 0 := Fixed.ofNat (debtOf s user)
  debtAsFixed ≤ maxBorrow

noncomputable instance HealthyOnState.decidable (s p u) :
    Decidable (HealthyOnState s p u) := by
  unfold HealthyOnState; infer_instance

/-- Position is *healthy*: debt is no more than the collateral's
value (in loan-asset units, valued at the oracle's current read)
discounted by `lltv`. -/
def Healthy (w : World) (user : Addr) : Prop :=
  HealthyOnState w.state w.oracle.read user

noncomputable instance Healthy.decidable (w u) :
    Decidable (Healthy w u) := HealthyOnState.decidable _ _ _

/-! ### Healthy ↔ ℚ-form bridges

Downstream proofs that reason in cross-multiplied ℚ form use these
bridges instead of re-deriving the slack arithmetic each time. -/

private lemma fixed0_toRat (x : Fixed 0) : x.toRat = (x.mantissa : ℚ) := by
  simp [Fixed.toRat]

/-- Forward direction: the typed two-floor health check entails the
ℚ-exact inequality `debt ≤ coll · price · lltv`. -/
theorem Healthy.toQForm {w : World} {user : Addr} (h : Healthy w user) :
    (debtOf w.state user : ℚ)
      ≤ (w.state.collateral user : ℚ) * w.oracle.read_q * lltv_q := by
  unfold Healthy HealthyOnState at h
  set collValue : Fixed 0 :=
    Fixed.mulFloorAt (Fixed.ofNat (w.state.collateral user)) w.oracle.read 0
  set maxBorrow : Fixed 0 := Fixed.mulFloorAt collValue lltv 0
  -- The typed comparison `Fixed.ofNat (debtOf w.state user) ≤ maxBorrow`
  -- reduces to the mantissa-level `debtOf w.state user ≤ maxBorrow.mantissa`
  -- via the `Fixed.LE` instance.
  have h_nat : debtOf w.state user ≤ maxBorrow.mantissa := h
  have hdebt : (debtOf w.state user : ℚ) ≤ (maxBorrow.mantissa : ℚ) := by
    exact_mod_cast h_nat
  rw [← fixed0_toRat maxBorrow] at hdebt
  have h_max : maxBorrow.toRat ≤ collValue.toRat * lltv.toRat :=
    Fixed.mulFloorAt_toRat_le _ _ 0 (by omega)
  have h_cv : collValue.toRat
            ≤ (Fixed.ofNat (w.state.collateral user)).toRat * w.oracle.read.toRat :=
    Fixed.mulFloorAt_toRat_le _ _ 0 (by omega)
  have h_lltv_nonneg : 0 ≤ lltv.toRat := Fixed.toRat_nonneg _
  have h_ofNat : (Fixed.ofNat (w.state.collateral user)).toRat
      = (w.state.collateral user : ℚ) := Fixed.toRat_ofNat _
  rw [h_ofNat] at h_cv
  calc (debtOf w.state user : ℚ)
      ≤ maxBorrow.toRat := hdebt
    _ ≤ collValue.toRat * lltv.toRat := h_max
    _ ≤ (w.state.collateral user : ℚ) * w.oracle.read.toRat * lltv.toRat := by
        exact mul_le_mul_of_nonneg_right h_cv h_lltv_nonneg
    _ = (w.state.collateral user : ℚ) * w.oracle.read_q * lltv_q := rfl

/-- Bounded converse: ℚ form with 2-wei slack at the loan-asset scale
entails the typed `Healthy`.  The slack breaks down as one wei per
floor (each `mulDivDown` shaves up to 1 wei at scale 0; the first
unit's propagation through the second floor is bounded by
`lltv ≤ 1`). -/
theorem Healthy.ofQFormPlusSlack {w : World} {user : Addr}
    (h_slack : (debtOf w.state user : ℚ) + 2
                ≤ (w.state.collateral user : ℚ) * w.oracle.read_q * lltv_q) :
    Healthy w user := by
  unfold Healthy HealthyOnState
  set collValue : Fixed 0 :=
    Fixed.mulFloorAt (Fixed.ofNat (w.state.collateral user)) w.oracle.read 0
  set maxBorrow : Fixed 0 := Fixed.mulFloorAt collValue lltv 0
  have h_cv_slack :
      (Fixed.ofNat (w.state.collateral user)).toRat * w.oracle.read.toRat
        < collValue.toRat + 1 := by
    have h := Fixed.toRat_mul_lt_mulFloorAt_add_unit
              (Fixed.ofNat (w.state.collateral user)) w.oracle.read 0 (by omega)
    simpa using h
  have h_mb_slack :
      collValue.toRat * lltv.toRat < maxBorrow.toRat + 1 := by
    have h := Fixed.toRat_mul_lt_mulFloorAt_add_unit collValue lltv 0 (by omega)
    simpa using h
  have h_ofNat : (Fixed.ofNat (w.state.collateral user)).toRat
      = (w.state.collateral user : ℚ) := Fixed.toRat_ofNat _
  rw [h_ofNat] at h_cv_slack
  have h_lltv_le_one : lltv.toRat ≤ 1 := lltv_q_le_one
  have h_lltv_pos : 0 < lltv.toRat := lltv_q_pos
  have h_step1 :
      (w.state.collateral user : ℚ) * w.oracle.read.toRat * lltv.toRat
        < (collValue.toRat + 1) * lltv.toRat :=
    mul_lt_mul_of_pos_right h_cv_slack h_lltv_pos
  have h_step2 : (collValue.toRat + 1) * lltv.toRat
                  ≤ collValue.toRat * lltv.toRat + 1 := by
    have hexpand : (collValue.toRat + 1) * lltv.toRat
                = collValue.toRat * lltv.toRat + lltv.toRat := by ring
    rw [hexpand]; linarith
  have h_step3 : collValue.toRat * lltv.toRat + 1 < maxBorrow.toRat + 2 := by
    linarith
  have h_chain :
      (w.state.collateral user : ℚ) * w.oracle.read.toRat * lltv.toRat
        < maxBorrow.toRat + 2 :=
    lt_of_lt_of_le (lt_of_lt_of_le h_step1 h_step2) (le_of_lt h_step3)
  have h_lt_q : (debtOf w.state user : ℚ) < maxBorrow.toRat := by
    have := h_slack
    unfold Oracle.read_q lltv_q at this
    linarith [h_chain]
  rw [fixed0_toRat] at h_lt_q
  have h_lt_n : debtOf w.state user < maxBorrow.mantissa := by
    exact_mod_cast h_lt_q
  -- Goal: `Fixed.ofNat (debtOf w.state user) ≤ maxBorrow`, i.e. (after
  -- unfolding `Fixed.LE`) `debtOf w.state user ≤ maxBorrow.mantissa`.
  show debtOf w.state user ≤ maxBorrow.mantissa
  omega

/-! ### Post-state helpers (state-level)

Named post-states for `borrow` / `withdrawCollateral`, shared between
each operation's health-check guard and its return value. -/

noncomputable def afterBorrow
    (s : State) (user : Addr) (loan' : ERC20.State) (assets : ℕ) : State :=
  { s with
    loanAsset := loan'
    debtShares := ERC20.mint s.debtShares user (borrowShareFor s assets)
    totalBorrowAssets := s.totalBorrowAssets + assets }

noncomputable def afterWithdrawCollateral
    (s : State) (user : Addr) (col' : ERC20.State) (c : ℕ) : State :=
  { s with
    collateralAsset := col'
    collateral := s.collateral.update user (s.collateral user - c) }

/-! ### Operations on `World` -/

noncomputable def supply (w : World) (user : Addr) (assets : ℕ) :
    Option (World × ℕ) :=
  match ERC20.transferFrom w.state.loanAsset user marketAddress assets with
  | none => none
  | some loan' =>
    some
      (⟨{ w.state with
          loanAsset := loan'
          supplyShares :=
            ERC20.mint w.state.supplyShares user (supplyShareFor w.state assets)
          totalSupplyAssets := w.state.totalSupplyAssets + assets },
        w.oracle⟩,
       supplyShareFor w.state assets)

noncomputable def withdraw (w : World) (user : Addr) (shares : ℕ) :
    Option (World × ℕ) :=
  if w.state.totalSupplyAssets <
       w.state.totalBorrowAssets + supplyAssetFor w.state shares
  then none
  else
    match ERC20.burn w.state.supplyShares user shares with
    | none => none
    | some shares' =>
      match ERC20.transferFrom w.state.loanAsset marketAddress user
          (supplyAssetFor w.state shares) with
      | none => none
      | some loan' =>
        some
          (⟨{ w.state with
              loanAsset := loan'
              supplyShares := shares'
              totalSupplyAssets :=
                w.state.totalSupplyAssets - supplyAssetFor w.state shares },
            w.oracle⟩,
           supplyAssetFor w.state shares)

/-- Supply collateral.  The `user ≠ marketAddress` guard rules out the
ERC-20 self-transfer corner where the receiver-leg of `transfer` is
balance-neutral while the `state.collateral` ledger update is
user-additive — that mismatch would break the `CollateralBacked`
half of `MarketAccounting`.  Real protocols can't hit this case
(contract addresses don't act as users); the guard makes that fact
provable in the model. -/
noncomputable def supplyCollateral (w : World) (user : Addr) (c : ℕ) :
    Option World :=
  if user = marketAddress then none
  else
    match ERC20.transferFrom w.state.collateralAsset user marketAddress c with
    | none => none
    | some col' =>
      some
        ⟨{ w.state with
           collateralAsset := col'
           collateral :=
             w.state.collateral.update user (w.state.collateral user + c) },
         w.oracle⟩

noncomputable def withdrawCollateral
    (w : World) (user : Addr) (c : ℕ) : Option World :=
  if w.state.collateral user < c then none
  else
    match ERC20.transferFrom w.state.collateralAsset marketAddress user c with
    | none => none
    | some col' =>
      if HealthyOnState (afterWithdrawCollateral w.state user col' c)
          w.oracle.read user
      then some ⟨afterWithdrawCollateral w.state user col' c, w.oracle⟩
      else none

noncomputable def borrow (w : World) (user : Addr) (assets : ℕ) :
    Option (World × ℕ) :=
  if w.state.totalSupplyAssets < w.state.totalBorrowAssets + assets then none
  else
    match ERC20.transferFrom w.state.loanAsset marketAddress user assets with
    | none => none
    | some loan' =>
      if HealthyOnState (afterBorrow w.state user loan' assets)
          w.oracle.read user
      then some (⟨afterBorrow w.state user loan' assets, w.oracle⟩,
                 borrowShareFor w.state assets)
      else none

noncomputable def repay (w : World) (user : Addr) (shares : ℕ) :
    Option (World × ℕ) :=
  match ERC20.transferFrom w.state.loanAsset user marketAddress
      (repayCost w.state shares) with
  | none => none
  | some loan' =>
    match ERC20.burn w.state.debtShares user shares with
    | none => none
    | some debt' =>
      some
        (⟨{ w.state with
            loanAsset := loan'
            debtShares := debt'
            totalBorrowAssets :=
              w.state.totalBorrowAssets - repayCost w.state shares },
          w.oracle⟩,
         repayCost w.state shares)

/-! ### Phase B-1: interest accrual -/

noncomputable def accrueInterest (w : World) (Δ : ℕ) : World :=
  ⟨{ w.state with
      totalBorrowAssets := w.state.totalBorrowAssets + Δ
      totalSupplyAssets := w.state.totalSupplyAssets + Δ },
    w.oracle⟩

@[simp] lemma accrueInterest_oracle (w : World) (Δ : ℕ) :
    (accrueInterest w Δ).oracle = w.oracle := rfl

/-! ### Phase C-1: liquidation and bad-debt write-off -/

/-- Collateral seized for `repaidShares` at observed price `p`,
rounded up.  The ceiling rounding favours the liquidator (they
receive at least `repaidAssets · incentiveFactor` worth of
collateral).  Defined to be `0` at `p = 0` so the function is
total — `liquidate` rejects such states up-front via the unhealth
guard plus the collateral-availability guard.

Decomposed as: (i) `repayCost · bonus`, exact `Fixed.mul` giving
`Fixed 18`, then (ii) `Fixed.divCeilAt` of that by `p` (a `Fixed 36`),
with `target = 0` — landing back in `Fixed 0`, from which `.toNat`
extracts the ℕ-valued seized amount.  The single ceil sits on the divide.

The `0 < p` guard is a `Fixed`-level comparison (`(0 : Fixed 36) < p`),
which reduces definitionally to `0 < p.mantissa` via `Fixed.LT`. -/
noncomputable def seizedFor (s : State) (p : OraclePrice) (repaidShares : ℕ) : ℕ :=
  if (0 : OraclePrice) < p then
    let withBonus : Fixed 18 :=
      (Fixed.ofNat (repayCost s repaidShares)).mul liquidationIncentiveFactor
    (Fixed.divCeilAt withBonus p 0 (by omega)).toNat
  else 0

/-- Liquidate an unhealthy borrower's position.  The liquidator
deposits `repayCost s repaidShares` loan asset and receives
`seizedFor s p repaidShares` collateral.  Partial liquidation is
allowed — the caller picks `repaidShares`. -/
noncomputable def liquidate (w : World)
    (liquidator borrower : Addr) (repaidShares : ℕ) :
    Option (World × ℕ) :=
  if HealthyOnState w.state w.oracle.read borrower then none
  else if w.state.collateral borrower <
            seizedFor w.state w.oracle.read repaidShares then none
  else
    match ERC20.transferFrom w.state.loanAsset liquidator marketAddress
            (repayCost w.state repaidShares) with
    | none => none
    | some loan' =>
      match ERC20.burn w.state.debtShares borrower repaidShares with
      | none => none
      | some debt' =>
        match ERC20.transferFrom w.state.collateralAsset marketAddress liquidator
                (seizedFor w.state w.oracle.read repaidShares) with
        | none => none
        | some col' =>
          some
            (⟨{ w.state with
                loanAsset         := loan'
                collateralAsset   := col'
                debtShares        := debt'
                totalBorrowAssets :=
                  w.state.totalBorrowAssets - repayCost w.state repaidShares
                collateral        := w.state.collateral.update borrower
                  (w.state.collateral borrower -
                   seizedFor w.state w.oracle.read repaidShares) },
              w.oracle⟩,
             seizedFor w.state w.oracle.read repaidShares)

/-- Realize bad debt for a borrower whose collateral is exhausted
but who still has positive debt shares.  All remaining shares are
burned; `totalBorrowAssets` and `totalSupplyAssets` decrease by
the same realized loss `min (repayCost s shares) TBA`.  The cap at
`TBA` is what ensures `BorrowBacked` is preserved — under
`BorrowBacked`, `loss ≤ TBA ≤ TSA`, so neither subtraction
underflows. -/
noncomputable def writeOff (w : World) (borrower : Addr) : Option World :=
  if w.state.collateral borrower ≠ 0 then none
  else if w.state.debtShares.balances borrower = 0 then none
  else
    match ERC20.burn w.state.debtShares borrower
            (w.state.debtShares.balances borrower) with
    | none => none
    | some debt' =>
      some
        ⟨{ w.state with
            debtShares        := debt'
            totalBorrowAssets :=
              w.state.totalBorrowAssets -
                min (repayCost w.state (w.state.debtShares.balances borrower))
                    w.state.totalBorrowAssets
            totalSupplyAssets :=
              w.state.totalSupplyAssets -
                min (repayCost w.state (w.state.debtShares.balances borrower))
                    w.state.totalBorrowAssets },
         w.oracle⟩

/-! ### Action and step

`step` lifts each `Action` to a uniform `World → Option World` function. -/

inductive Action where
  | userSupply             : Addr → ℕ → Action
  | userWithdraw           : Addr → ℕ → Action
  | userSupplyCollateral   : Addr → ℕ → Action
  | userWithdrawCollateral : Addr → ℕ → Action
  | userBorrow             : Addr → ℕ → Action
  | userRepay              : Addr → ℕ → Action
  | userLiquidate          : Addr → Addr → ℕ → Action  -- liquidator, borrower, repaidShares
  | userWriteOff           : Addr → Action
  | envAccrueInt           : ℕ → Action
  | envPriceTick           : OraclePrice → Action

noncomputable def step (a : Action) (w : World) : Option World :=
  match a with
  | .userSupply u amt              => (supply w u amt).map Prod.fst
  | .userWithdraw u sh             => (withdraw w u sh).map Prod.fst
  | .userSupplyCollateral u c      => supplyCollateral w u c
  | .userWithdrawCollateral u c    => withdrawCollateral w u c
  | .userBorrow u amt              => (borrow w u amt).map Prod.fst
  | .userRepay u sh                => (repay w u sh).map Prod.fst
  | .userLiquidate lq br sh        => (liquidate w lq br sh).map Prod.fst
  | .userWriteOff br               => writeOff w br
  | .envAccrueInt Δ                => some (accrueInterest w Δ)
  | .envPriceTick p'               => some ⟨w.state, Oracle.update w.oracle p'⟩

end Market
