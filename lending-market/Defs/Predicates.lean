import Defs.Semantics

/-!
# Lending Market — Side-condition predicates

Predicate definitions used as preservation-theorem preconditions:
action filters, action-level rounding/move budgets, borrower
state-space regions, borrower rounding budgets, repay-side
conditions, and step-level budget combinators.

These are *not* invariants of the protocol — they are restricting
hypotheses that gate when a preservation theorem fires (e.g.
`step_preserves_assetCovered` only applies to actions satisfying
`LiquidateStepBudget` and `BurnStepBudget`).
-/

namespace Market

/-! ### Action filters

`NoBadDebt`, `NoPriceMove`, `NoAccrual` exclude exactly the actions
that break specific invariants (bad-debt write-off → supply share
price; price tick → `AllHealthy`; interest accrual → `AllHealthy`). -/

/-- An action that does **not** realize bad debt.  Activated on
`.userWriteOff`: bad-debt write-off socializes loss to lenders, so
it breaks `SupplySharePriceLE` (the supply-share price drops). -/
def NoBadDebt : Action → Prop
  | .userWriteOff _ => False
  | _               => True

/-- An action that does **not** move the oracle price. -/
def NoPriceMove : Action → Prop
  | .envPriceTick _ => False
  | _               => True

/-- An action that does **not** accrue interest. -/
def NoAccrual : Action → Prop
  | .envAccrueInt _ => False
  | _               => True

/-! ### Action-level rounding/move budgets -/

/-- `AccrualBudget a w` gates `step_preserves_assetCovered` on
`envAccrueInt Δ`: requires `Δ · lltv ≤ TBA · (1 - lltv)` in ℚ form. -/
def AccrualBudget : Action → World → Prop
  | .envAccrueInt Δ, w =>
      (Δ : ℚ) * lltv_q ≤ (w.state.totalBorrowAssets : ℚ) * (1 - lltv_q)
  | _,                _ => True

/-- `PriceMoveBudget a p` gates `step_preserves_assetCovered` on
`envPriceTick p'`: requires the new price `p'` to satisfy
`p · lltv ≤ p'` in ℚ form. -/
def PriceMoveBudget : Action → OraclePrice → Prop
  | .envPriceTick p', p => p.toRat * lltv_q ≤ p'.toRat
  | _,                _ => True

/-! ### Region predicates

For a borrower `b`, `Healable` and `BadDebtPath` partition the
borrower's state-space relative to the bonus-adjusted coverage.

Both predicates are stated via `debtOf_q` (the borrower's ℚ-debt) times
the liquidation bonus, compared to the collateral value at the
oracle's price.  Proofs convert to the share-multiplied (division-free)
form via `Healable_iff_shareMul` / `BadDebtPath_iff_shareMul`. -/

/-- Borrower `b`'s bonus-inflated ℚ-debt is covered by their collateral
value.  Disjunction of the strictly-`Healthy` and "healable unhealthy"
sub-regions. -/
def Healable (w : World) (b : Addr) : Prop :=
  debtOf_q w.state b * liquidationIncentiveFactor_q
    ≤ (w.state.collateral b : ℚ) * w.oracle.read_q

/-- Borrower `b`'s bonus-inflated ℚ-debt exceeds their collateral
value.  In this region, no liquidation restores `Healthy` and every
liquidation eats lender capital under the fixed-bonus design. -/
def BadDebtPath (w : World) (b : Addr) : Prop :=
  (w.state.collateral b : ℚ) * w.oracle.read_q
    < debtOf_q w.state b * liquidationIncentiveFactor_q

/-- Share-multiplied form of `Healable`, equivalent because
`dshTotal + vBS > 0`. -/
theorem Healable_iff_shareMul (w : World) (b : Addr) :
    Healable w b ↔
    (w.state.debtShares.balances b : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
        * liquidationIncentiveFactor_q
      ≤ (w.state.collateral b : ℚ) * w.oracle.read_q
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
  unfold Healable debtOf_q
  have hvBS_pos_q : (0 : ℚ) < (virtualBorrowShares : ℚ) := by
    exact_mod_cast virtualBorrowShares_pos
  have hTs_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
    exact_mod_cast Nat.zero_le _
  have hS_pos :
      (0 : ℚ) < (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    linarith
  rw [div_mul_eq_mul_div]
  exact div_le_iff₀ hS_pos

/-- Share-multiplied form of `BadDebtPath`, equivalent because
`dshTotal + vBS > 0`. -/
theorem BadDebtPath_iff_shareMul (w : World) (b : Addr) :
    BadDebtPath w b ↔
    (w.state.collateral b : ℚ) * w.oracle.read_q
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
      < (w.state.debtShares.balances b : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
        * liquidationIncentiveFactor_q := by
  unfold BadDebtPath debtOf_q
  have hvBS_pos_q : (0 : ℚ) < (virtualBorrowShares : ℚ) := by
    exact_mod_cast virtualBorrowShares_pos
  have hTs_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
    exact_mod_cast Nat.zero_le _
  have hS_pos :
      (0 : ℚ) < (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    linarith
  rw [div_mul_eq_mul_div]
  exact lt_div_iff₀ hS_pos

theorem healable_or_bad_debt_path (w : World) (b : Addr) :
    Healable w b ∨ BadDebtPath w b := by
  rw [Healable_iff_shareMul, BadDebtPath_iff_shareMul]
  exact Or.symm (lt_or_ge _ _)

theorem not_healable_iff_bad_debt_path (w : World) (b : Addr) :
    ¬ Healable w b ↔ BadDebtPath w b := by
  rw [Healable_iff_shareMul, BadDebtPath_iff_shareMul]
  exact not_le

/-! ### Liquidation rounding budgets

Closed-form, borrower-local conditions tight enough to discharge the
ℕ-rounding slop in `repayCost` and `seizedFor` for the
`AssetCovered`-direct preservation theorem `step_preserves_assetCovered`. -/

/-- Closed-form one-step rounding-loss budget for the borrower:
the slack `bonus + price` (LHS) must fit inside the headroom
`collateralValue − debtOf · bonus` (RHS).

The LHS decomposes as a sum of two ceilDiv slacks, each at most one
wei at their natural scale, valued in loan-asset units:

| Term in LHS                       | Origin of the wei                            | Valuation factor |
|-----------------------------------|----------------------------------------------|------------------|
| `liquidationIncentiveFactor_q`    | one wei of `repayCost` (the burn-leg ceilDiv) | × `bonus`        |
| `w.oracle.read_q`                 | one wei of `seizedFor` (the seize-leg ceilDiv)| × `price`        |

These are exactly the two rounding-up steps in a single `liquidate`
call: the burn side rounds the assets owed *up* (favouring the
protocol), and the seize side rounds the collateral granted *up*
(favouring the liquidator).  Their summed worst-case overshoot must
not exceed how far the borrower currently sits below the bonus-adjusted
coverage line, hence the `≤ collateralValue − debtOf · bonus`.

Used as both
* the borrower-local rounding budget for `liquidate_preserves_assetCovered`
  (rounding); and
* the closed-form healing budget for `exists_full_liquidation_to_healthy`
  (full-burn liquidation lands in `Healthy`). -/
noncomputable def HealableLiquidationBudget (w : World) (b : Addr) : Prop :=
  liquidationIncentiveFactor_q + w.oracle.read_q
    ≤ (w.state.collateral b : ℚ) * w.oracle.read_q
      - (debtOf w.state b : ℚ) * liquidationIncentiveFactor_q

/-- The repayment leg stays inside real borrowed assets.

When this fails, the burn can consume the virtual borrow asset and
increase the remaining borrow-share rate.  Not a borrower rounding
budget; ordinary rate-monotonicity side condition for non-actor users
after a `repay` or partial `liquidate` burn.

The exact share-threshold form `repaidShares ≤ maxSafeRepayShares s`
and its consequences are developed in `Market.RepayBudget`. -/
def RepayDoesNotHitVirtualBorrowAsset (w : World) (repaidShares : ℕ) : Prop :=
  repayCost w.state repaidShares ≤ w.state.totalBorrowAssets

/-- The largest number of debt shares whose `repayCost` still fits
inside `totalBorrowAssets`.

In the abbreviations `R := totalBorrowAssets`, `S := totalSupply`,
`vR := virtualBorrowAssets`, `vS := virtualBorrowShares`, this is
`R * (S + vS) / (R + vR)` (floor division).  It is the exact
`RepayDoesNotHitVirtualBorrowAsset` threshold: the guard holds iff
`repaidShares ≤ maxSafeRepayShares s`.  See `Market.RepayBudget`. -/
noncomputable def maxSafeRepayShares (s : State) : ℕ :=
  s.totalBorrowAssets * (s.debtShares.totalSupply + virtualBorrowShares)
    / (s.totalBorrowAssets + virtualBorrowAssets)

/-- Borrow-side virtual-price floor: the recorded debt-share rate
`S * vR ≤ R * vS` is at least as cheap as the virtual initial price.

When this holds, every successful debt-share burn `k ≤ S` is safe
(`RepayDoesNotHitVirtualBorrowAsset`), so no explicit burn budget is
needed.  Not a global invariant: `repay` can break it via ceilDiv
rounding dust.  See `Market.RepayBudget`. -/
def BorrowPriceFloor (s : State) : Prop :=
  s.debtShares.totalSupply * virtualBorrowAssets
    ≤ s.totalBorrowAssets * virtualBorrowShares

/-! ### Step-level budgets for `step_preserves_assetCovered`

Action-level case-analyzing predicates, mirroring the `NoPriceMove` /
`NoAccrual` pattern: each governs one specific concern (healable region
or repay cost-bound), is `True` for the actions it does not constrain,
and is intentionally `False` for environment actions excluded from
`step_preserves_assetCovered` (those are handled by the chain theorems
in `AllHealthyToAssetCovered.lean`). -/

/-- Healable side condition: required only for `userLiquidate`, where
the action's borrower must satisfy `HealableLiquidationBudget`. -/
noncomputable def LiquidateStepBudget : Action → World → Prop
  | .userLiquidate _ b _, w => HealableLiquidationBudget w b
  | _, _ => True

/-- Repay-cost side condition: required for share-burn actions
(`userRepay` and `userLiquidate`) — the action's repaid-shares amount
must satisfy `RepayDoesNotHitVirtualBorrowAsset`. -/
def BurnStepBudget : Action → World → Prop
  | .userRepay _ sh, w => RepayDoesNotHitVirtualBorrowAsset w sh
  | .userLiquidate _ _ sh, w => RepayDoesNotHitVirtualBorrowAsset w sh
  | _, _ => True

end Market
