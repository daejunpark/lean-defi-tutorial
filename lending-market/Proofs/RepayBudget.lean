import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas

/-!
# Lending Market — Repay/burn budget structure

This module analyses the budget predicate
`RepayDoesNotHitVirtualBorrowAsset` (defined in `Market.Defs.Predicates`,
consumed by `step_preserves_assetCovered` via `BurnStepBudget`) as a
closed-form share threshold, and lays out why the guard is needed
and when it can be discharged automatically.

## Setup

Let `R := totalBorrowAssets`, `S := debtShares.totalSupply`,
`vR := virtualBorrowAssets`, `vS := virtualBorrowShares`, and let
`k := repaidShares`.  The guard

```
RepayDoesNotHitVirtualBorrowAsset w k  :=  repayCost s k ≤ R
```

unfolds (after dividing through by the strictly positive denominators
`S + vS` and `R + vR`) to the linear inequality

```
k * (R + vR) ≤ R * (S + vS)
```

equivalently

```
k ≤ R * (S + vS) / (R + vR)  =:  K  =  maxSafeRepayShares s
```

So the safe region is prefix-shaped:

```
0 ≤ k ≤ K            safe
K < k ≤ S            guard-unsafe
```

The guard-unsafe interval is the rate-monotonicity hazard: at `K < k`
the ceilDiv-rounded `repayCost` strictly exceeds the real `R`, so a
successful burn drains `totalBorrowAssets` to zero while leaving some
debt shares outstanding (when `k < S`); the virtual borrow asset alone
then collateralises those remaining shares, and the per-share rate
`(R' + vR) / (S' + vS)` jumps.

## Contents

The narrative is laid out as a sequence of `theorem`s users can read
in order:

1. **Exact guard equivalence** — `repayCost s k ≤ R ↔ k ≤ K`, lifted
   to the world-level guard predicate.
2. **Safe / unsafe interval** — the safe prefix `k ≤ K` and the
   strict above-cap excess `R < repayCost s k`.
3. **Price-floor sufficient condition** — when the recorded debt-share
   rate is at most the virtual initial price (`S * vR ≤ R * vS`,
   `BorrowPriceFloor`), the entire successful-burn interval `k ≤ S`
   is safe and the budget is discharged automatically.
4. **Post-state shape of above-cap burns** — successful `repay` /
   `liquidate` with `K < k` zero out `totalBorrowAssets`; the
   share-side stays positive iff the burn is partial (`k < S`).
   Together this is the "virtual-only" regime.

The price-floor condition `BorrowPriceFloor` is **not** a global
borrow-side invariant: `repay` can break it through ceilDiv rounding
dust.  It is a sufficient condition for the safe regime, not a
substitute for the guard.
-/

namespace Market

open Util (ceilDiv ceilDiv_le_iff_le_mul)

/-! ## Exact guard equivalence

The state-level cap `maxSafeRepayShares` (`Defs.Predicates`) is the exact
threshold for `repayCost s k ≤ totalBorrowAssets`.  The lifted form
on `World` is the equivalence consumed by `BurnStepBudget`. -/

/-- `repayCost s k ≤ R ↔ k ≤ K`, the exact share-threshold form of
the burn-side guard.  Both sides reduce to `k * (R + vR) ≤ R * (S + vS)`
once the strictly positive denominators are cleared. -/
theorem repayCost_le_totalBorrowAssets_iff_le_maxSafeRepayShares
    (s : State) (k : ℕ) :
    repayCost s k ≤ s.totalBorrowAssets ↔ k ≤ maxSafeRepayShares s := by
  unfold repayCost maxSafeRepayShares
  have hS_pos : 0 < s.debtShares.totalSupply + virtualBorrowShares := by
    have := virtualBorrowShares_pos; omega
  have hR_pos : 0 < s.totalBorrowAssets + virtualBorrowAssets := by
    have := virtualBorrowAssets_pos; omega
  rw [ceilDiv_le_iff_le_mul _ _ _ hS_pos, Nat.le_div_iff_mul_le hR_pos]

/-- World-level form: the `BurnStepBudget` clause for a single
share-burn action is exactly `k ≤ K`. -/
theorem repayDoesNotHitVirtualBorrowAsset_iff_le_maxSafeRepayShares
    (w : World) (k : ℕ) :
    RepayDoesNotHitVirtualBorrowAsset w k ↔ k ≤ maxSafeRepayShares w.state :=
  repayCost_le_totalBorrowAssets_iff_le_maxSafeRepayShares w.state k

/-! ## Safe and unsafe intervals

Direct corollaries of the equivalence above.  The above-cap side is
strict (`R < repayCost s k`), because the equivalence is `≤ ↔ ≤`. -/

/-- Prefix safety: every `k ≤ K` is below the guard. -/
theorem repayCost_safe_of_le_maxSafeRepayShares
    {s : State} {k : ℕ} (hk : k ≤ maxSafeRepayShares s) :
    repayCost s k ≤ s.totalBorrowAssets :=
  (repayCost_le_totalBorrowAssets_iff_le_maxSafeRepayShares s k).mpr hk

/-- Above-cap strict excess: every `k > K` strictly overshoots `R`. -/
theorem totalBorrowAssets_lt_repayCost_of_maxSafeRepayShares_lt
    {s : State} {k : ℕ} (hk : maxSafeRepayShares s < k) :
    s.totalBorrowAssets < repayCost s k := by
  by_contra hle
  push Not at hle
  have := (repayCost_le_totalBorrowAssets_iff_le_maxSafeRepayShares s k).mp hle
  omega

/-! ## Price-floor sufficient condition

When the recorded debt-share rate is at most the virtual initial
price (`BorrowPriceFloor`), the cap covers the entire successful-burn
interval `k ≤ S`, and the budget discharges automatically. -/

/-- `BorrowPriceFloor s ⟹ S ≤ K`.

Reason: `S * vR ≤ R * vS` rearranges to
`S * (R + vR) ≤ R * (S + vS)`, which is the threshold form of
`S ≤ R * (S + vS) / (R + vR)`. -/
theorem totalDebtShares_le_maxSafeRepayShares_of_borrowPriceFloor
    {s : State} (hfloor : BorrowPriceFloor s) :
    s.debtShares.totalSupply ≤ maxSafeRepayShares s := by
  unfold maxSafeRepayShares
  unfold BorrowPriceFloor at hfloor
  have hR_pos : 0 < s.totalBorrowAssets + virtualBorrowAssets := by
    have := virtualBorrowAssets_pos; omega
  rw [Nat.le_div_iff_mul_le hR_pos]
  nlinarith [hfloor]

/-- Automatic-budget corollary: under `BorrowPriceFloor`, every
successful-burn amount `k ≤ S` satisfies the guard, so no explicit
burn budget is needed in that regime. -/
theorem repayDoesNotHitVirtualBorrowAsset_of_borrowPriceFloor
    {w : World} {k : ℕ}
    (hfloor : BorrowPriceFloor w.state)
    (hk : k ≤ w.state.debtShares.totalSupply) :
    RepayDoesNotHitVirtualBorrowAsset w k := by
  rw [repayDoesNotHitVirtualBorrowAsset_iff_le_maxSafeRepayShares]
  exact hk.trans (totalDebtShares_le_maxSafeRepayShares_of_borrowPriceFloor hfloor)

/-! ## Post-state shape of above-cap burns

When a successful `repay` / `liquidate` runs at `K < k` (the guard is
violated but the share-side burn still goes through), the real borrow
side is fully consumed (`totalBorrowAssets' = 0`) while the share
supply only drops by `k`.  On a partial burn (`k < S`) the share
supply stays strictly positive — the "virtual-only" regime where the
virtual borrow asset alone collateralises the remaining shares. -/

/-- Above-cap successful `repay` zeroes out the real borrow side:
`R < repayCost` together with `Nat` subtraction forces `R' = 0`. -/
theorem repay_above_cap_leaves_zero_totalBorrowAssets
    {w w' : World} {user : Addr} {k assets : ℕ}
    (hr : repay w user k = some (w', assets))
    (hunsafe : maxSafeRepayShares w.state < k) :
    w'.state.totalBorrowAssets = 0 := by
  obtain ⟨htba, _, hassets, _⟩ := repay_extract hr
  have hexcess := totalBorrowAssets_lt_repayCost_of_maxSafeRepayShares_lt hunsafe
  rw [htba, hassets]
  omega

/-- Partial `repay` (`k < S`) leaves the share-supply strictly
positive: `0 < S' = S - k`. -/
theorem repay_partial_burn_leaves_debt_shares
    {w w' : World} {user : Addr} {k assets : ℕ}
    (hr : repay w user k = some (w', assets))
    (hpartial : k < w.state.debtShares.totalSupply) :
    0 < w'.state.debtShares.totalSupply := by
  obtain ⟨_, hsh, _, _⟩ := repay_extract hr
  rw [hsh]
  omega

/-- Above-cap successful `liquidate` zeroes out the real borrow side
(mirror of `repay_above_cap_leaves_zero_totalBorrowAssets`). -/
theorem liquidate_above_cap_leaves_zero_totalBorrowAssets
    {w w' : World} {liquidator borrower : Addr} {k seized : ℕ}
    (hl : liquidate w liquidator borrower k = some (w', seized))
    (hunsafe : maxSafeRepayShares w.state < k) :
    w'.state.totalBorrowAssets = 0 := by
  obtain ⟨htba, _⟩ := liquidate_extract hl
  have hexcess := totalBorrowAssets_lt_repayCost_of_maxSafeRepayShares_lt hunsafe
  rw [htba]
  omega

/-- Partial `liquidate` (`k < S`) leaves the share-supply strictly
positive (mirror of `repay_partial_burn_leaves_debt_shares`). -/
theorem liquidate_partial_burn_leaves_debt_shares
    {w w' : World} {liquidator borrower : Addr} {k seized : ℕ}
    (hl : liquidate w liquidator borrower k = some (w', seized))
    (hpartial : k < w.state.debtShares.totalSupply) :
    0 < w'.state.debtShares.totalSupply := by
  obtain ⟨_, hsh, _⟩ := liquidate_extract hl
  rw [hsh]
  omega

/-! ### The virtual-only regime

The user-facing hazard: in the joint above-cap-and-partial interval
`K < k < S`, a successful `repay` / `liquidate` leaves the market
with `totalBorrowAssets' = 0` while `0 < debtShares.totalSupply'`.
The remaining debt shares are then collateralised by the virtual
borrow asset alone, and the per-share rate `(R' + vR) / (S' + vS)`
jumps discontinuously.  This is precisely what the burn budget
`RepayDoesNotHitVirtualBorrowAsset` exists to prevent. -/

/-- Above-cap partial `repay` enters the virtual-only regime:
`totalBorrowAssets' = 0` while `0 < debtShares.totalSupply'`. -/
theorem repay_above_cap_partial_burn_enters_virtual_only_regime
    {w w' : World} {user : Addr} {k assets : ℕ}
    (hr : repay w user k = some (w', assets))
    (hunsafe : maxSafeRepayShares w.state < k)
    (hpartial : k < w.state.debtShares.totalSupply) :
    w'.state.totalBorrowAssets = 0 ∧ 0 < w'.state.debtShares.totalSupply :=
  ⟨repay_above_cap_leaves_zero_totalBorrowAssets hr hunsafe,
   repay_partial_burn_leaves_debt_shares hr hpartial⟩

/-- Above-cap partial `liquidate` enters the virtual-only regime
(mirror of `repay_above_cap_partial_burn_enters_virtual_only_regime`). -/
theorem liquidate_above_cap_partial_burn_enters_virtual_only_regime
    {w w' : World} {liquidator borrower : Addr} {k seized : ℕ}
    (hl : liquidate w liquidator borrower k = some (w', seized))
    (hunsafe : maxSafeRepayShares w.state < k)
    (hpartial : k < w.state.debtShares.totalSupply) :
    w'.state.totalBorrowAssets = 0 ∧ 0 < w'.state.debtShares.totalSupply :=
  ⟨liquidate_above_cap_leaves_zero_totalBorrowAssets hl hunsafe,
   liquidate_partial_burn_leaves_debt_shares hl hpartial⟩

end Market
