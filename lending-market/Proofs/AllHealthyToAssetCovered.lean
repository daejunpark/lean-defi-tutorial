import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas
import Proofs.AllHealthy
import Proofs.AssetCovered

/-!
# Lending Market — `AllHealthy ⟹ AssetCovered` chain

The fragile-to-durable chain.  `AllHealthy` (every user has the LTV
buffer) is preserved by all six user ops but breaks under environment
events; `AssetCovered` (debt covered without the LTV buffer) is the
durable layer that survives those events under their respective budgets.

This file expresses how the fragile `AllHealthy` layer feeds into
`AssetCovered`:

* state-level — `allHealthy_implies_assetCovered`: pre-state `AllHealthy`
  implies pre-state `AssetCovered`.
* env-action preservation — `accrueInterest_preserves_assetCovered`,
  `priceTick_preserves_assetCovered`: env actions break `AllHealthy`,
  but under the action's budget they take an `AllHealthy` state to an
  `AssetCovered` state (still a chain, since the post-state need only
  satisfy the weaker `AssetCovered`).
* step-level — `step_remains_assetCovered_under_allHealthy`: starting
  from `AllHealthy`, every action that survives the `AllHealthy`
  preservation contract (or accrual under budget, or price tick under
  budget) lands in an `AssetCovered` post-state.

The truly `AssetCovered → AssetCovered` direction lives in
`AssetCovered.lean` (and its budgeted step-level theorem
`step_preserves_assetCovered`).

## Main theorems
- `allHealthy_implies_assetCovered`
- `accrueInterest_preserves_assetCovered`
- `priceTick_preserves_assetCovered`
- `step_remains_assetCovered_under_allHealthy`
-/

namespace Market

open Util (ceilDiv ceilDiv_mul_ge)

/-- `AllHealthy w` implies `AssetCovered w`.  In the new two-floor
`Healthy` form, no oracle-price nonnegativity hypothesis is needed
(mantissas are `Nat`; `toRat` is automatic). -/
theorem allHealthy_implies_assetCovered
    {w : World} (hAH : AllHealthy w) :
    AssetCovered w := by
  rw [AssetCovered_iff_shareMul]
  intro u
  exact healthy_user_implies_assetCovered_user (hAH u)

/-! ## Environment-action preservation (under `AllHealthy`)

Both env actions break `AllHealthy`, but under their respective budgets
they land in `AssetCovered` from an `AllHealthy` start. -/

/-- `accrueInterest` preserves `AssetCovered` exactly — no rounding
slack — under `AllHealthy w` and the budget
`Δ · lltv_q +≤ TBA · (1 - lltv_q)`.

The proof composes three ℚ-strict ingredients: per-user `AllHealthy`
scaled by `S`; the ceilDiv lower bound `sh · R ≤ debtOf · S`; and the
budget which gives `R_new · lltv_q +≤ R_old`. -/
theorem accrueInterest_preserves_assetCovered
    {w : World} {Δ : ℕ}
    (hAH : AllHealthy w)
    (hΔ : (Δ : ℚ) * lltv_q ≤ (w.state.totalBorrowAssets : ℚ) * (1 - lltv_q)) :
    AssetCovered (accrueInterest w Δ) := by
  rw [AssetCovered_iff_shareMul]
  intro u
  show (w.state.debtShares.balances u : ℚ)
        * (((w.state.totalBorrowAssets + Δ : ℕ) : ℚ) + (virtualBorrowAssets : ℚ))
       ≤ (w.state.collateral u : ℚ) * w.oracle.read_q
        * ((w.state.debtShares.totalSupply : ℚ) + (virtualBorrowShares : ℚ))
  have hltv_pos : (0 : ℚ) < lltv_q := lltv_q_pos
  have hltv_nn : (0 : ℚ) ≤ lltv_q := le_of_lt hltv_pos
  have hltv_le_one : lltv_q ≤ 1 := lltv_q_le_one
  have hvBA_nn : (0 : ℚ) ≤ (virtualBorrowAssets : ℚ) := by exact_mod_cast Nat.zero_le _
  have hsh_nn : (0 : ℚ) ≤ (w.state.debtShares.balances u : ℚ) := by
    exact_mod_cast Nat.zero_le _
  have hcoll_nn : (0 : ℚ) ≤ (w.state.collateral u : ℚ) := by exact_mod_cast Nat.zero_le _
  have hTBA_nn : (0 : ℚ) ≤ (w.state.totalBorrowAssets : ℚ) := by exact_mod_cast Nat.zero_le _
  have hDBT_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
    exact_mod_cast Nat.zero_le _
  have hvBS_nn : (0 : ℚ) ≤ (virtualBorrowShares : ℚ) := by exact_mod_cast Nat.zero_le _
  have hS_nn : (0 : ℚ) ≤ ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
    linarith
  have hCD : (w.state.debtShares.balances u) *
                (w.state.totalBorrowAssets + virtualBorrowAssets)
              ≤ debtOf w.state u *
                (w.state.debtShares.totalSupply + virtualBorrowShares) := by
    unfold debtOf repayCost
    apply ceilDiv_mul_ge
    have := virtualBorrowShares_pos; omega
  have hCD_q : (w.state.debtShares.balances u : ℚ) *
                  ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
                ≤ (debtOf w.state u : ℚ) *
                  ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
    exact_mod_cast hCD
  have hAH_S : (debtOf w.state u : ℚ) *
                 ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
               ≤ (w.state.collateral u : ℚ) * w.oracle.read_q * lltv_q *
                 ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
    -- `hAH u` is the new two-floor `Healthy`; pull out the ℚ-form
    -- `debt ≤ coll · price · lltv` bound.
    have h := mul_le_mul_of_nonneg_right (Healthy.toQForm (hAH u)) hS_nn
    nlinarith
  have hSRold : (w.state.debtShares.balances u : ℚ) *
                   ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
                 ≤ (w.state.collateral u : ℚ) * w.oracle.read_q * lltv_q *
                   ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
    linarith
  have hRnew_lltv : ((w.state.totalBorrowAssets : ℚ) + Δ + virtualBorrowAssets) * lltv_q
                    ≤ (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets := by
    nlinarith [hΔ, hltv_le_one, hvBA_nn, hltv_nn]
  have key : (w.state.debtShares.balances u : ℚ) *
                ((w.state.totalBorrowAssets : ℚ) + Δ + virtualBorrowAssets) * lltv_q
              ≤ (w.state.collateral u : ℚ) * w.oracle.read_q * lltv_q *
                ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
    have h := mul_le_mul_of_nonneg_left hRnew_lltv hsh_nn
    nlinarith [h, hSRold]
  have key' : (w.state.debtShares.balances u : ℚ) *
                ((w.state.totalBorrowAssets : ℚ) + Δ + virtualBorrowAssets) * lltv_q
              ≤ (w.state.collateral u : ℚ) * w.oracle.read_q *
                ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) * lltv_q := by
    have e : (w.state.collateral u : ℚ) * w.oracle.read_q * lltv_q *
              ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
           = (w.state.collateral u : ℚ) * w.oracle.read_q *
              ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) * lltv_q := by
      ring
    rw [← e]; exact key
  have hcancel := le_of_mul_le_mul_right key' hltv_pos
  have hcast : ((w.state.totalBorrowAssets + Δ : ℕ) : ℚ) + (virtualBorrowAssets : ℚ)
             = (w.state.totalBorrowAssets : ℚ) + Δ + virtualBorrowAssets := by
    push_cast; ring
  rw [hcast]; exact hcancel

/-- `AssetCovered` survives a price tick from `w.oracle.read_q`
to `p'.toRat` provided the drop is bounded:
`w.oracle.read_q · lltv_q ≤ p'.toRat`.  Symmetric to
`accrueInterest_preserves_assetCovered`. -/
theorem priceTick_preserves_assetCovered
    {w : World} {p' : OraclePrice}
    (hAH : AllHealthy w)
    (hpmb : w.oracle.read_q * lltv_q ≤ p'.toRat) :
    AssetCovered ⟨w.state, Oracle.update w.oracle p'⟩ := by
  rw [AssetCovered_iff_shareMul]
  intro u
  set R : ℕ := w.state.totalBorrowAssets + virtualBorrowAssets
  set S : ℕ := w.state.debtShares.totalSupply + virtualBorrowShares
  have hS_pos : 0 < S := by
    show 0 < w.state.debtShares.totalSupply + virtualBorrowShares
    have := virtualBorrowShares_pos; omega
  have hCD : w.state.debtShares.balances u * R ≤ debtOf w.state u * S := by
    show w.state.debtShares.balances u * (w.state.totalBorrowAssets + virtualBorrowAssets)
       ≤ debtOf w.state u * (w.state.debtShares.totalSupply + virtualBorrowShares)
    unfold debtOf repayCost; exact ceilDiv_mul_ge _ hS_pos
  have hCD_q : (w.state.debtShares.balances u : ℚ) * (R : ℚ)
              ≤ (debtOf w.state u : ℚ) * (S : ℚ) := by exact_mod_cast hCD
  have hS_nn : (0 : ℚ) ≤ (S : ℚ) := by exact_mod_cast Nat.zero_le _
  have hcol_nn : (0 : ℚ) ≤ (w.state.collateral u : ℚ) := by exact_mod_cast Nat.zero_le _
  have hAH_S : (debtOf w.state u : ℚ) * (S : ℚ)
              ≤ (w.state.collateral u : ℚ) * w.oracle.read_q * lltv_q * (S : ℚ) := by
    have h := mul_le_mul_of_nonneg_right (Healthy.toQForm (hAH u)) hS_nn
    nlinarith
  have hSh_R : (w.state.debtShares.balances u : ℚ) * (R : ℚ)
              ≤ (w.state.collateral u : ℚ) * w.oracle.read_q * lltv_q * (S : ℚ) := by linarith
  have hcS_nn : (0 : ℚ) ≤ (w.state.collateral u : ℚ) * (S : ℚ) := mul_nonneg hcol_nn hS_nn
  have hPbud : (w.state.collateral u : ℚ) * w.oracle.read_q * lltv_q * (S : ℚ)
              ≤ (w.state.collateral u : ℚ) * p'.toRat * (S : ℚ) := by
    nlinarith [hcS_nn, hpmb]
  show (w.state.debtShares.balances u : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
       ≤ (w.state.collateral u : ℚ)
          * (⟨w.state, Oracle.update w.oracle p'⟩ : World).oracle.read_q
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
  show (w.state.debtShares.balances u : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
       ≤ (w.state.collateral u : ℚ) * p'.toRat
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
  have hRq : ((R : ℕ) : ℚ) = (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets := by
    show ((w.state.totalBorrowAssets + virtualBorrowAssets : ℕ) : ℚ)
       = (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets
    push_cast; ring
  have hSq : ((S : ℕ) : ℚ) = (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    show ((w.state.debtShares.totalSupply + virtualBorrowShares : ℕ) : ℚ)
       = (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares
    push_cast; ring
  rw [← hRq, ← hSq]; linarith

/-! ## Step-level chain

Under `AllHealthy w`, every step lands in `AssetCovered w'`.  User
actions discharge through `step_preserves_allHealthy` plus
`allHealthy_implies_assetCovered`; the two environment actions
discharge through `accrueInterest_preserves_assetCovered` /
`priceTick_preserves_assetCovered` above. -/

/-- Step-level chain: under `AllHealthy w`, every step lands in
`AssetCovered w'`.  User actions discharge through
`step_preserves_allHealthy ∘ allHealthy_implies_assetCovered`; the two
environment actions discharge through their respective `AssetCovered`
preservation theorems and budgets. -/
theorem step_remains_assetCovered_under_allHealthy
    {a : Action} {w w' : World}
    (h_pmb : PriceMoveBudget a (w.oracle.read))
    (hbk : Bookkeep w) (hAH : AllHealthy w)
    (h_acb : AccrualBudget a w)
    (hstep : step a w = some w') :
    AssetCovered w' := by
  cases a with
  | userSupply u amt =>
    obtain ⟨_, hsup⟩ := step_userSupply_some hstep
    exact allHealthy_implies_assetCovered (supply_preserves_allHealthy hAH hsup)
  | userWithdraw u sh =>
    obtain ⟨_, hwd⟩ := step_userWithdraw_some hstep
    exact allHealthy_implies_assetCovered (withdraw_preserves_allHealthy hAH hwd)
  | userSupplyCollateral u c =>
    exact allHealthy_implies_assetCovered
      (supplyCollateral_preserves_allHealthy hAH (step_userSupplyCollateral_some hstep))
  | userWithdrawCollateral u c =>
    exact allHealthy_implies_assetCovered
      (withdrawCollateral_preserves_allHealthy hAH
        (step_userWithdrawCollateral_some hstep))
  | userBorrow u amt =>
    obtain ⟨_, hb⟩ := step_userBorrow_some hstep
    exact allHealthy_implies_assetCovered (borrow_preserves_allHealthy hAH hb)
  | userRepay u sh =>
    obtain ⟨_, hr⟩ := step_userRepay_some hstep
    exact allHealthy_implies_assetCovered (repay_preserves_allHealthy hbk hAH hr)
  | userLiquidate lq br sh =>
    obtain ⟨_, hl⟩ := step_userLiquidate_some hstep
    exact allHealthy_implies_assetCovered (liquidate_preserves_allHealthy hAH hl)
  | userWriteOff br =>
    exact allHealthy_implies_assetCovered
      (writeOff_preserves_allHealthy hAH (step_userWriteOff_some hstep))
  | envAccrueInt Δ =>
    rw [step_envAccrueInt_some hstep]
    have hΔ : (Δ : ℚ) * lltv_q ≤ (w.state.totalBorrowAssets : ℚ) * (1 - lltv_q) := h_acb
    exact accrueInterest_preserves_assetCovered hAH hΔ
  | envPriceTick p' =>
    rw [step_envPriceTick_some hstep]
    have h_pmb' : w.oracle.read_q * lltv_q ≤ p'.toRat := h_pmb
    exact priceTick_preserves_assetCovered hAH h_pmb'

end Market
