import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates

/-!
# Lending Market — Cross-file lemmas

Helper lemmas used by multiple proof files.

## Contents
- ERC-20 shape lemmas: `mint_totalSupply`, `burn_totalSupply`,
  `balance_le_totalSupply`, `burn_amount_le`,
  `burn_balances_self`, `burn_balances_other`.
- Conversion-formula bounds: `supplyShareFor_bound`,
  `borrowShareFor_bound`.
- Op-result extraction: `supply_extract`, `withdraw_extract`,
  `borrow_extract`, `repay_extract`, `liquidate_extract`,
  `writeOff_extract`.
- Step-result extraction: `step_user*_some`, `step_envAccrueInt_some`,
  `step_envPriceTick_some`.
- Zero-debt-shares simplifications: `debtOf_eq_zero_of_debtShares_balance_eq_zero`,
  `healthy_of_debtShares_balance_zero`.
- Liquidation post-state shape: `liquidate_burns_repaidShares`,
  `liquidate_debtShares_balances_other`,
  `liquidate_repaidShares_le_borrower_balance`.
- Rounding bounds: `repayCost_le_shareValue_add_one`,
  `seizedFor_mul_price_le_cost_bonus_add_price`.
- Rate-monotonicity helpers: `assetCovered_after_burn_rate_le`,
  `assetCovered_after_borrow_rate_le`.
- Liquidation bonus formula theorems:
  `MAX_LIF_mantissa`, `LIQ_CURSOR_mantissa`, `MAX_LIF_toRat`,
  `LIQ_CURSOR_toRat`, `LIQ_CURSOR_mantissa_lt_WAD`,
  `liquidationIncentiveFactor_q_ge_one`,
  `liquidationIncentiveFactor_q_nonneg`,
  `liquidationIncentiveFactor_q_lltv_q_lt_one`.
-/

namespace Market

open Util (ceilDiv ceilDiv_mul_ge)

/-! ## ERC-20 shape lemmas -/

lemma mint_totalSupply (s : ERC20.State) (u : Addr) (amt : ℕ) :
    (ERC20.mint s u amt).totalSupply = s.totalSupply + amt := rfl

lemma burn_totalSupply {s s' : ERC20.State} {u : Addr} {amt : ℕ}
    (hb : ERC20.burn s u amt = some s') :
    s'.totalSupply = s.totalSupply - amt := by
  unfold ERC20.burn at hb
  split at hb
  · simp at hb
  · simp only [Option.some.injEq] at hb
    rw [← hb]

lemma balance_le_totalSupply
    {s : ERC20.State} (h : ERC20.Invariant s) (u : Addr) :
    s.balances u ≤ s.totalSupply := by
  unfold ERC20.Invariant ERC20.sumBalances at h
  rw [h]
  have he := Finsupp.sum_update_add s.balances u 0 (fun _ b => b)
    (fun _ => rfl) (fun _ _ _ => rfl)
  dsimp only at he
  omega

lemma burn_amount_le {s s' : ERC20.State} {u : Addr} {amt : ℕ}
    (hb : ERC20.burn s u amt = some s') :
    amt ≤ s.balances u := by
  unfold ERC20.burn at hb
  split at hb
  · simp at hb
  · next h => simp only [not_lt] at h; exact h

lemma burn_balances_self {s s' : ERC20.State} {u : Addr} {amt : ℕ}
    (hb : ERC20.burn s u amt = some s') :
    s'.balances u = s.balances u - amt := by
  unfold ERC20.burn at hb
  split at hb
  · simp at hb
  · simp only [Option.some.injEq] at hb
    rw [← hb]
    show (s.balances.update u (s.balances u - amt)) u = s.balances u - amt
    rw [Finsupp.update_apply, if_pos rfl]

lemma burn_balances_other {s s' : ERC20.State} {u v : Addr} {amt : ℕ}
    (hb : ERC20.burn s u amt = some s') (h : v ≠ u) :
    s'.balances v = s.balances v := by
  unfold ERC20.burn at hb
  split at hb
  · simp at hb
  · simp only [Option.some.injEq] at hb
    rw [← hb]
    show (s.balances.update u (s.balances u - amt)) v = s.balances v
    rw [Finsupp.update_apply, if_neg h]

/-! ## Conversion-formula bounds (state-level) -/

lemma supplyShareFor_bound (s : State) (d : ℕ) :
    supplyShareFor s d * (s.totalSupplyAssets + virtualSupplyAssets)
      ≤ d * (s.supplyShares.totalSupply + virtualSupplyShares) := by
  unfold supplyShareFor
  exact Nat.div_mul_le_self _ _

lemma borrowShareFor_bound (s : State) (d : ℕ) :
    d * (s.debtShares.totalSupply + virtualBorrowShares)
      ≤ borrowShareFor s d * (s.totalBorrowAssets + virtualBorrowAssets) := by
  unfold borrowShareFor
  apply ceilDiv_mul_ge
  have := virtualBorrowAssets_pos; omega

/-! ## Op-result extraction (world-level)

Each lemma turns `op w … = some (w', …)` into the corresponding
totals/shares update facts on `w'.state` plus the oracle equality
`w'.oracle = w.oracle`. -/

lemma supply_extract {w w' : World} {user : Addr} {assets shares : ℕ}
    (hsup : supply w user assets = some (w', shares)) :
    w'.state.totalSupplyAssets = w.state.totalSupplyAssets + assets ∧
    w'.state.supplyShares.totalSupply = w.state.supplyShares.totalSupply + shares ∧
    shares = supplyShareFor w.state assets ∧
    w'.oracle = w.oracle := by
  unfold supply at hsup
  split at hsup
  · simp at hsup
  · next loan' _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hsup
    obtain ⟨⟨rfl, rfl⟩, hk⟩ := hsup
    refine ⟨rfl, ?_, hk.symm, rfl⟩
    show (ERC20.mint w.state.supplyShares user (supplyShareFor w.state assets)).totalSupply
         = w.state.supplyShares.totalSupply + shares
    rw [hk, mint_totalSupply]

lemma withdraw_extract {w w' : World} {user : Addr} {shares assets : ℕ}
    (hw : withdraw w user shares = some (w', assets)) :
    w'.state.totalSupplyAssets = w.state.totalSupplyAssets - assets ∧
    w'.state.supplyShares.totalSupply = w.state.supplyShares.totalSupply - shares ∧
    assets = supplyAssetFor w.state shares ∧
    w'.oracle = w.oracle := by
  unfold withdraw at hw
  split at hw
  · simp at hw
  · next _ =>
    split at hw
    · simp at hw
    · next shares' hburn =>
      split at hw
      · simp at hw
      · next loan' _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨⟨rfl, rfl⟩, ha⟩ := hw
        refine ⟨?_, ?_, ha.symm, rfl⟩
        · rw [← ha]
        · show shares'.totalSupply = w.state.supplyShares.totalSupply - shares
          exact burn_totalSupply hburn

lemma borrow_extract
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (hb : borrow w user assets = some (w', shares)) :
    w'.state.totalBorrowAssets = w.state.totalBorrowAssets + assets ∧
    w'.state.debtShares.totalSupply = w.state.debtShares.totalSupply + shares ∧
    shares = borrowShareFor w.state assets ∧
    Healthy w' user ∧
    w'.oracle = w.oracle := by
  unfold borrow at hb
  split at hb
  · simp at hb
  · next _ =>
    split at hb
    · simp at hb
    · next loan' _ =>
      split at hb
      · next hHealth =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨⟨rfl, rfl⟩, hk⟩ := hb
        refine ⟨?_, ?_, hk.symm, ?_, rfl⟩
        · show (afterBorrow w.state user loan' assets).totalBorrowAssets
              = w.state.totalBorrowAssets + assets
          unfold afterBorrow; rfl
        · show (afterBorrow w.state user loan' assets).debtShares.totalSupply
              = w.state.debtShares.totalSupply + shares
          unfold afterBorrow
          show (ERC20.mint w.state.debtShares user (borrowShareFor w.state assets)).totalSupply
               = w.state.debtShares.totalSupply + shares
          rw [mint_totalSupply, hk]
        · exact hHealth
      · simp at hb

lemma repay_extract {w w' : World} {user : Addr} {shares assets : ℕ}
    (hr : repay w user shares = some (w', assets)) :
    w'.state.totalBorrowAssets = w.state.totalBorrowAssets - assets ∧
    w'.state.debtShares.totalSupply = w.state.debtShares.totalSupply - shares ∧
    assets = repayCost w.state shares ∧
    w'.oracle = w.oracle := by
  unfold repay at hr
  split at hr
  · simp at hr
  · next loan' _ =>
    split at hr
    · simp at hr
    · next debt' hburn =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨⟨rfl, rfl⟩, ha⟩ := hr
      refine ⟨?_, ?_, ha.symm, rfl⟩
      · rw [← ha]
      · show debt'.totalSupply = w.state.debtShares.totalSupply - shares
        exact burn_totalSupply hburn

lemma liquidate_extract
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    w'.state.totalBorrowAssets =
        w.state.totalBorrowAssets - repayCost w.state repaidShares ∧
    w'.state.debtShares.totalSupply =
        w.state.debtShares.totalSupply - repaidShares ∧
    seized = seizedFor w.state w.oracle.read repaidShares ∧
    w'.state.collateral borrower =
        w.state.collateral borrower - seized ∧
    (∀ v, v ≠ borrower → w'.state.collateral v = w.state.collateral v) ∧
    seized ≤ w.state.collateral borrower ∧
    ¬ Healthy w borrower ∧
    w'.oracle = w.oracle := by
  unfold liquidate at hl
  split at hl
  · simp at hl
  · next hUnhealthy =>
    split at hl
    · simp at hl
    · next hCol =>
      simp only [not_lt] at hCol
      split at hl
      · simp at hl
      · next loan' _ =>
        split at hl
        · simp at hl
        · next debt' hburn =>
          split at hl
          · simp at hl
          · next col' _ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hl
            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hl
            refine ⟨rfl, ?_, rfl, ?_, ?_, hCol, hUnhealthy, rfl⟩
            · exact burn_totalSupply hburn
            · show (w.state.collateral.update borrower
                      (w.state.collateral borrower -
                       seizedFor w.state w.oracle.read repaidShares)) borrower
                  = w.state.collateral borrower -
                    seizedFor w.state w.oracle.read repaidShares
              rw [Finsupp.update_apply, if_pos rfl]
            · intro v hv
              show (w.state.collateral.update borrower
                      (w.state.collateral borrower -
                       seizedFor w.state w.oracle.read repaidShares)) v
                  = w.state.collateral v
              rw [Finsupp.update_apply, if_neg hv]

lemma writeOff_extract
    {w w' : World} {borrower : Addr} (hwo : writeOff w borrower = some w') :
    w.state.collateral borrower = 0 ∧
    0 < w.state.debtShares.balances borrower ∧
    (let loss := min (repayCost w.state (w.state.debtShares.balances borrower))
                     w.state.totalBorrowAssets
     w'.state.totalBorrowAssets = w.state.totalBorrowAssets - loss ∧
     w'.state.totalSupplyAssets = w.state.totalSupplyAssets - loss) ∧
    w'.state.debtShares.totalSupply =
        w.state.debtShares.totalSupply - w.state.debtShares.balances borrower ∧
    w'.state.debtShares.balances borrower = 0 ∧
    w'.oracle = w.oracle := by
  unfold writeOff at hwo
  split at hwo
  · simp at hwo
  · next hCol =>
    push Not at hCol
    split at hwo
    · simp at hwo
    · next hSh =>
      have hSh_pos : 0 < w.state.debtShares.balances borrower := Nat.pos_of_ne_zero hSh
      split at hwo
      · simp at hwo
      · next debt' hburn =>
        simp only [Option.some.injEq] at hwo
        rw [← hwo]
        refine ⟨hCol, hSh_pos, ⟨rfl, rfl⟩, ?_, ?_, rfl⟩
        · show debt'.totalSupply =
              w.state.debtShares.totalSupply - w.state.debtShares.balances borrower
          exact burn_totalSupply hburn
        · -- debt'.balances borrower = 0 because we burned exactly its balance.
          unfold ERC20.burn at hburn
          split at hburn
          · simp at hburn
          · simp only [Option.some.injEq] at hburn
            rw [← hburn]
            show (w.state.debtShares.balances.update borrower
                    (w.state.debtShares.balances borrower -
                     w.state.debtShares.balances borrower)) borrower = 0
            rw [Finsupp.update_apply, if_pos rfl]
            omega

/-! ## Step-result extraction (world-level) -/

lemma step_userSupply_some {w w' : World} {u : Addr} {amt : ℕ}
    (hstep : step (.userSupply u amt) w = some w') :
    ∃ sh, supply w u amt = some (w', sh) := by
  simp only [step, Option.map_eq_some_iff] at hstep
  obtain ⟨⟨_, sh⟩, hsup, hp⟩ := hstep
  cases hp; exact ⟨sh, hsup⟩

lemma step_userWithdraw_some {w w' : World} {u : Addr} {sh : ℕ}
    (hstep : step (.userWithdraw u sh) w = some w') :
    ∃ a, withdraw w u sh = some (w', a) := by
  simp only [step, Option.map_eq_some_iff] at hstep
  obtain ⟨⟨_, a⟩, hwd, hp⟩ := hstep
  cases hp; exact ⟨a, hwd⟩

lemma step_userSupplyCollateral_some {w w' : World} {u : Addr} {c : ℕ}
    (hstep : step (.userSupplyCollateral u c) w = some w') :
    supplyCollateral w u c = some w' := by
  simp only [step] at hstep; exact hstep

lemma step_userWithdrawCollateral_some
    {w w' : World} {u : Addr} {c : ℕ}
    (hstep : step (.userWithdrawCollateral u c) w = some w') :
    withdrawCollateral w u c = some w' := by
  simp only [step] at hstep; exact hstep

lemma step_userBorrow_some {w w' : World} {u : Addr} {amt : ℕ}
    (hstep : step (.userBorrow u amt) w = some w') :
    ∃ sh, borrow w u amt = some (w', sh) := by
  simp only [step, Option.map_eq_some_iff] at hstep
  obtain ⟨⟨_, sh⟩, hb, hp⟩ := hstep
  cases hp; exact ⟨sh, hb⟩

lemma step_userRepay_some {w w' : World} {u : Addr} {sh : ℕ}
    (hstep : step (.userRepay u sh) w = some w') :
    ∃ a, repay w u sh = some (w', a) := by
  simp only [step, Option.map_eq_some_iff] at hstep
  obtain ⟨⟨_, a⟩, hr, hp⟩ := hstep
  cases hp; exact ⟨a, hr⟩

lemma step_userLiquidate_some {w w' : World} {lq br : Addr} {sh : ℕ}
    (hstep : step (.userLiquidate lq br sh) w = some w') :
    ∃ seized, liquidate w lq br sh = some (w', seized) := by
  simp only [step, Option.map_eq_some_iff] at hstep
  obtain ⟨⟨_, seized⟩, hl, hp⟩ := hstep
  cases hp; exact ⟨seized, hl⟩

lemma step_userWriteOff_some {w w' : World} {br : Addr}
    (hstep : step (.userWriteOff br) w = some w') :
    writeOff w br = some w' := by
  simp only [step] at hstep; exact hstep

lemma step_envAccrueInt_some {w w' : World} {Δ : ℕ}
    (hstep : step (.envAccrueInt Δ) w = some w') :
    w' = accrueInterest w Δ := by
  simp only [step, Option.some.injEq] at hstep
  exact hstep.symm

lemma step_envPriceTick_some {w w' : World} {p' : OraclePrice}
    (hstep : step (.envPriceTick p') w = some w') :
    w' = ⟨w.state, Oracle.update w.oracle p'⟩ := by
  simp only [step, Option.some.injEq] at hstep
  exact hstep.symm

/-! ## Zero-debt-shares simplifications -/

/-- Zero debt shares imply zero `debtOf`. -/
lemma debtOf_eq_zero_of_debtShares_balance_eq_zero
    {s : State} {u : Addr} (hZero : s.debtShares.balances u = 0) :
    debtOf s u = 0 := by
  unfold debtOf repayCost Util.ceilDiv
  rw [hZero, Nat.zero_mul]
  have hvBS : 0 < virtualBorrowShares := virtualBorrowShares_pos
  rw [Nat.div_eq_of_lt (by omega)]

/-- A zero-debt position is healthy.  In the new two-floor form, no
oracle-price nonnegativity hypothesis is needed: the conclusion
`debtOf ≤ maxBorrow.mantissa` reduces to `0 ≤ maxBorrow.mantissa`,
which is true for any `Fixed 0` value. -/
lemma healthy_of_debtShares_balance_zero
    {w : World} {u : Addr}
    (hZero : w.state.debtShares.balances u = 0) :
    Healthy w u := by
  have hDebtZero := debtOf_eq_zero_of_debtShares_balance_eq_zero hZero
  unfold Healthy HealthyOnState
  rw [hDebtZero]
  exact Nat.zero_le _

/-! ## Liquidation post-state shape -/

/-- A successful liquidation burns exactly `repaidShares` of the
borrower's debt-share balance. -/
lemma liquidate_burns_repaidShares
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    w'.state.debtShares.balances borrower =
        w.state.debtShares.balances borrower - repaidShares := by
  unfold liquidate at hl
  split at hl
  · simp at hl
  · split at hl
    · simp at hl
    · split at hl
      · simp at hl
      · next loan' _ =>
        split at hl
        · simp at hl
        · next debt' hburn =>
          split at hl
          · simp at hl
          · next col' _ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, _⟩ := hl
            exact burn_balances_self hburn

/-- A successful liquidation leaves non-borrower debt-share balances
unchanged. -/
lemma liquidate_debtShares_balances_other
    {w w' : World} {liquidator borrower u : Addr} {repaidShares seized : ℕ}
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized))
    (hu : u ≠ borrower) :
    w'.state.debtShares.balances u = w.state.debtShares.balances u := by
  unfold liquidate at hl
  split at hl
  · simp at hl
  · split at hl
    · simp at hl
    · split at hl
      · simp at hl
      · next loan' _ =>
        split at hl
        · simp at hl
        · next debt' hburn =>
          split at hl
          · simp at hl
          · next col' _ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, _⟩ := hl
            unfold ERC20.burn at hburn
            split at hburn
            · simp at hburn
            · simp only [Option.some.injEq] at hburn
              rw [← hburn]
              show (w.state.debtShares.balances.update borrower
                      (w.state.debtShares.balances borrower - repaidShares)) u
                  = w.state.debtShares.balances u
              rw [Finsupp.update_apply, if_neg hu]

/-- A successful liquidation can only burn shares the borrower has. -/
lemma liquidate_repaidShares_le_borrower_balance
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    repaidShares ≤ w.state.debtShares.balances borrower := by
  unfold liquidate at hl
  split at hl
  · simp at hl
  · split at hl
    · simp at hl
    · split at hl
      · simp at hl
      · next loan' _ =>
        split at hl
        · simp at hl
        · next debt' hburn =>
          split at hl
          · simp at hl
          · simp only [Option.some.injEq, Prod.mk.injEq] at hl
            unfold ERC20.burn at hburn
            split at hburn
            · simp at hburn
            · next h => simp only [not_lt] at h; exact h

/-! ## Lower bound for `seizedFor`

The new `seizedFor` is defined via `Fixed.divCeil`; this lower-bound
lemma is the dual of `seizedFor_mul_price_le_cost_bonus_add_price` and
is the form used by proofs about liquidator profit / debt evolution. -/

/-- `seizedFor · price ≥ repayCost · bonus`.  The ceil-rounded
liquidator-favouring leg always pays at least the exact bonus value. -/
lemma cost_bonus_le_seizedFor_mul_price
    {s : State} {p : OraclePrice} {repaidShares : ℕ}
    (hp : (0 : OraclePrice) < p) :
    (repayCost s repaidShares : ℚ) * liquidationIncentiveFactor_q
      ≤ (seizedFor s p repaidShares : ℚ) * p.toRat := by
  unfold seizedFor
  rw [if_pos hp]
  have hp : 0 < p.mantissa := hp
  -- Use the divCeil lower bound: x.toRat / y.toRat ≤ divCeil.toRat.
  have h_divCeil :=
    Fixed.divCeilAt_toRat_ge
      ((Fixed.ofNat (repayCost s repaidShares)).mul liquidationIncentiveFactor)
      p 0 (by omega) hp
  -- divCeil's input is `(repayCost.ofNat).mul bonus : Fixed 18`.
  -- Its toRat is `repayCost * bonus.toRat` (after unfold).
  have h_input_toRat :
      ((Fixed.ofNat (repayCost s repaidShares)).mul
          liquidationIncentiveFactor).toRat
        = (repayCost s repaidShares : ℚ) * liquidationIncentiveFactor_q := by
    rw [Fixed.toRat_mul, Fixed.toRat_ofNat]
  rw [h_input_toRat] at h_divCeil
  -- divCeil's toRat at target=0 is just its mantissa (as ℚ).
  have h_out_toRat :
      (Fixed.divCeilAt ((Fixed.ofNat (repayCost s repaidShares)).mul
          liquidationIncentiveFactor) p 0 (by omega)).toRat
        = ((Fixed.divCeilAt ((Fixed.ofNat (repayCost s repaidShares)).mul
              liquidationIncentiveFactor) p 0 (by omega)).mantissa : ℚ) := by
    show ((Fixed.divCeilAt _ p 0 _).mantissa : ℚ) / (10 : ℚ) ^ 0
        = ((Fixed.divCeilAt _ p 0 _).mantissa : ℚ)
    simp
  rw [h_out_toRat] at h_divCeil
  -- Now h_divCeil : repayCost * bonus_q / p.toRat ≤ seized
  -- Multiply both sides by p.toRat > 0.
  have hp_toRat : (0 : ℚ) < p.toRat := by
    show (0 : ℚ) < ((p.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ 36
    apply div_pos
    · exact_mod_cast hp
    · positivity
  have h_mul := mul_le_mul_of_nonneg_right h_divCeil (le_of_lt hp_toRat)
  rw [div_mul_cancel₀ _ (ne_of_gt hp_toRat)] at h_mul
  exact h_mul

/-! ## Rounding bounds for `repayCost` and `seizedFor` -/

/-- `repayCost` is at most the exact share value plus one loan-asset
unit (the ceil rounding excess). -/
lemma repayCost_le_shareValue_add_one
    (s : State) (repaidShares : ℕ) :
    (repayCost s repaidShares : ℚ)
      ≤ (repaidShares : ℚ)
          * ((s.totalBorrowAssets : ℚ) + virtualBorrowAssets)
          / ((s.debtShares.totalSupply : ℚ) + virtualBorrowShares)
        + 1 := by
  set R : ℕ := s.totalBorrowAssets + virtualBorrowAssets
  set S : ℕ := s.debtShares.totalSupply + virtualBorrowShares
  have hS_pos : 0 < S := by
    dsimp [S]
    have := virtualBorrowShares_pos
    omega
  have hCostS_nat :
      repayCost s repaidShares * S ≤ repaidShares * R + S := by
    have h :
        repayCost s repaidShares * S ≤ repaidShares * R + S - 1 := by
      dsimp [R, S]
      unfold repayCost Util.ceilDiv
      exact Nat.div_mul_le_self _ _
    omega
  have hCostS :
      (repayCost s repaidShares : ℚ) * (S : ℚ)
        ≤ (repaidShares : ℚ) * (R : ℚ) + (S : ℚ) := by
    have hcast :
        ((repayCost s repaidShares * S : ℕ) : ℚ)
          ≤ ((repaidShares * R + S : ℕ) : ℚ) := by
      exact_mod_cast hCostS_nat
    push_cast at hcast
    simpa [mul_assoc] using hcast
  have hS_pos_q : (0 : ℚ) < (S : ℚ) := by
    exact_mod_cast hS_pos
  have hR :
      (R : ℚ) = (s.totalBorrowAssets : ℚ) + virtualBorrowAssets := by
    dsimp [R]
    push_cast
    ring
  have hS :
      (S : ℚ) = (s.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    dsimp [S]
    push_cast
    ring
  rw [← hR, ← hS]
  have hmul :
      (repayCost s repaidShares : ℚ) * (S : ℚ)
        ≤ ((repaidShares : ℚ) * (R : ℚ) / (S : ℚ) + 1) * (S : ℚ) := by
    have hne : (S : ℚ) ≠ 0 := ne_of_gt hS_pos_q
    rw [add_mul, div_mul_cancel₀ _ hne, one_mul]
    exact hCostS
  exact le_of_mul_le_mul_right hmul hS_pos_q

/-- `seizedFor` is at most the exact bonus repayment plus one collateral
unit, expressed in loan-asset value units (the ceil rounding excess
after multiplying by `p`).

In the fixed-point reformulation `seizedFor s p k` is
`ceilDiv (repayCost s k · bonus.mantissa · 10^18) p.mantissa` (mantissa
form), and the inequality is the standard `ceilDiv a b · b ≤ a + b`
bound divided by `10^36`. -/
lemma seizedFor_mul_price_le_cost_bonus_add_price
    {s : State} {p : OraclePrice} {repaidShares : ℕ}
    (hp : (0 : OraclePrice) < p) :
    (seizedFor s p repaidShares : ℚ) * p.toRat
      ≤ (repayCost s repaidShares : ℚ) * liquidationIncentiveFactor_q + p.toRat := by
  unfold seizedFor
  rw [if_pos hp]
  have hp : 0 < p.mantissa := hp
  set m : ℕ := repayCost s repaidShares with hm_def
  set b : ℕ := liquidationIncentiveFactor.mantissa with hb_def
  set pm : ℕ := p.mantissa with hpm_def
  -- New seizedFor's toNat is `ceilDiv (m * b * 10^18) pm`.
  have hsz_mantissa :
      ((Fixed.divCeilAt
            ((Fixed.ofNat m).mul liquidationIncentiveFactor) p 0
            (by omega)).toNat : ℕ)
        = Util.ceilDiv (m * b * 10 ^ 18) pm := by
    simp [Fixed.toNat, Fixed.divCeilAt_mantissa, Fixed.mul_mantissa, Fixed.ofNat_mantissa,
          hb_def, hpm_def]
  rw [hsz_mantissa]
  -- Nat ceil-bound: `ceilDiv (m·b·10^18) pm · pm ≤ m·b·10^18 + pm`.
  have hpm_pos : 0 < pm := hp
  have h_nat :
      Util.ceilDiv (m * b * 10 ^ 18) pm * pm ≤ m * b * 10 ^ 18 + pm := by
    unfold Util.ceilDiv
    have h_div_mul : (m * b * 10 ^ 18 + pm - 1) / pm * pm
                       ≤ m * b * 10 ^ 18 + pm - 1 :=
      Nat.div_mul_le_self _ _
    omega
  have h_nat_q :
      ((Util.ceilDiv (m * b * 10 ^ 18) pm : ℕ) : ℚ) * (pm : ℚ)
        ≤ (m : ℚ) * (b : ℚ) * (10 : ℚ) ^ 18 + (pm : ℚ) := by
    exact_mod_cast h_nat
  -- Unfold the ℚ-side terms.
  have hp_toRat : p.toRat = (pm : ℚ) / (10 : ℚ) ^ 36 := rfl
  have hbonus_toRat : liquidationIncentiveFactor_q = (b : ℚ) / (10 : ℚ) ^ 18 := rfl
  rw [hp_toRat, hbonus_toRat]
  have hpm_pos_q : (0 : ℚ) < (pm : ℚ) := by exact_mod_cast hpm_pos
  have h10_36 : (0 : ℚ) < (10 : ℚ) ^ 36 := by positivity
  have h10_18 : (0 : ℚ) < (10 : ℚ) ^ 18 := by positivity
  have h10_pow : (10 : ℚ) ^ 36 = (10 : ℚ) ^ 18 * (10 : ℚ) ^ 18 := by
    rw [← pow_add]
  -- Clear the `10^36` denominator on the LHS via mul_div_assoc' + div_le_iff.
  rw [mul_div_assoc', div_le_iff₀ h10_36]
  -- Goal: ((ceilDiv ... : ℕ) : ℚ) * pm ≤ (m * (b / 10^18) + pm / 10^36) * 10^36
  have h_rhs :
      ((m : ℚ) * ((b : ℚ) / (10 : ℚ) ^ 18) + (pm : ℚ) / (10 : ℚ) ^ 36) * (10 : ℚ) ^ 36
        = (m : ℚ) * (b : ℚ) * (10 : ℚ) ^ 18 + (pm : ℚ) := by
    rw [h10_pow]; field_simp
  rw [h_rhs]
  exact h_nat_q

/-! ## Rate-monotonicity helpers for `AssetCovered` post-state

The two abstract ℚ-rate-monotonicity lemmas behind partial liquidation
and borrow, in multiplicative form. -/

/-- After a debt-share burn (`repay` or partial `liquidate`): if the
new per-share rate `(R - cost) / (S - burned)` is no larger than the
old `R / S` (witnessed by `burned · R ≤ cost · S`), and the user's new
balance is no larger than their old balance, then the per-user
multiplicative `AssetCovered` inequality is preserved. -/
lemma assetCovered_after_burn_rate_le
    {Yold Ynew C p R S cost burned : ℚ}
    (hAC : Yold * R ≤ C * p * S)
    (hYnew_le : Ynew ≤ Yold)
    (hYnew_nn : 0 ≤ Ynew)
    (hR_nn : 0 ≤ R)
    (hS_pos : 0 < S)
    (hS_burn_nn : 0 ≤ S - burned)
    (hrate : burned * R ≤ cost * S) :
    Ynew * (R - cost) ≤ C * p * (S - burned) := by
  have hRateRearr : (R - cost) * S ≤ R * (S - burned) := by
    nlinarith
  have h1 :
      Ynew * ((R - cost) * S)
        ≤ Ynew * (R * (S - burned)) :=
    mul_le_mul_of_nonneg_left hRateRearr hYnew_nn
  have hRS_nn : 0 ≤ R * (S - burned) := mul_nonneg hR_nn hS_burn_nn
  have h2 :
      Ynew * (R * (S - burned))
        ≤ Yold * (R * (S - burned)) :=
    mul_le_mul_of_nonneg_right hYnew_le hRS_nn
  have h3 :
      (Yold * R) * (S - burned)
        ≤ (C * p * S) * (S - burned) :=
    mul_le_mul_of_nonneg_right hAC hS_burn_nn
  by_contra hnot
  push Not at hnot
  have hbad :
      (C * p * (S - burned)) * S < (Ynew * (R - cost)) * S :=
    mul_lt_mul_of_pos_right hnot hS_pos
  nlinarith

/-- After minting new debt shares during `borrow`: if the new
per-share rate `(R + assets) / (S + minted)` is no larger than the
old `R / S` (witnessed by `assets · S ≤ minted · R`), the per-user
multiplicative `AssetCovered` inequality is preserved at any user
whose balance does not change. -/
lemma assetCovered_after_borrow_rate_le
    {Y C p R S assets minted : ℚ}
    (hAC : Y * R ≤ C * p * S)
    (hY_nn : 0 ≤ Y)
    (hS_pos : 0 < S)
    (hS_minted_nn : 0 ≤ S + minted)
    (hrate : assets * S ≤ minted * R) :
    Y * (R + assets) ≤ C * p * (S + minted) := by
  have hRateRearr : (R + assets) * S ≤ R * (S + minted) := by
    nlinarith
  have h1 :
      Y * ((R + assets) * S) ≤ Y * (R * (S + minted)) :=
    mul_le_mul_of_nonneg_left hRateRearr hY_nn
  have h2 :
      (Y * R) * (S + minted) ≤ (C * p * S) * (S + minted) :=
    mul_le_mul_of_nonneg_right hAC hS_minted_nn
  by_contra hnot
  push Not at hnot
  have hbad :
      (C * p * (S + minted)) * S < (Y * (R + assets)) * S :=
    mul_lt_mul_of_pos_right hnot hS_pos
  nlinarith

/-! ## Liquidation bonus formula theorems

Concrete mantissa / `toRat` values for `MAX_LIQUIDATION_INCENTIVE_FACTOR`
and `LIQUIDATION_CURSOR`, plus the two structural theorems
`bonus ≥ 1` and `bonus · lltv < 1` derived from the Morpho formula
(`morphoLiquidationIncentiveFactor` in `Defs.States`) together
with `lltv < 1`.

### Constants — concrete ℕ mantissas and ℚ values

The mantissas reduce via kernel computation (`Fixed.ofRat 1.15` on
`Wad` = `⟨⌊1.15 · 10^18⌋.toNat⟩` = `⟨115·10^16⟩`).  `native_decide`
is fast for `10^18`-sized literals; falls back to `decide` for cases
where the kernel cooperates. -/

@[simp] theorem MAX_LIF_mantissa :
    MAX_LIQUIDATION_INCENTIVE_FACTOR.mantissa = 115 * 10 ^ 16 := by native_decide

@[simp] theorem LIQ_CURSOR_mantissa :
    LIQUIDATION_CURSOR.mantissa = 3 * 10 ^ 17 := by native_decide

theorem MAX_LIF_toRat : MAX_LIQUIDATION_INCENTIVE_FACTOR.toRat = 23 / 20 := by
  unfold Fixed.toRat
  rw [MAX_LIF_mantissa]
  norm_num

theorem LIQ_CURSOR_toRat : LIQUIDATION_CURSOR.toRat = 3 / 10 := by
  unfold Fixed.toRat
  rw [LIQ_CURSOR_mantissa]
  norm_num

theorem LIQ_CURSOR_mantissa_lt_WAD : LIQUIDATION_CURSOR.mantissa < 10 ^ 18 := by
  rw [LIQ_CURSOR_mantissa]; norm_num

/-! ### Bonus is `≥ 1` — easy direction -/

private lemma scaledCursor_mantissa_le :
    (Fixed.mulFloor LIQUIDATION_CURSOR (1 - lltv) : Wad).mantissa
      ≤ LIQUIDATION_CURSOR.mantissa := by
  -- `(mulFloor x y).mantissa = x.mantissa * y.mantissa / 10^s` (same-scale).
  -- `y = 1 - lltv` has `mantissa ≤ 10^18`, so the result mantissa
  -- ≤ `x.mantissa * 10^18 / 10^18 = x.mantissa`.
  rw [Fixed.mulFloor_mantissa]
  have h_y : (1 - lltv : Wad).mantissa ≤ 10 ^ 18 := by
    show 10 ^ 18 - lltv.mantissa ≤ 10 ^ 18
    omega
  calc LIQUIDATION_CURSOR.mantissa * (1 - lltv : Wad).mantissa / 10 ^ 18
      ≤ LIQUIDATION_CURSOR.mantissa * 10 ^ 18 / 10 ^ 18 := by
        apply Nat.div_le_div_right
        exact Nat.mul_le_mul_left _ h_y
    _ = LIQUIDATION_CURSOR.mantissa := by
        rw [Nat.mul_div_cancel _ (by positivity : 0 < 10 ^ 18)]

private lemma oneMinusScaled_mantissa_pos :
    0 < (1 - Fixed.mulFloor LIQUIDATION_CURSOR (1 - lltv) : Wad).mantissa := by
  show 0 < 10 ^ 18 - _
  have h := scaledCursor_mantissa_le
  have h_lt : LIQUIDATION_CURSOR.mantissa < 10 ^ 18 := LIQ_CURSOR_mantissa_lt_WAD
  omega

private lemma oneMinusScaled_mantissa_le :
    (1 - Fixed.mulFloor LIQUIDATION_CURSOR (1 - lltv) : Wad).mantissa
      ≤ 10 ^ 18 := by
  show 10 ^ 18 - _ ≤ 10 ^ 18
  omega

private lemma floor_div_mantissa_ge_WAD :
    10 ^ 18 ≤ (Fixed.divFloor (1 : Wad)
                (1 - Fixed.mulFloor LIQUIDATION_CURSOR (1 - lltv))).mantissa := by
  rw [Fixed.divFloor_mantissa]
  -- mantissa = (1 : Wad).mantissa * 10^18 / oneMinusScaled.mantissa
  --         = 10^18 * 10^18 / oneMinusScaled.mantissa
  set omS_m : Nat := (1 - Fixed.mulFloor LIQUIDATION_CURSOR (1 - lltv) : Wad).mantissa
  have h_omS_pos : 0 < omS_m := oneMinusScaled_mantissa_pos
  have h_omS_le : omS_m ≤ 10 ^ 18 := oneMinusScaled_mantissa_le
  show 10 ^ 18 ≤ (1 : Wad).mantissa * 10 ^ 18 / omS_m
  rw [Fixed.one_mantissa]
  -- Goal: 10^18 ≤ 10^18 * 10^18 / omS_m
  apply (Nat.le_div_iff_mul_le h_omS_pos).mpr
  -- 10^18 * omS_m ≤ 10^18 * 10^18
  exact Nat.mul_le_mul_left _ h_omS_le

theorem liquidationIncentiveFactor_q_ge_one : 1 ≤ liquidationIncentiveFactor_q := by
  unfold liquidationIncentiveFactor_q liquidationIncentiveFactor morphoLiquidationIncentiveFactor
  rw [Fixed.toRat_min]
  -- Both arguments of `min` have toRat ≥ 1.
  apply le_min
  · rw [MAX_LIF_toRat]; norm_num
  · -- floor_div.toRat ≥ 1 from `mantissa ≥ 10^18`.
    show 1 ≤ (Fixed.divFloor (1 : Wad) _).toRat
    unfold Fixed.toRat
    rw [le_div_iff₀ (by positivity)]
    have h := floor_div_mantissa_ge_WAD
    have hq : ((10 ^ 18 : ℕ) : ℚ)
            ≤ (((Fixed.divFloor (1 : Wad)
                  (1 - Fixed.mulFloor LIQUIDATION_CURSOR (1 - lltv))
                  ).mantissa : ℕ) : ℚ) := by
      exact_mod_cast h
    push_cast at hq
    linarith

theorem liquidationIncentiveFactor_q_nonneg : 0 ≤ liquidationIncentiveFactor_q := by
  have := liquidationIncentiveFactor_q_ge_one; linarith

/-! ### Structural constraint `bonus · lltv < 1` — the hard direction

A **theorem** derived from the Morpho formula + `lltv < 1`.
Two cases:

- **Case A** (`MAX_LIF ≤ formula_floor`): `bonus = MAX_LIF`.  From
  `MAX_LIF ≤ formula_floor ≤ 1 / oneMinusScaled` and
  `oneMinusScaled ≥ 0.7 + 0.3 · lltv`, we get
  `lltv ≤ (1/MAX_LIF − 0.7)/0.3 ≈ 0.5652`.  Then
  `bonus · lltv = MAX_LIF · lltv ≤ MAX_LIF · 0.5652 ≈ 0.65 < 1`.

- **Case B** (`formula_floor < MAX_LIF`): `bonus = formula_floor ≤
  1/(0.7 + 0.3·lltv)`.  Then `bonus · lltv ≤ lltv/(0.7 + 0.3·lltv) <
  1` iff `lltv < 1` (which is the axiom).
-/
theorem liquidationIncentiveFactor_q_lltv_q_lt_one :
    liquidationIncentiveFactor_q * lltv_q < 1 := by
  -- Convenient ℚ aliases.
  set pq : ℚ := lltv_q with hpq_def
  set Mq : ℚ := MAX_LIQUIDATION_INCENTIVE_FACTOR.toRat with hMq_def
  set Qq : ℚ := LIQUIDATION_CURSOR.toRat with hQq_def
  have hMq : Mq = 23 / 20 := MAX_LIF_toRat
  have hQq : Qq = 3 / 10 := LIQ_CURSOR_toRat
  have hpq_pos : 0 < pq := lltv_q_pos
  have hpq_lt_one : pq < 1 := lltv_q_lt_one
  have hpq_nn : (0 : ℚ) ≤ pq := hpq_pos.le
  -- Step 1: `(1 - lltv).toRat = 1 - pq`.
  have h_le_one : lltv ≤ (1 : Wad) := by
    have h : lltv.mantissa < (1 : Wad).mantissa := lltv_lt_one
    exact h.le
  have h_omll : (1 - lltv : Wad).toRat = 1 - pq := by
    rw [Fixed.toRat_sub_of_le h_le_one, Fixed.toRat_one]
  -- Step 2: `scaled.toRat ≤ Qq · (1 - pq)`.
  set scaled : Wad := Fixed.mulFloor LIQUIDATION_CURSOR (1 - lltv)
  have h_scaled_le_q : scaled.toRat ≤ Qq * (1 - pq) := by
    have := Fixed.mulFloor_toRat_le LIQUIDATION_CURSOR (1 - lltv)
    rw [h_omll] at this
    exact this
  have h_scaled_nn : 0 ≤ scaled.toRat := Fixed.toRat_nonneg _
  -- Step 3: `oneMinusScaled.toRat ≥ 1 - Qq · (1 - pq) = (1-Qq) + Qq·pq`.
  set omS : Wad := 1 - scaled
  have h_omS : omS.toRat = 1 - scaled.toRat := by
    rw [Fixed.toRat_sub_of_le, Fixed.toRat_one]
    -- Need: scaled ≤ 1 (as Wad), i.e. scaled.mantissa ≤ 10^18.
    show scaled.mantissa ≤ (1 : Wad).mantissa
    have h_le_cursor : scaled.mantissa ≤ LIQUIDATION_CURSOR.mantissa :=
      scaledCursor_mantissa_le
    have h_cursor_lt : LIQUIDATION_CURSOR.mantissa < 10 ^ 18 :=
      LIQ_CURSOR_mantissa_lt_WAD
    show _ ≤ 10 ^ 18
    omega
  have h_omS_ge : (1 - Qq) + Qq * pq ≤ omS.toRat := by
    have : 1 - Qq * (1 - pq) = (1 - Qq) + Qq * pq := by ring
    rw [h_omS]; linarith [h_scaled_le_q]
  have h_omS_pos : 0 < omS.toRat := by
    have h_omS_nn := h_omS_ge
    have hQq_pos : 0 < Qq := by rw [hQq]; norm_num
    have hQq_lt_one : Qq < 1 := by rw [hQq]; norm_num
    nlinarith [hQq_pos, hQq_lt_one, hpq_pos]
  have h_omS_le_one : omS.toRat ≤ 1 := by
    rw [h_omS]; linarith [h_scaled_nn]
  -- Step 4: `floor_div.toRat ≤ 1/omS.toRat ≤ 1/((1-Qq)+Qq·pq)`.
  set floor_div : Wad := Fixed.divFloor (1 : Wad) omS
  have h_omS_mantissa_pos : 0 < omS.mantissa := oneMinusScaled_mantissa_pos
  have h_div_le_q : floor_div.toRat ≤ (1 : Wad).toRat / omS.toRat :=
    Fixed.divFloor_toRat_le (1 : Wad) omS h_omS_mantissa_pos
  rw [Fixed.toRat_one] at h_div_le_q
  -- Step 5: `bonus.toRat = min Mq floor_div.toRat`.
  show (min MAX_LIQUIDATION_INCENTIVE_FACTOR floor_div).toRat * pq < 1
  rw [Fixed.toRat_min]
  -- Step 6: case-split on `min Mq floor_div.toRat` outcome.
  -- We compute concrete bounds with Mq = 23/20, Qq = 3/10.
  have hMq_pos : 0 < Mq := by rw [hMq]; norm_num
  have hQq_pos : 0 < Qq := by rw [hQq]; norm_num
  rcases le_total Mq floor_div.toRat with hcase | hcase
  · -- Case A: min = Mq.  Use Mq ≤ floor_div.toRat ≤ 1/omS.toRat to bound pq.
    rw [min_eq_left hcase]
    -- From `Mq ≤ floor_div.toRat ≤ 1/omS.toRat`: `omS.toRat ≤ 1/Mq`.
    have h_omS_le_inv : omS.toRat ≤ 1 / Mq := by
      have h_chain : Mq ≤ 1 / omS.toRat := le_trans hcase h_div_le_q
      rw [le_div_iff₀ h_omS_pos] at h_chain
      rw [le_div_iff₀ hMq_pos]
      linarith
    -- Combined with `(1-Qq) + Qq·pq ≤ omS.toRat`: `(1-Qq) + Qq·pq ≤ 1/Mq`.
    have h_bound : (1 - Qq) + Qq * pq ≤ 1 / Mq := le_trans h_omS_ge h_omS_le_inv
    -- With Mq = 23/20 and Qq = 3/10, `1/Mq = 20/23` and we get
    -- `pq ≤ (20/23 - 7/10) / (3/10) = 13/23`.  Then `Mq · pq ≤ 13/20 < 1`.
    rw [hMq, hQq] at h_bound
    have h_pq : pq ≤ 13 / 23 := by
      rw [show (1 : ℚ) / (23/20) = 20/23 by norm_num] at h_bound
      linarith
    have h_final : (23 / 20 : ℚ) * pq ≤ 13 / 20 := by
      have : (23/20 : ℚ) * (13/23) = 13/20 := by norm_num
      have h_mul : (23 / 20 : ℚ) * pq ≤ (23/20) * (13/23) :=
        mul_le_mul_of_nonneg_left h_pq (by norm_num : (0 : ℚ) ≤ 23/20)
      linarith
    rw [hMq]; linarith
  · -- Case B: min = floor_div.toRat.  `floor_div.toRat ≤ 1/omS.toRat ≤ 1/((1-Qq)+Qq·pq)`.
    rw [min_eq_right hcase]
    -- omS.toRat ≥ (1-Qq) + Qq·pq > 0, so dividing flips: 1/omS.toRat ≤ 1/((1-Qq)+Qq·pq).
    have h_denom_pos : 0 < (1 - Qq) + Qq * pq := by
      rw [hQq]; linarith [hpq_pos]
    have h_inv_le : 1 / omS.toRat ≤ 1 / ((1 - Qq) + Qq * pq) :=
      one_div_le_one_div_of_le h_denom_pos h_omS_ge
    have h_div_le_formula : floor_div.toRat ≤ 1 / ((1 - Qq) + Qq * pq) :=
      le_trans h_div_le_q h_inv_le
    -- `bonus · pq ≤ pq / ((1-Qq) + Qq·pq)`, which is `< 1` iff `pq < (1-Qq) + Qq·pq ⟺ pq < 1`.
    have h_mul : floor_div.toRat * pq ≤ (1 / ((1 - Qq) + Qq * pq)) * pq :=
      mul_le_mul_of_nonneg_right h_div_le_formula hpq_nn
    have h_simplify : (1 / ((1 - Qq) + Qq * pq)) * pq = pq / ((1 - Qq) + Qq * pq) := by
      rw [one_div, div_eq_mul_inv, mul_comm]
    rw [h_simplify] at h_mul
    -- pq / ((1-Qq) + Qq·pq) < 1 ⟺ pq < (1-Qq) + Qq·pq ⟺ (1-Qq)·pq < (1-Qq) ⟺ pq < 1
    have h_lt : pq / ((1 - Qq) + Qq * pq) < 1 := by
      rw [div_lt_one h_denom_pos]
      have hQq_lt_one : Qq < 1 := by rw [hQq]; norm_num
      nlinarith [hpq_lt_one, hQq_lt_one]
    linarith

end Market
