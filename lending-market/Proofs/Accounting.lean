import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas

/-!
# Lending Market — `MarketAccounting` preservation

`MarketAccounting w` (defined in `Defs.Invariants`) bundles three accounting
facts on the protocol's books:

- `borrowBacked`: `totalBorrowAssets ≤ totalSupplyAssets`.  A
  totals-arithmetic invariant, not solvency in the cash-flow sense.
- `collateralBacked`:
  `Σ_u state.collateral u ≤ state.collateralAsset.balances marketAddress`.
  Stated as a `Finsupp.sum` because the point-wise variant fails
  preservation through `withdrawCollateral` (other users' entries
  don't shrink with the market's balance).
- `marketNotBorrower`: `state.collateral marketAddress = 0`.  Carried
  as an auxiliary fact so that ops routing through the market itself
  (which become ERC-20 self-transfers — balance-neutral, while the
  `state.collateral` ledger update is user-additive) can't break
  `collateralBacked`.  The `user ≠ marketAddress` guard added to
  `supplyCollateral` is what makes this preservable.

## Main theorem
- `step_preserves_marketAccounting`
-/

namespace Market

/-! ## `Finsupp.sum` after a single-entry update

Two specializations of `Finsupp.sum_update_add` to the additive map
`fun _ x => x` over ℕ, used throughout `*_preserves_marketAccounting`. -/

private lemma sum_update_add_self (f : Addr →₀ ℕ) (u : Addr) (c : ℕ) :
    (f.update u (f u + c)).sum (fun _ x => x)
      = f.sum (fun _ x => x) + c := by
  have h := Finsupp.sum_update_add f u (f u + c) (fun _ x => x)
    (fun _ => rfl) (fun _ _ _ => rfl)
  dsimp only at h
  omega

private lemma sum_update_sub_self (f : Addr →₀ ℕ) (u : Addr) (c : ℕ)
    (hc : c ≤ f u) :
    (f.update u (f u - c)).sum (fun _ x => x)
      = f.sum (fun _ x => x) - c := by
  have h := Finsupp.sum_update_add f u (f u - c) (fun _ x => x)
    (fun _ => rfl) (fun _ _ _ => rfl)
  dsimp only at h
  omega

/-! ## Per-op `MarketAccounting` preservation lemmas (private) -/

private lemma supply_preserves_marketAccounting
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (h : MarketAccounting w) (hsup : supply w user assets = some (w', shares)) :
    MarketAccounting w' := by
  unfold supply at hsup
  split at hsup
  · simp at hsup
  · next loan' _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hsup
    obtain ⟨rfl, _⟩ := hsup
    refine ⟨?_, h.collateralBacked, h.marketNotBorrower⟩
    show w.state.totalBorrowAssets ≤ w.state.totalSupplyAssets + assets
    have := h.borrowBacked
    unfold BorrowBacked at this; omega

private lemma withdraw_preserves_marketAccounting
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (h : MarketAccounting w)
    (hw : withdraw w user shares = some (w', assets)) :
    MarketAccounting w' := by
  unfold withdraw at hw
  split at hw
  · simp at hw
  · next hLiq =>
    simp only [not_lt] at hLiq
    split at hw
    · simp at hw
    · next shares' _ =>
      split at hw
      · simp at hw
      · next loan' _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, _⟩ := hw
        refine ⟨?_, h.collateralBacked, h.marketNotBorrower⟩
        show w.state.totalBorrowAssets
              ≤ w.state.totalSupplyAssets - supplyAssetFor w.state shares
        omega

private lemma supplyCollateral_preserves_marketAccounting
    {w w' : World} {user : Addr} {c : ℕ}
    (h : MarketAccounting w) (hsc : supplyCollateral w user c = some w') :
    MarketAccounting w' := by
  unfold supplyCollateral at hsc
  split at hsc
  · simp at hsc
  · next huser =>
    -- huser : ¬ user = marketAddress
    split at hsc
    · simp at hsc
    · next col' htr =>
      simp only [Option.some.injEq] at hsc
      rw [← hsc]
      refine ⟨h.borrowBacked, ?_, ?_⟩
      · -- collateralBacked
        show (w.state.collateral.update user (w.state.collateral user + c)).sum
                (fun _ x => x)
              ≤ col'.balances marketAddress
        rw [sum_update_add_self]
        have hbal : col'.balances marketAddress
              = w.state.collateralAsset.balances marketAddress + c :=
          ERC20.transferFrom_balances_receiver huser htr
        rw [hbal]
        have hCB := h.collateralBacked
        unfold CollateralBacked at hCB
        omega
      · -- marketNotBorrower
        show (w.state.collateral.update user (w.state.collateral user + c))
                marketAddress = 0
        rw [Finsupp.update_apply, if_neg (Ne.symm huser)]
        exact h.marketNotBorrower

private lemma withdrawCollateral_preserves_marketAccounting
    {w w' : World} {user : Addr} {c : ℕ}
    (h : MarketAccounting w)
    (hw : withdrawCollateral w user c = some w') :
    MarketAccounting w' := by
  unfold withdrawCollateral at hw
  split at hw
  · simp at hw
  · next hcc =>
    simp only [not_lt] at hcc  -- hcc : c ≤ w.state.collateral user
    split at hw
    · simp at hw
    · next col' htr =>
      split at hw
      · -- health-check pass
        next _ =>
        simp only [Option.some.injEq] at hw
        rw [← hw]
        unfold afterWithdrawCollateral
        refine ⟨h.borrowBacked, ?_, ?_⟩
        · -- collateralBacked
          show (w.state.collateral.update user (w.state.collateral user - c)).sum
                  (fun _ x => x)
                ≤ col'.balances marketAddress
          rw [sum_update_sub_self _ _ _ hcc]
          by_cases huser : user = marketAddress
          · -- user = marketAddress: forced c = 0 (self-transfer)
            subst huser
            have hc : c = 0 := by
              have := h.marketNotBorrower; omega
            subst hc
            have hbal : col'.balances marketAddress
                  = w.state.collateralAsset.balances marketAddress :=
              ERC20.transferFrom_self_balances htr marketAddress
            rw [hbal, Nat.sub_zero]
            exact h.collateralBacked
          · -- user ≠ marketAddress
            have hbal : col'.balances marketAddress
                  = w.state.collateralAsset.balances marketAddress - c :=
              ERC20.transferFrom_balances_sender_eq (Ne.symm huser) htr
            rw [hbal]
            have hCB := h.collateralBacked
            unfold CollateralBacked at hCB
            omega
        · -- marketNotBorrower
          show (w.state.collateral.update user (w.state.collateral user - c))
                  marketAddress = 0
          by_cases huser : user = marketAddress
          · subst huser
            rw [Finsupp.update_apply, if_pos rfl]
            have := h.marketNotBorrower; omega
          · rw [Finsupp.update_apply, if_neg (Ne.symm huser)]
            exact h.marketNotBorrower
      · simp at hw

private lemma borrow_preserves_marketAccounting
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (h : MarketAccounting w)
    (hb : borrow w user assets = some (w', shares)) :
    MarketAccounting w' := by
  unfold borrow at hb
  split at hb
  · simp at hb
  · next hLiq =>
    simp only [not_lt] at hLiq
    split at hb
    · simp at hb
    · next loan' _ =>
      split at hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, _⟩ := hb
        unfold afterBorrow
        refine ⟨?_, h.collateralBacked, h.marketNotBorrower⟩
        show w.state.totalBorrowAssets + assets ≤ w.state.totalSupplyAssets
        omega
      · simp at hb

private lemma repay_preserves_marketAccounting
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (h : MarketAccounting w) (hr : repay w user shares = some (w', assets)) :
    MarketAccounting w' := by
  unfold repay at hr
  split at hr
  · simp at hr
  · next loan' _ =>
    split at hr
    · simp at hr
    · next debt' _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, _⟩ := hr
      refine ⟨?_, h.collateralBacked, h.marketNotBorrower⟩
      show w.state.totalBorrowAssets - repayCost w.state shares
            ≤ w.state.totalSupplyAssets
      have := h.borrowBacked; unfold BorrowBacked at this; omega

private lemma accrueInterest_preserves_marketAccounting
    {w : World} {Δ : ℕ} (h : MarketAccounting w) :
    MarketAccounting (accrueInterest w Δ) := by
  refine ⟨?_, h.collateralBacked, h.marketNotBorrower⟩
  show w.state.totalBorrowAssets + Δ ≤ w.state.totalSupplyAssets + Δ
  have := h.borrowBacked; unfold BorrowBacked at this; omega

/-- `liquidate` decreases `TBA`, optionally moves collateral out of
the market wallet, and reduces the borrower's `state.collateral`
entry — preserving every conjunct of `MarketAccounting`.  The proof
case-splits on `borrower = marketAddress` (then `seized = 0` by
`marketNotBorrower`, so the op is collateral-neutral) and
`liquidator = marketAddress` (then the collateral transfer is a
self-transfer and the market wallet balance is unchanged). -/
private lemma liquidate_preserves_marketAccounting
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (h : MarketAccounting w)
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    MarketAccounting w' := by
  unfold liquidate at hl
  split at hl
  · simp at hl
  · split at hl
    · simp at hl
    · next hCol =>
      simp only [not_lt] at hCol
      split at hl
      · simp at hl
      · next loan' _ =>
        split at hl
        · simp at hl
        · next debt' _ =>
          split at hl
          · simp at hl
          · next col' htr =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, rfl⟩ := hl
            -- Now `seized` is unified with `seizedFor w.state w.oracle.read repaidShares`
            -- and `w'` with the post-state record literal.
            refine ⟨?_, ?_, ?_⟩
            · -- borrowBacked
              show w.state.totalBorrowAssets - repayCost w.state repaidShares
                    ≤ w.state.totalSupplyAssets
              have := h.borrowBacked; unfold BorrowBacked at this; omega
            · -- collateralBacked
              show (w.state.collateral.update borrower
                      (w.state.collateral borrower
                        - seizedFor w.state w.oracle.read repaidShares)).sum
                      (fun _ x => x)
                    ≤ col'.balances marketAddress
              rw [sum_update_sub_self _ _ _ hCol]
              -- Σ' = Σ - seized
              by_cases hlq : liquidator = marketAddress
              · -- self-transfer: balance unchanged
                subst hlq
                have hbal : col'.balances marketAddress
                      = w.state.collateralAsset.balances marketAddress :=
                  ERC20.transferFrom_self_balances htr marketAddress
                rw [hbal]
                have hCB := h.collateralBacked
                unfold CollateralBacked at hCB
                omega
              · -- transfer marketAddress → liquidator: balance drops by seized
                have hbal : col'.balances marketAddress
                      = w.state.collateralAsset.balances marketAddress
                          - seizedFor w.state w.oracle.read repaidShares :=
                  ERC20.transferFrom_balances_sender_eq (Ne.symm hlq) htr
                rw [hbal]
                have hCB := h.collateralBacked
                unfold CollateralBacked at hCB
                -- Need to know seized ≤ collateralAsset.balances marketAddress
                -- This follows from seized ≤ collat.sum ≤ balance.
                have hseized_le_sum :
                    seizedFor w.state w.oracle.read repaidShares
                      ≤ w.state.collateral.sum (fun _ x => x) := by
                  have h1 := Finsupp.sum_update_add w.state.collateral borrower
                    (w.state.collateral borrower
                      - seizedFor w.state w.oracle.read repaidShares)
                    (fun _ x => x) (fun _ => rfl) (fun _ _ _ => rfl)
                  dsimp only at h1
                  -- (update _ _).sum ≥ 0 and (update _ _).sum + collat borrower
                  --   = collat.sum + (collat borrower - seized).
                  -- So collat.sum ≥ seized (using collat borrower ≥ seized).
                  have h2 : 0 ≤ (w.state.collateral.update borrower
                      (w.state.collateral borrower
                        - seizedFor w.state w.oracle.read repaidShares)).sum
                          (fun _ x => x) := Nat.zero_le _
                  omega
                omega
            · -- marketNotBorrower
              show (w.state.collateral.update borrower
                      (w.state.collateral borrower
                        - seizedFor w.state w.oracle.read repaidShares))
                      marketAddress = 0
              by_cases hbm : borrower = marketAddress
              · subst hbm
                rw [Finsupp.update_apply, if_pos rfl]
                have := h.marketNotBorrower
                omega
              · rw [Finsupp.update_apply, if_neg (Ne.symm hbm)]
                exact h.marketNotBorrower

private lemma writeOff_preserves_marketAccounting
    {w w' : World} {borrower : Addr}
    (h : MarketAccounting w) (hwo : writeOff w borrower = some w') :
    MarketAccounting w' := by
  unfold writeOff at hwo
  split at hwo
  · simp at hwo
  · split at hwo
    · simp at hwo
    · next _ =>
      split at hwo
      · simp at hwo
      · next debt' _ =>
        simp only [Option.some.injEq] at hwo
        rw [← hwo]
        refine ⟨?_, h.collateralBacked, h.marketNotBorrower⟩
        -- borrowBacked: TBA - loss ≤ TSA - loss with same loss
        show w.state.totalBorrowAssets
              - min (repayCost w.state (w.state.debtShares.balances borrower))
                    w.state.totalBorrowAssets
            ≤ w.state.totalSupplyAssets
              - min (repayCost w.state (w.state.debtShares.balances borrower))
                    w.state.totalBorrowAssets
        have := h.borrowBacked; unfold BorrowBacked at this
        exact Nat.sub_le_sub_right this _

/-- `writeOff` drops `TBA` and `TSA` by exactly the same realized
loss.  Requires `MarketAccounting w` so that
`loss ≤ TBA ≤ TSA` and neither truncating subtraction underflows. -/
private lemma writeOff_TBA_TSA_drop_equally
    {w w' : World} {borrower : Addr}
    (h : MarketAccounting w) (hwo : writeOff w borrower = some w') :
    w.state.totalBorrowAssets - w'.state.totalBorrowAssets =
    w.state.totalSupplyAssets - w'.state.totalSupplyAssets := by
  obtain ⟨_, _, ⟨hTBA, hTSA⟩, _, _, _⟩ := writeOff_extract hwo
  rw [hTBA, hTSA]
  have hloss_le_TBA :
      min (repayCost w.state (w.state.debtShares.balances borrower))
          w.state.totalBorrowAssets ≤ w.state.totalBorrowAssets :=
    Nat.min_le_right _ _
  have := h.borrowBacked
  unfold BorrowBacked at this
  omega

/-! ## Main theorem -/

theorem step_preserves_marketAccounting {a : Action} {w w' : World}
    (h : MarketAccounting w) (hstep : step a w = some w') :
    MarketAccounting w' := by
  cases a with
  | userSupply u amt =>
    obtain ⟨_, hsup⟩ := step_userSupply_some hstep
    exact supply_preserves_marketAccounting h hsup
  | userWithdraw u sh =>
    obtain ⟨_, hwd⟩ := step_userWithdraw_some hstep
    exact withdraw_preserves_marketAccounting h hwd
  | userSupplyCollateral u c =>
    exact supplyCollateral_preserves_marketAccounting h
      (step_userSupplyCollateral_some hstep)
  | userWithdrawCollateral u c =>
    exact withdrawCollateral_preserves_marketAccounting h
      (step_userWithdrawCollateral_some hstep)
  | userBorrow u amt =>
    obtain ⟨_, hb⟩ := step_userBorrow_some hstep
    exact borrow_preserves_marketAccounting h hb
  | userRepay u sh =>
    obtain ⟨_, hr⟩ := step_userRepay_some hstep
    exact repay_preserves_marketAccounting h hr
  | userLiquidate lq br sh =>
    obtain ⟨_, hl⟩ := step_userLiquidate_some hstep
    exact liquidate_preserves_marketAccounting h hl
  | userWriteOff br =>
    exact writeOff_preserves_marketAccounting h (step_userWriteOff_some hstep)
  | envAccrueInt Δ =>
    rw [step_envAccrueInt_some hstep]
    exact accrueInterest_preserves_marketAccounting h
  | envPriceTick p' =>
    rw [step_envPriceTick_some hstep]
    -- only the oracle changes; state is untouched
    exact ⟨h.borrowBacked, h.collateralBacked, h.marketNotBorrower⟩

end Market
