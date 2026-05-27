import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas

/-!
# Lending Market — Bookkeep preservation

`Bookkeep` is the four-conjunct ERC-20 ledger invariant on the
sub-ledgers (loan asset, collateral asset, supply shares, debt
shares) of the state component `w.state`.  Each operation calls into
ERC-20 primitives whose own preservation lemmas
(`mint_preserves_invariant`, `burn_preserves_invariant`,
`transfer_preserves_invariant`) discharge the corresponding conjunct.

## Main theorem
- `step_preserves_bookkeep`
-/

namespace Market

/-! ## Per-op preservation lemmas (private) -/

private lemma supply_preserves_bookkeep
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (h : Bookkeep w) (hsup : supply w user assets = some (w', shares)) :
    Bookkeep w' := by
  unfold supply at hsup
  split at hsup
  · simp at hsup
  · next loan' htransfer =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hsup
    obtain ⟨rfl, _⟩ := hsup
    exact ⟨ERC20.transferFrom_preserves_invariant h.loanAssetInv htransfer,
           h.collatAssetInv,
           ERC20.mint_preserves_invariant h.supplyShareInv,
           h.debtShareInv⟩

private lemma withdraw_preserves_bookkeep
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (h : Bookkeep w) (hw : withdraw w user shares = some (w', assets)) :
    Bookkeep w' := by
  unfold withdraw at hw
  split at hw
  · simp at hw
  · split at hw
    · simp at hw
    · next shares' hburn =>
      split at hw
      · simp at hw
      · next loan' htransfer =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, _⟩ := hw
        exact ⟨ERC20.transferFrom_preserves_invariant h.loanAssetInv htransfer,
               h.collatAssetInv,
               ERC20.burn_preserves_invariant h.supplyShareInv hburn,
               h.debtShareInv⟩

private lemma supplyCollateral_preserves_bookkeep
    {w w' : World} {user : Addr} {c : ℕ}
    (h : Bookkeep w) (hsc : supplyCollateral w user c = some w') :
    Bookkeep w' := by
  unfold supplyCollateral at hsc
  split at hsc
  · simp at hsc
  · next _ =>
    split at hsc
    · simp at hsc
    · next col' htransfer =>
      simp only [Option.some.injEq] at hsc
      rw [← hsc]
      exact ⟨h.loanAssetInv,
             ERC20.transferFrom_preserves_invariant h.collatAssetInv htransfer,
             h.supplyShareInv, h.debtShareInv⟩

private lemma withdrawCollateral_preserves_bookkeep
    {w w' : World} {user : Addr} {c : ℕ}
    (h : Bookkeep w) (hw : withdrawCollateral w user c = some w') :
    Bookkeep w' := by
  unfold withdrawCollateral at hw
  split at hw
  · simp at hw
  · split at hw
    · simp at hw
    · next col' htransfer =>
      split at hw
      · simp only [Option.some.injEq] at hw
        rw [← hw]
        unfold afterWithdrawCollateral
        exact ⟨h.loanAssetInv,
               ERC20.transferFrom_preserves_invariant h.collatAssetInv htransfer,
               h.supplyShareInv, h.debtShareInv⟩
      · simp at hw

private lemma borrow_preserves_bookkeep
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (h : Bookkeep w) (hb : borrow w user assets = some (w', shares)) :
    Bookkeep w' := by
  unfold borrow at hb
  split at hb
  · simp at hb
  · split at hb
    · simp at hb
    · next loan' htransfer =>
      split at hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, _⟩ := hb
        unfold afterBorrow
        exact ⟨ERC20.transferFrom_preserves_invariant h.loanAssetInv htransfer,
               h.collatAssetInv, h.supplyShareInv,
               ERC20.mint_preserves_invariant h.debtShareInv⟩
      · simp at hb

private lemma repay_preserves_bookkeep
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (h : Bookkeep w) (hr : repay w user shares = some (w', assets)) :
    Bookkeep w' := by
  unfold repay at hr
  split at hr
  · simp at hr
  · next loan' htransfer =>
    split at hr
    · simp at hr
    · next debt' hburn =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, _⟩ := hr
      exact ⟨ERC20.transferFrom_preserves_invariant h.loanAssetInv htransfer,
             h.collatAssetInv, h.supplyShareInv,
             ERC20.burn_preserves_invariant h.debtShareInv hburn⟩

private lemma accrueInterest_preserves_bookkeep
    {w : World} {Δ : ℕ} (h : Bookkeep w) :
    Bookkeep (accrueInterest w Δ) :=
  ⟨h.loanAssetInv, h.collatAssetInv, h.supplyShareInv, h.debtShareInv⟩

private lemma liquidate_preserves_bookkeep
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (h : Bookkeep w)
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    Bookkeep w' := by
  unfold liquidate at hl
  split at hl
  · simp at hl
  · split at hl
    · simp at hl
    · split at hl
      · simp at hl
      · next loan' htrLoan =>
        split at hl
        · simp at hl
        · next debt' hburn =>
          split at hl
          · simp at hl
          · next col' htrCol =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, _⟩ := hl
            exact ⟨ERC20.transferFrom_preserves_invariant h.loanAssetInv htrLoan,
                   ERC20.transferFrom_preserves_invariant h.collatAssetInv htrCol,
                   h.supplyShareInv,
                   ERC20.burn_preserves_invariant h.debtShareInv hburn⟩

private lemma writeOff_preserves_bookkeep
    {w w' : World} {borrower : Addr}
    (h : Bookkeep w) (hwo : writeOff w borrower = some w') :
    Bookkeep w' := by
  unfold writeOff at hwo
  split at hwo
  · simp at hwo
  · split at hwo
    · simp at hwo
    · split at hwo
      · simp at hwo
      · next debt' hburn =>
        simp only [Option.some.injEq] at hwo
        rw [← hwo]
        exact ⟨h.loanAssetInv, h.collatAssetInv, h.supplyShareInv,
               ERC20.burn_preserves_invariant h.debtShareInv hburn⟩

/-! ## Main theorem -/

theorem step_preserves_bookkeep {a : Action} {w w' : World}
    (h : Bookkeep w) (hstep : step a w = some w') : Bookkeep w' := by
  cases a with
  | userSupply u amt =>
    obtain ⟨_, hsup⟩ := step_userSupply_some hstep
    exact supply_preserves_bookkeep h hsup
  | userWithdraw u sh =>
    obtain ⟨_, hwd⟩ := step_userWithdraw_some hstep
    exact withdraw_preserves_bookkeep h hwd
  | userSupplyCollateral u c =>
    exact supplyCollateral_preserves_bookkeep h
      (step_userSupplyCollateral_some hstep)
  | userWithdrawCollateral u c =>
    exact withdrawCollateral_preserves_bookkeep h
      (step_userWithdrawCollateral_some hstep)
  | userBorrow u amt =>
    obtain ⟨_, hb⟩ := step_userBorrow_some hstep
    exact borrow_preserves_bookkeep h hb
  | userRepay u sh =>
    obtain ⟨_, hr⟩ := step_userRepay_some hstep
    exact repay_preserves_bookkeep h hr
  | userLiquidate lq br sh =>
    obtain ⟨_, hl⟩ := step_userLiquidate_some hstep
    exact liquidate_preserves_bookkeep h hl
  | userWriteOff br =>
    exact writeOff_preserves_bookkeep h (step_userWriteOff_some hstep)
  | envAccrueInt Δ =>
    rw [step_envAccrueInt_some hstep]
    exact accrueInterest_preserves_bookkeep h
  | envPriceTick p' =>
    rw [step_envPriceTick_some hstep]
    -- Goal: Bookkeep (w.state, Oracle.update w.oracle p').
    -- Bookkeep only inspects `.1`, which is `w.state`, unchanged.
    exact ⟨h.loanAssetInv, h.collatAssetInv, h.supplyShareInv, h.debtShareInv⟩

end Market
