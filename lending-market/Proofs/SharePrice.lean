import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas

/-!
# Lending Market — SupplySharePriceLE preservation

The supply-share price `(TSA + vSA) / (SS + vSS)` is non-decreasing
across every action.  `supply` and `withdraw` are non-trivial (the
floor rounding favors existing shareholders); the four ops that
don't touch the supply side use reflexivity.  `accrueInterest`
raises `TSA` without changing the share total — also non-decreasing.

## Main theorem
- `step_preserves_supplySharePriceLE`
-/

namespace Market

/-! ## Per-op preservation lemmas (private) -/

private lemma supply_preserves_supplySharePriceLE
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (hsup : supply w user assets = some (w', shares)) :
    SupplySharePriceLE w w' := by
  obtain ⟨htA, htS, hk, _⟩ := supply_extract hsup
  unfold SupplySharePriceLE
  rw [htA, htS]
  have hbound : shares * (w.state.totalSupplyAssets + virtualSupplyAssets)
              ≤ assets * (w.state.supplyShares.totalSupply + virtualSupplyShares) := by
    rw [hk]; exact supplyShareFor_bound w.state assets
  have el : (w.state.totalSupplyAssets + virtualSupplyAssets) *
              (w.state.supplyShares.totalSupply + shares + virtualSupplyShares)
          = (w.state.totalSupplyAssets + virtualSupplyAssets) *
              (w.state.supplyShares.totalSupply + virtualSupplyShares)
          + (w.state.totalSupplyAssets + virtualSupplyAssets) * shares := by ring
  have er : (w.state.totalSupplyAssets + assets + virtualSupplyAssets) *
              (w.state.supplyShares.totalSupply + virtualSupplyShares)
          = (w.state.totalSupplyAssets + virtualSupplyAssets) *
              (w.state.supplyShares.totalSupply + virtualSupplyShares)
          + assets * (w.state.supplyShares.totalSupply + virtualSupplyShares) := by ring
  have hcomm : (w.state.totalSupplyAssets + virtualSupplyAssets) * shares
             = shares * (w.state.totalSupplyAssets + virtualSupplyAssets) := Nat.mul_comm _ _
  omega

private lemma withdraw_preserves_supplySharePriceLE
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (hbk : Bookkeep w) (hw : withdraw w user shares = some (w', assets)) :
    SupplySharePriceLE w w' := by
  unfold withdraw at hw
  split at hw
  · simp at hw
  · next hLiq =>
    simp only [not_lt] at hLiq
    split at hw
    · simp at hw
    · next shares' hburn =>
      split at hw
      · simp at hw
      · next loan' _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, ha⟩ := hw
        subst ha
        have hbal := burn_amount_le hburn
        have hbal_le := balance_le_totalSupply hbk.supplyShareInv user
        have hkS : shares ≤ w.state.supplyShares.totalSupply := by omega
        have ha_le : supplyAssetFor w.state shares ≤ w.state.totalSupplyAssets := by omega
        have hbound : supplyAssetFor w.state shares *
                        (w.state.supplyShares.totalSupply + virtualSupplyShares)
                    ≤ shares * (w.state.totalSupplyAssets + virtualSupplyAssets) := by
          unfold supplyAssetFor; exact Nat.div_mul_le_self _ _
        show (w.state.totalSupplyAssets + virtualSupplyAssets) *
               (shares'.totalSupply + virtualSupplyShares)
             ≤ (w.state.totalSupplyAssets - supplyAssetFor w.state shares + virtualSupplyAssets) *
               (w.state.supplyShares.totalSupply + virtualSupplyShares)
        rw [show shares'.totalSupply = w.state.supplyShares.totalSupply - shares
             from burn_totalSupply hburn]
        have el : (w.state.totalSupplyAssets + virtualSupplyAssets) *
                    (w.state.supplyShares.totalSupply - shares + virtualSupplyShares)
                + (w.state.totalSupplyAssets + virtualSupplyAssets) * shares
                = (w.state.totalSupplyAssets + virtualSupplyAssets) *
                    (w.state.supplyShares.totalSupply + virtualSupplyShares) := by
          rw [← Nat.mul_add]
          have : w.state.supplyShares.totalSupply - shares + virtualSupplyShares + shares
               = w.state.supplyShares.totalSupply + virtualSupplyShares := by omega
          rw [this]
        have er : (w.state.totalSupplyAssets - supplyAssetFor w.state shares + virtualSupplyAssets) *
                    (w.state.supplyShares.totalSupply + virtualSupplyShares)
                + supplyAssetFor w.state shares *
                    (w.state.supplyShares.totalSupply + virtualSupplyShares)
                = (w.state.totalSupplyAssets + virtualSupplyAssets) *
                    (w.state.supplyShares.totalSupply + virtualSupplyShares) := by
          rw [← Nat.add_mul]
          have : w.state.totalSupplyAssets - supplyAssetFor w.state shares + virtualSupplyAssets
                  + supplyAssetFor w.state shares
               = w.state.totalSupplyAssets + virtualSupplyAssets := by omega
          rw [this]
        have hcomm : (w.state.totalSupplyAssets + virtualSupplyAssets) * shares
                   = shares * (w.state.totalSupplyAssets + virtualSupplyAssets) :=
          Nat.mul_comm _ _
        omega

private lemma supplyCollateral_preserves_supplySharePriceLE
    {w w' : World} {user : Addr} {c : ℕ}
    (hsc : supplyCollateral w user c = some w') :
    SupplySharePriceLE w w' := by
  unfold supplyCollateral at hsc
  split at hsc
  · simp at hsc
  · next _ =>
    split at hsc
    · simp at hsc
    · next col' _ =>
      simp only [Option.some.injEq] at hsc
      rw [← hsc]
      exact Nat.le_refl _

private lemma withdrawCollateral_preserves_supplySharePriceLE
    {w w' : World} {user : Addr} {c : ℕ}
    (hw : withdrawCollateral w user c = some w') :
    SupplySharePriceLE w w' := by
  unfold withdrawCollateral at hw
  split at hw
  · simp at hw
  · split at hw
    · simp at hw
    · next col' _ =>
      split at hw
      · simp only [Option.some.injEq] at hw
        rw [← hw]
        unfold afterWithdrawCollateral
        exact Nat.le_refl _
      · simp at hw

private lemma borrow_preserves_supplySharePriceLE
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (hb : borrow w user assets = some (w', shares)) :
    SupplySharePriceLE w w' := by
  unfold borrow at hb
  split at hb
  · simp at hb
  · split at hb
    · simp at hb
    · next loan' _ =>
      split at hb
      · simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, _⟩ := hb
        unfold afterBorrow
        exact Nat.le_refl _
      · simp at hb

private lemma repay_preserves_supplySharePriceLE
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (hr : repay w user shares = some (w', assets)) :
    SupplySharePriceLE w w' := by
  unfold repay at hr
  split at hr
  · simp at hr
  · next loan' _ =>
    split at hr
    · simp at hr
    · next debt' _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, _⟩ := hr
      exact Nat.le_refl _

private lemma accrueInterest_preserves_supplySharePriceLE
    (w : World) (Δ : ℕ) :
    SupplySharePriceLE w (accrueInterest w Δ) := by
  unfold SupplySharePriceLE
  show (w.state.totalSupplyAssets + virtualSupplyAssets) *
         (w.state.supplyShares.totalSupply + virtualSupplyShares)
       ≤ (w.state.totalSupplyAssets + Δ + virtualSupplyAssets) *
         (w.state.supplyShares.totalSupply + virtualSupplyShares)
  exact Nat.mul_le_mul_right _ (by omega)

/-- `liquidate` does not touch the supply side (`TSA` and supply
shares are unchanged), so the supply-share price ratio is exactly
preserved. -/
private lemma liquidate_preserves_supplySharePriceLE
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    SupplySharePriceLE w w' := by
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
        · next debt' _ =>
          split at hl
          · simp at hl
          · next col' _ =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hl
            obtain ⟨rfl, _⟩ := hl
            -- TSA and supplyShares.totalSupply are unchanged.
            exact Nat.le_refl _

/-! ## Main theorem -/

theorem step_preserves_supplySharePriceLE {a : Action} {w w' : World}
    (h_nbd : NoBadDebt a) (hbk : Bookkeep w) (hstep : step a w = some w') :
    SupplySharePriceLE w w' := by
  cases a with
  | userSupply u amt =>
    obtain ⟨_, hsup⟩ := step_userSupply_some hstep
    exact supply_preserves_supplySharePriceLE hsup
  | userWithdraw u sh =>
    obtain ⟨_, hwd⟩ := step_userWithdraw_some hstep
    exact withdraw_preserves_supplySharePriceLE hbk hwd
  | userSupplyCollateral u c =>
    exact supplyCollateral_preserves_supplySharePriceLE
      (step_userSupplyCollateral_some hstep)
  | userWithdrawCollateral u c =>
    exact withdrawCollateral_preserves_supplySharePriceLE
      (step_userWithdrawCollateral_some hstep)
  | userBorrow u amt =>
    obtain ⟨_, hb⟩ := step_userBorrow_some hstep
    exact borrow_preserves_supplySharePriceLE hb
  | userRepay u sh =>
    obtain ⟨_, hr⟩ := step_userRepay_some hstep
    exact repay_preserves_supplySharePriceLE hr
  | userLiquidate lq br sh =>
    obtain ⟨_, hl⟩ := step_userLiquidate_some hstep
    exact liquidate_preserves_supplySharePriceLE hl
  | userWriteOff br =>
    -- Bad-debt write-off socializes loss: TSA drops while supply shares
    -- stay constant, so the share price strictly decreases.  Excluded
    -- by `NoBadDebt`.
    exact absurd h_nbd (by simp [NoBadDebt])
  | envAccrueInt Δ =>
    rw [step_envAccrueInt_some hstep]
    exact accrueInterest_preserves_supplySharePriceLE w Δ
  | envPriceTick p' =>
    rw [step_envPriceTick_some hstep]
    show SupplySharePriceLE w ⟨w.state, Oracle.update w.oracle p'⟩
    -- The post-state's `.state` projection is `w.state`, so the comparison
    -- is reflexive on the state component.
    unfold SupplySharePriceLE
    exact Nat.le_refl _

end Market
