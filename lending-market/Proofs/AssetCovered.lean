import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas

/-!
# Lending Market — AssetCovered preservation

`AssetCovered w` is `AllHealthy w` with the LTV buffer removed: the
**last line of defence** against bad debt.  This file collects the
preservation theorems whose precondition is `AssetCovered w` itself
(the durable layer's own preservation), plus a consumption-side
corollary.

Environment-action preservation (`accrueInterest`, `envPriceTick`)
takes `AllHealthy w`, not `AssetCovered w`, so it lives in
`AllHealthyToAssetCovered.lean` together with the chain theorems
`allHealthy_implies_assetCovered` and
`step_remains_assetCovered_under_allHealthy`.

## Main theorems
- `assetCovered_implies_debtOf_le` — consumption-side corollary
  (1-wei ceilDiv slack).
- `step_preserves_assetCovered` — user ops only (env actions
  excluded by `NoPriceMove` / `NoAccrual`); takes the action-level
  step budgets `LiquidateStepBudget` and `BurnStepBudget`.

The per-op preservation lemmas (`<op>_preserves_assetCovered`,
`writeOff_impossible_of_assetCovered`) and the building block
`assetCovered_user_of_debtOf_le_collateral_value` are `private`
to this file.  `healthy_user_implies_assetCovered_user` is exposed
because `AllHealthyToAssetCovered.lean` reuses it.
-/

namespace Market

open Util (ceilDiv ceilDiv_mul_ge)

/-! ## Per-user `Healthy → AssetCovered` building block (private) -/

/-- A recorded-debt coverage bound implies the multiplicative
`AssetCovered` inequality for one user. -/
private lemma assetCovered_user_of_debtOf_le_collateral_value
    {w : World} {u : Addr}
    (hDebt :
      (debtOf w.state u : ℚ) ≤
        (w.state.collateral u : ℚ) * w.oracle.read_q) :
    (w.state.debtShares.balances u : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
      ≤ (w.state.collateral u : ℚ) * w.oracle.read_q
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
  set R : ℕ := w.state.totalBorrowAssets + virtualBorrowAssets
  set S : ℕ := w.state.debtShares.totalSupply + virtualBorrowShares
  have hS_pos : 0 < S := by
    dsimp [S]
    have := virtualBorrowShares_pos
    omega
  have hCD :
      w.state.debtShares.balances u * R ≤ debtOf w.state u * S := by
    dsimp [R, S]
    unfold debtOf repayCost
    exact ceilDiv_mul_ge _ hS_pos
  have hCD_q :
      (w.state.debtShares.balances u : ℚ) * (R : ℚ)
        ≤ (debtOf w.state u : ℚ) * (S : ℚ) := by
    exact_mod_cast hCD
  have hS_nn : (0 : ℚ) ≤ (S : ℚ) := by
    exact_mod_cast Nat.zero_le S
  have hDebtS :
      (debtOf w.state u : ℚ) * (S : ℚ)
        ≤ ((w.state.collateral u : ℚ) * w.oracle.read_q) * (S : ℚ) :=
    mul_le_mul_of_nonneg_right hDebt hS_nn
  have hR :
      (R : ℚ) = (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets := by
    dsimp [R]; push_cast; ring
  have hS :
      (S : ℚ) = (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    dsimp [S]; push_cast; ring
  rw [← hR, ← hS]
  nlinarith

/-- A healthy user is asset-covered at the same oracle price.

In the new two-floor `Healthy`, no oracle-price nonnegativity
hypothesis is needed (mantissas are `Nat`, `toRat` is automatic). -/
lemma healthy_user_implies_assetCovered_user
    {w : World} {u : Addr}
    (hH : Healthy w u) :
    (w.state.debtShares.balances u : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
      ≤ (w.state.collateral u : ℚ) * w.oracle.read_q
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
  -- Extract the ℚ-form bound `debt ≤ coll · p · lltv` and weaken by
  -- `lltv ≤ 1` to get `debt ≤ coll · p`.
  have hQ := Healthy.toQForm hH
  have hCol_nn : (0 : ℚ) ≤ (w.state.collateral u : ℚ) := by
    exact_mod_cast Nat.zero_le _
  have hp_nn : 0 ≤ w.oracle.read_q := Oracle.read_q_nonneg _
  have hValue_nn :
      (0 : ℚ) ≤ (w.state.collateral u : ℚ) * w.oracle.read_q :=
    mul_nonneg hCol_nn hp_nn
  have hDebt :
      (debtOf w.state u : ℚ)
        ≤ (w.state.collateral u : ℚ) * w.oracle.read_q := by
    nlinarith [hQ, lltv_q_le_one, hValue_nn]
  exact assetCovered_user_of_debtOf_le_collateral_value hDebt

/-! ## Consumption-side corollary -/

/-- `AssetCovered` implies a per-user `debtOf` bound with 1-wei slack
in loan-asset units (the ceilDiv rounding excess on `debtOf`). -/
theorem assetCovered_implies_debtOf_le
    {w : World} (hAC : AssetCovered w) :
    ∀ u, (debtOf w.state u : ℚ) ≤ (w.state.collateral u : ℚ) * (Oracle.read w.oracle).toRat + 1 := by
  intro u
  set X := w.state.debtShares.balances u *
             (w.state.totalBorrowAssets + virtualBorrowAssets) with hX
  set S := w.state.debtShares.totalSupply + virtualBorrowShares with hSeq
  have hS_pos : 0 < S := by
    simp only [hSeq]; have := virtualBorrowShares_pos; omega
  have hSq_pos : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS_pos
  have hSq_nn : (0 : ℚ) ≤ (S : ℚ) := le_of_lt hSq_pos
  have hdebtOf_eq : debtOf w.state u = ceilDiv X S := by
    simp only [debtOf, repayCost, hX, hSeq]
  rw [hdebtOf_eq]
  have hAC_u : (X : ℚ) ≤ (w.state.collateral u : ℚ) * (Oracle.read w.oracle).toRat * (S : ℚ) := by
    have h := (assetCoveredAt_iff_shareMul w u).mp (hAC u)
    have hX_q : (X : ℚ) = (w.state.debtShares.balances u : ℚ) *
                            ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets) := by
      simp only [hX]; push_cast; ring
    have hS_q : (S : ℚ) = (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
      simp only [hSeq]; push_cast; rfl
    rw [hX_q, hS_q]; linarith [h]
  have hceilℕ : ceilDiv X S * S ≤ X + S - 1 := by
    unfold ceilDiv; exact Nat.div_mul_le_self _ _
  have hX_S_ge1 : 1 ≤ X + S := by omega
  have hceilℚ : ((ceilDiv X S : ℕ) : ℚ) * (S : ℚ) ≤ (X : ℚ) + (S : ℚ) - 1 := by
    have h1 : ((ceilDiv X S * S : ℕ) : ℚ) ≤ ((X + S - 1 : ℕ) : ℚ) := by
      exact_mod_cast hceilℕ
    rw [Nat.cast_sub hX_S_ge1] at h1
    push_cast at h1; linarith
  have hbig : ((ceilDiv X S : ℕ) : ℚ) * (S : ℚ)
                ≤ ((w.state.collateral u : ℚ) * (Oracle.read w.oracle).toRat + 1) * (S : ℚ) := by
    calc ((ceilDiv X S : ℕ) : ℚ) * (S : ℚ)
        ≤ (X : ℚ) + (S : ℚ) - 1 := hceilℚ
      _ ≤ (w.state.collateral u : ℚ) * (Oracle.read w.oracle).toRat * (S : ℚ) + (S : ℚ) - 1 := by linarith
      _ ≤ (w.state.collateral u : ℚ) * (Oracle.read w.oracle).toRat * (S : ℚ) + (S : ℚ) := by linarith
      _ = ((w.state.collateral u : ℚ) * (Oracle.read w.oracle).toRat + 1) * (S : ℚ) := by ring
  exact le_of_mul_le_mul_right hbig hSq_pos

/-! ## Per-op preservation lemmas (private) -/

/-- `supply` does not touch the borrow/collateral side of
`AssetCovered`. -/
private lemma supply_preserves_assetCovered
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (hAC : AssetCovered w)
    (hsup : supply w user assets = some (w', shares)) :
    AssetCovered w' := by
  rw [AssetCovered_iff_shareMul] at hAC ⊢
  unfold supply at hsup
  split at hsup
  · simp at hsup
  · next loan' _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hsup
    obtain ⟨rfl, _⟩ := hsup
    exact hAC

/-- `withdraw` does not touch the borrow/collateral side of
`AssetCovered`. -/
private lemma withdraw_preserves_assetCovered
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (hAC : AssetCovered w)
    (hw : withdraw w user shares = some (w', assets)) :
    AssetCovered w' := by
  rw [AssetCovered_iff_shareMul] at hAC ⊢
  unfold withdraw at hw
  split at hw
  · simp at hw
  · split at hw
    · simp at hw
    · next shares' _ =>
      split at hw
      · simp at hw
      · next loan' _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, _⟩ := hw
        exact hAC

/-- Supplying collateral only increases one user's collateral. -/
private lemma supplyCollateral_preserves_assetCovered
    {w w' : World} {actor : Addr} {c : ℕ}
    (hp : 0 ≤ w.oracle.read_q)
    (hAC : AssetCovered w)
    (hsc : supplyCollateral w actor c = some w') :
    AssetCovered w' := by
  rw [AssetCovered_iff_shareMul] at hAC ⊢
  unfold supplyCollateral at hsc
  split at hsc
  · simp at hsc
  · next _ =>
    split at hsc
    · simp at hsc
    · next col' _ =>
      simp only [Option.some.injEq] at hsc
      rw [← hsc]
      intro v
      have hOld := hAC v
      by_cases hv : v = actor
      · subst v
        have hS_nn :
            (0 : ℚ) ≤
              (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
          have hTs_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
            exact_mod_cast Nat.zero_le _
          have hvBS_nn : (0 : ℚ) ≤ (virtualBorrowShares : ℕ) := by
            exact_mod_cast Nat.zero_le virtualBorrowShares
          linarith
        have hDelta_nn :
            0 ≤ (c : ℚ) * w.oracle.read_q
                * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
          have hc_nn : (0 : ℚ) ≤ (c : ℚ) := by exact_mod_cast Nat.zero_le c
          exact mul_nonneg (mul_nonneg hc_nn hp) hS_nn
        simp only [Finsupp.update_apply, ↓reduceIte]
        push_cast
        nlinarith
      · simpa [Finsupp.update_apply, hv] using hOld

/-- Withdrawing collateral is accepted only when the actor is healthy
after the withdrawal; other users' borrow/collateral data is
unchanged. -/
private lemma withdrawCollateral_preserves_assetCovered
    {w w' : World} {actor : Addr} {c : ℕ}
    (hAC : AssetCovered w)
    (hwd : withdrawCollateral w actor c = some w') :
    AssetCovered w' := by
  rw [AssetCovered_iff_shareMul] at hAC ⊢
  unfold withdrawCollateral at hwd
  split at hwd
  · simp at hwd
  · split at hwd
    · simp at hwd
    · next col' _ =>
      split at hwd
      · next hHealthy =>
        simp only [Option.some.injEq] at hwd
        rw [← hwd]
        intro v
        by_cases hv : v = actor
        · subst v
          exact healthy_user_implies_assetCovered_user
            (w := ⟨afterWithdrawCollateral w.state actor col' c, w.oracle⟩)
            hHealthy
        · simpa [afterWithdrawCollateral, Finsupp.update_apply, hv]
            using hAC v
      · simp at hwd

/-- `borrow` preserves `AssetCovered`: the actor is checked healthy in
the post-state, and all other users see a non-increasing borrow rate
because `borrowShareFor` rounds up. -/
private lemma borrow_preserves_assetCovered
    {w w' : World} {actor : Addr} {assets shares : ℕ}
    (hAC : AssetCovered w)
    (hb : borrow w actor assets = some (w', shares)) :
    AssetCovered w' := by
  rw [AssetCovered_iff_shareMul] at hAC ⊢
  unfold borrow at hb
  split at hb
  · simp at hb
  · split at hb
    · simp at hb
    · next loan' _ =>
      split at hb
      · next hHealthy =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hb
        obtain ⟨rfl, hshares⟩ := hb
        subst hshares
        intro v
        by_cases hv : v = actor
        · subst v
          exact healthy_user_implies_assetCovered_user
            (w := ⟨afterBorrow w.state actor loan' assets, w.oracle⟩)
            hHealthy
        · unfold afterBorrow
          simp only
          set minted : ℕ := borrowShareFor w.state assets
          have hBal_u :
              (ERC20.mint w.state.debtShares actor minted).balances v
                = w.state.debtShares.balances v := by
            dsimp [ERC20.mint, minted]
            simp [Finsupp.single_eq_of_ne hv]
          have hTotal :
              (ERC20.mint w.state.debtShares actor minted).totalSupply
                = w.state.debtShares.totalSupply + minted := by
            dsimp [ERC20.mint, minted]
          rw [hBal_u, hTotal]
          set Y : ℚ := (w.state.debtShares.balances v : ℚ)
          set C : ℚ := (w.state.collateral v : ℚ)
          set p : ℚ := w.oracle.read_q
          set R : ℚ := (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets
          set S : ℚ := (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares
          set aQ : ℚ := (assets : ℚ)
          set kQ : ℚ := (minted : ℚ)
          have hAC_u : Y * R ≤ C * p * S := by
            have h := hAC v
            simpa [Y, C, p, R, S] using h
          have hY_nn : 0 ≤ Y := by
            dsimp [Y]; exact_mod_cast Nat.zero_le _
          have hS_pos : 0 < S := by
            dsimp [S]
            have hTs_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
              exact_mod_cast Nat.zero_le _
            have hvBS_pos : (0 : ℚ) < (virtualBorrowShares : ℕ) := by
              exact_mod_cast virtualBorrowShares_pos
            linarith
          have hS_minted_nn : 0 ≤ S + kQ := by
            have hS_nn : (0 : ℚ) ≤ S := le_of_lt hS_pos
            have hk_nn : (0 : ℚ) ≤ kQ := by
              dsimp [kQ]; exact_mod_cast Nat.zero_le _
            linarith
          have hRate : aQ * S ≤ kQ * R := by
            have hnat := borrowShareFor_bound w.state assets
            have hcast :
                ((assets
                  * (w.state.debtShares.totalSupply + virtualBorrowShares) : ℕ) : ℚ)
                  ≤
                ((minted
                  * (w.state.totalBorrowAssets + virtualBorrowAssets) : ℕ) : ℚ) := by
              exact_mod_cast hnat
            push_cast at hcast
            simpa [aQ, kQ, R, S, minted, mul_assoc] using hcast
          have hGoal :
              Y * (R + aQ) ≤ C * p * (S + kQ) :=
            assetCovered_after_borrow_rate_le
              (Y := Y) (C := C) (p := p) (R := R) (S := S)
              (assets := aQ) (minted := kQ)
              hAC_u hY_nn hS_pos hS_minted_nn hRate
          have hRewriteR :
              ((w.state.totalBorrowAssets + assets : ℕ) : ℚ) + virtualBorrowAssets
                = (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets
                  + (assets : ℚ) := by
            push_cast; ring
          have hRewriteS :
              ((w.state.debtShares.totalSupply + minted : ℕ) : ℚ) + virtualBorrowShares
                = (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares
                  + (minted : ℚ) := by
            push_cast; ring
          rw [hRewriteR, hRewriteS]
          simpa [Y, C, p, R, S, aQ, kQ] using hGoal
      · simp at hb

/-- `repay` preserves `AssetCovered` when the repayment does not consume
the virtual borrow asset. -/
private lemma repay_preserves_assetCovered
    {w w' : World} {user : Addr} {sh assets : ℕ}
    (hbk : Bookkeep w)
    (hAC : AssetCovered w)
    (hBudget : RepayDoesNotHitVirtualBorrowAsset w sh)
    (hr : repay w user sh = some (w', assets)) :
    AssetCovered w' := by
  rw [AssetCovered_iff_shareMul] at hAC ⊢
  unfold repay at hr
  split at hr
  · simp at hr
  · next loan' _ =>
    split at hr
    · simp at hr
    · next debt' hburn =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, _⟩ := hr
      change repayCost w.state sh ≤ w.state.totalBorrowAssets at hBudget
      have hBurn_le : sh ≤ w.state.debtShares.balances user :=
        burn_amount_le hburn
      have hUserBal_le := balance_le_totalSupply hbk.debtShareInv user
      have hSh_le_total : sh ≤ w.state.debtShares.totalSupply := by omega
      have hBurnTotal : debt'.totalSupply = w.state.debtShares.totalSupply - sh :=
        burn_totalSupply hburn
      have hCostBound :
          sh * (w.state.totalBorrowAssets + virtualBorrowAssets)
            ≤ repayCost w.state sh *
                (w.state.debtShares.totalSupply + virtualBorrowShares) := by
        unfold repayCost
        apply ceilDiv_mul_ge
        have := virtualBorrowShares_pos
        omega
      intro u
      have hYnew_le_nat :
          debt'.balances u ≤ w.state.debtShares.balances u := by
        by_cases huu : u = user
        · subst huu
          rw [burn_balances_self hburn]
          omega
        · rw [burn_balances_other hburn huu]
      have hCastTBA :
          ((w.state.totalBorrowAssets - repayCost w.state sh : ℕ) : ℚ)
            = (w.state.totalBorrowAssets : ℚ) - (repayCost w.state sh : ℚ) :=
        Nat.cast_sub hBudget
      have hCastSh :
          ((w.state.debtShares.totalSupply - sh : ℕ) : ℚ)
            = (w.state.debtShares.totalSupply : ℚ) - (sh : ℚ) :=
        Nat.cast_sub hSh_le_total
      rw [hBurnTotal, hCastTBA, hCastSh]
      set Yold : ℚ := (w.state.debtShares.balances u : ℚ)
      set Ynew : ℚ := (debt'.balances u : ℚ)
      set C : ℚ := (w.state.collateral u : ℚ)
      set p : ℚ := w.oracle.read_q
      set R : ℚ := (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets
      set S : ℚ := (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares
      set cost : ℚ := (repayCost w.state sh : ℚ)
      set shQ : ℚ := (sh : ℚ)
      have hAC_u : Yold * R ≤ C * p * S := by
        have h := hAC u
        simpa [Yold, C, p, R, S] using h
      have hYnew_le : Ynew ≤ Yold := by
        dsimp [Ynew, Yold]
        exact_mod_cast hYnew_le_nat
      have hYnew_nn : 0 ≤ Ynew := by
        dsimp [Ynew]; exact_mod_cast Nat.zero_le _
      have hR_nn : 0 ≤ R := by
        dsimp [R]
        have hTBA_nn : (0 : ℚ) ≤ (w.state.totalBorrowAssets : ℚ) := by
          exact_mod_cast Nat.zero_le _
        have hvBA_nn : (0 : ℚ) ≤ (virtualBorrowAssets : ℕ) := by
          exact_mod_cast Nat.zero_le virtualBorrowAssets
        linarith
      have hS_pos : 0 < S := by
        dsimp [S]
        have hTs_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
          exact_mod_cast Nat.zero_le _
        have hvBS_pos : (0 : ℚ) < (virtualBorrowShares : ℕ) := by
          exact_mod_cast virtualBorrowShares_pos
        linarith
      have hS_minus_nonneg : 0 ≤ S - shQ := by
        have hsh_le : shQ ≤ (w.state.debtShares.totalSupply : ℚ) := by
          dsimp [shQ]; exact_mod_cast hSh_le_total
        dsimp [S]
        have hvBS_nn : (0 : ℚ) ≤ (virtualBorrowShares : ℕ) := by
          exact_mod_cast Nat.zero_le virtualBorrowShares
        linarith
      have hRate : shQ * R ≤ cost * S := by
        have hcast :
            ((sh * (w.state.totalBorrowAssets + virtualBorrowAssets) : ℕ) : ℚ)
              ≤
            ((repayCost w.state sh *
              (w.state.debtShares.totalSupply + virtualBorrowShares) : ℕ) : ℚ) := by
          exact_mod_cast hCostBound
        push_cast at hcast
        simpa [shQ, R, S, cost] using hcast
      have hGoal :
          Ynew * (R - cost) ≤ C * p * (S - shQ) :=
        assetCovered_after_burn_rate_le
          (Yold := Yold) (Ynew := Ynew) (C := C) (p := p)
          (R := R) (S := S) (cost := cost) (burned := shQ)
          hAC_u hYnew_le hYnew_nn hR_nn hS_pos hS_minus_nonneg hRate
      have hRewriteR :
          (w.state.totalBorrowAssets : ℚ) - (repayCost w.state sh : ℚ)
            + virtualBorrowAssets = R - cost := by
        dsimp [R, cost]; ring
      have hRewriteS :
          (w.state.debtShares.totalSupply : ℚ) - (sh : ℚ)
            + virtualBorrowShares = S - shQ := by
        dsimp [S, shQ]; ring
      rw [hRewriteR, hRewriteS]
      exact hGoal

/-- In the healable-budget region, a budgeted partial liquidation
preserves `AssetCovered`.

For the borrower, `HealableLiquidationBudget` supplies the closed-form slack
`bonus + price` covering one bonus-scaled repayment rounding unit and
one seized-collateral rounding unit.  For non-borrowers, the
`RepayDoesNotHitVirtualBorrowAsset` side condition keeps the remaining
borrow-share rate monotone. -/
private lemma liquidate_preserves_assetCovered
    {w w' : World} {lq b : Addr} {sh seized : ℕ}
    (hp : 0 < w.oracle.read_q)
    (hbk : Bookkeep w)
    (hAC : AssetCovered w)
    (hHealBudget : HealableLiquidationBudget w b)
    (hRepayBudget : RepayDoesNotHitVirtualBorrowAsset w sh)
    (hLiq : liquidate w lq b sh = some (w', seized)) :
    AssetCovered w' := by
  rw [AssetCovered_iff_shareMul] at hAC ⊢
  intro u
  obtain ⟨hTBA, hShTotal, hSeized, hCol_b, hCol_other, hSeized_le, _, hor⟩ :=
    liquidate_extract hLiq
  change repayCost w.state sh ≤ w.state.totalBorrowAssets at hRepayBudget
  have hCost_le_TBA := hRepayBudget
  have hBurn_le : sh ≤ w.state.debtShares.balances b :=
    liquidate_repaidShares_le_borrower_balance hLiq
  have hSh_le_total : sh ≤ w.state.debtShares.totalSupply := by
    have hBal_le := balance_le_totalSupply hbk.debtShareInv b
    omega
  have hCostBound :
      sh * (w.state.totalBorrowAssets + virtualBorrowAssets)
        ≤ repayCost w.state sh *
            (w.state.debtShares.totalSupply + virtualBorrowShares) := by
    unfold repayCost
    apply ceilDiv_mul_ge
    have := virtualBorrowShares_pos
    omega
  by_cases hub : u = b
  · subst u
    have hBal_b := liquidate_burns_repaidShares hLiq
    rw [hor, hBal_b, hTBA, hShTotal, hCol_b]
    rw [Nat.cast_sub hBurn_le, Nat.cast_sub hCost_le_TBA,
      Nat.cast_sub hSh_le_total, Nat.cast_sub hSeized_le]
    set Y : ℚ := (w.state.debtShares.balances b : ℚ)
    set C : ℚ := (w.state.collateral b : ℚ)
    set p : ℚ := w.oracle.read_q
    set R : ℚ := (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets
    set S : ℚ := (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares
    set cost : ℚ := (repayCost w.state sh : ℚ)
    set seizedQ : ℚ := (seized : ℚ)
    set shQ : ℚ := (sh : ℚ)
    set bonus : ℚ := liquidationIncentiveFactor_q
    set D : ℕ := debtOf w.state b
    have hp_q : 0 < p := by simpa [p] using hp
    have hbonus_ge : (1 : ℚ) ≤ bonus :=
      liquidationIncentiveFactor_q_ge_one
    have hbonus_nn : (0 : ℚ) ≤ bonus := le_trans zero_le_one hbonus_ge
    have hR_nn : 0 ≤ R := by
      dsimp [R]
      have hTBA_nn : (0 : ℚ) ≤ (w.state.totalBorrowAssets : ℚ) := by
        exact_mod_cast Nat.zero_le _
      have hvBA_nn : (0 : ℚ) ≤ (virtualBorrowAssets : ℕ) := by
        exact_mod_cast Nat.zero_le virtualBorrowAssets
      linarith
    have hS_pos : 0 < S := by
      dsimp [S]
      have hTs_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
        exact_mod_cast Nat.zero_le _
      have hvBS_pos : (0 : ℚ) < (virtualBorrowShares : ℕ) := by
        exact_mod_cast virtualBorrowShares_pos
      linarith
    have hYrem_nn : 0 ≤ Y - shQ := by
      have hle : shQ ≤ Y := by
        dsimp [Y, shQ]; exact_mod_cast hBurn_le
      linarith
    have hS_burn_nn : 0 ≤ S - shQ := by
      have hle : shQ ≤ (w.state.debtShares.totalSupply : ℚ) := by
        dsimp [shQ]; exact_mod_cast hSh_le_total
      dsimp [S]
      have hvBS_nn : (0 : ℚ) ≤ (virtualBorrowShares : ℕ) := by
        exact_mod_cast Nat.zero_le virtualBorrowShares
      linarith
    have hCD_nat :
        w.state.debtShares.balances b
            * (w.state.totalBorrowAssets + virtualBorrowAssets)
          ≤ D * (w.state.debtShares.totalSupply + virtualBorrowShares) := by
      dsimp [D]
      unfold debtOf repayCost
      apply ceilDiv_mul_ge
      have := virtualBorrowShares_pos
      omega
    have hCD_q : Y * R ≤ (D : ℚ) * S := by
      have hcast :
          ((w.state.debtShares.balances b
            * (w.state.totalBorrowAssets + virtualBorrowAssets) : ℕ) : ℚ)
            ≤
          ((D * (w.state.debtShares.totalSupply + virtualBorrowShares) : ℕ) : ℚ) := by
        exact_mod_cast hCD_nat
      push_cast at hcast
      simpa [Y, R, S] using hcast
    have hExactDebt_le_D : Y * R / S ≤ (D : ℚ) := by
      rw [div_le_iff₀ hS_pos]
      simpa [mul_assoc] using hCD_q
    have hBudget' :
        bonus + p ≤ C * p - (D : ℚ) * bonus := by
      simpa [HealableLiquidationBudget, Y, C, p, bonus, D] using hHealBudget
    have hExactDebtBonus_le :
        (Y * R / S) * bonus ≤ (D : ℚ) * bonus :=
      mul_le_mul_of_nonneg_right hExactDebt_le_D hbonus_nn
    have hCp_lower :
        (Y * R / S) * bonus + bonus + p ≤ C * p := by
      nlinarith
    have hCostUpper : cost ≤ shQ * R / S + 1 := by
      simpa [cost, shQ, R, S] using
        repayCost_le_shareValue_add_one w.state sh
    have hCostBonusUpper :
        cost * bonus + p ≤ (shQ * R / S) * bonus + bonus + p := by
      nlinarith [hCostUpper, hbonus_nn]
    have hSeizedUpper :
        seizedQ * p ≤ cost * bonus + p := by
      have hp_fixed : (0 : OraclePrice) < w.oracle.read := by
        -- `0 < w.oracle.read_q = mantissa / 10^36` ⟹ `0 < mantissa`,
        -- which is `(0 : OraclePrice) < w.oracle.read` definitionally.
        have hp' : (0 : ℚ) < ((w.oracle.read.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ 36 := hp
        have h10 : (0 : ℚ) < (10 : ℚ) ^ 36 := by positivity
        have h_nat : 0 < w.oracle.read.mantissa := by
          have := (div_pos_iff_of_pos_right h10).mp hp'
          exact_mod_cast this
        exact h_nat
      have h :=
        seizedFor_mul_price_le_cost_bonus_add_price
          (s := w.state) (p := w.oracle.read) (repaidShares := sh) hp_fixed
      simpa [seizedQ, cost, p, bonus, hSeized] using h
    have hSeizedUpper' :
        seizedQ * p ≤ (shQ * R / S) * bonus + bonus + p :=
      le_trans hSeizedUpper hCostBonusUpper
    have hRemainingValue :
        (Y - shQ) * R / S * bonus ≤ (C - seizedQ) * p := by
      have hdiff :
          (Y * R / S) * bonus - (shQ * R / S) * bonus
            = (Y - shQ) * R / S * bonus := by
        field_simp [ne_of_gt hS_pos]
      nlinarith
    have hBasePerShare :
        (Y - shQ) * R / S ≤ (C - seizedQ) * p := by
      have hnonneg : 0 ≤ (Y - shQ) * R / S := by
        exact div_nonneg (mul_nonneg hYrem_nn hR_nn) (le_of_lt hS_pos)
      have hbonus :
          (Y - shQ) * R / S ≤ (Y - shQ) * R / S * bonus := by
        nlinarith [hbonus_ge, hnonneg]
      exact le_trans hbonus hRemainingValue
    have hBorrowerPre :
        (Y - shQ) * R ≤ (C - seizedQ) * p * S := by
      have hmul :=
        mul_le_mul_of_nonneg_right hBasePerShare (le_of_lt hS_pos)
      rw [div_mul_cancel₀ _ (ne_of_gt hS_pos)] at hmul
      exact hmul
    have hRate : shQ * R ≤ cost * S := by
      have hcast :
          ((sh * (w.state.totalBorrowAssets + virtualBorrowAssets) : ℕ) : ℚ)
            ≤
          ((repayCost w.state sh
            * (w.state.debtShares.totalSupply + virtualBorrowShares) : ℕ) : ℚ) := by
        exact_mod_cast hCostBound
      push_cast at hcast
      simpa [shQ, R, S, cost] using hcast
    have hGoal :
        (Y - shQ) * (R - cost)
          ≤ (C - seizedQ) * p * (S - shQ) :=
      assetCovered_after_burn_rate_le
        (Yold := Y - shQ) (Ynew := Y - shQ)
        (C := C - seizedQ) (p := p) (R := R) (S := S)
        (cost := cost) (burned := shQ)
        hBorrowerPre le_rfl hYrem_nn hR_nn hS_pos hS_burn_nn hRate
    have hRewriteR :
        (w.state.totalBorrowAssets : ℚ) - (repayCost w.state sh : ℚ)
          + virtualBorrowAssets = R - cost := by
      dsimp [R, cost]; ring
    have hRewriteS :
        (w.state.debtShares.totalSupply : ℚ) - (sh : ℚ)
          + virtualBorrowShares = S - shQ := by
      dsimp [S, shQ]; ring
    rw [hRewriteR, hRewriteS]
    exact hGoal
  · have hBal_u : w'.state.debtShares.balances u = w.state.debtShares.balances u :=
      liquidate_debtShares_balances_other hLiq hub
    have hCol_u : w'.state.collateral u = w.state.collateral u :=
      hCol_other u hub
    rw [hor, hBal_u, hCol_u, hTBA, hShTotal]
    have hCastTBA :
        ((w.state.totalBorrowAssets - repayCost w.state sh : ℕ) : ℚ)
          = (w.state.totalBorrowAssets : ℚ) - (repayCost w.state sh : ℚ) :=
      Nat.cast_sub hCost_le_TBA
    have hCastSh :
        ((w.state.debtShares.totalSupply - sh : ℕ) : ℚ)
          = (w.state.debtShares.totalSupply : ℚ) - (sh : ℚ) :=
      Nat.cast_sub hSh_le_total
    rw [hCastTBA, hCastSh]
    set Y : ℚ := (w.state.debtShares.balances u : ℚ)
    set C : ℚ := (w.state.collateral u : ℚ)
    set p : ℚ := w.oracle.read_q
    set R : ℚ := (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets
    set S : ℚ := (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares
    set cost : ℚ := (repayCost w.state sh : ℚ)
    set shQ : ℚ := (sh : ℚ)
    have hGoalShape :
        Y * (R - cost) ≤ C * p * (S - shQ) := by
      have hAC_u : Y * R ≤ C * p * S := by
        have h := hAC u
        simpa [Y, C, p, R, S] using h
      have hRate_nat := hCostBound
      have hRate : shQ * R ≤ cost * S := by
        have hcast :
            ((sh * (w.state.totalBorrowAssets + virtualBorrowAssets) : ℕ) : ℚ)
              ≤
            ((repayCost w.state sh *
              (w.state.debtShares.totalSupply + virtualBorrowShares) : ℕ) : ℚ) := by
          exact_mod_cast hRate_nat
        push_cast at hcast
        simpa [shQ, R, S, cost] using hcast
      have hS_pos : 0 < S := by
        dsimp [S]
        have hTs_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
          exact_mod_cast Nat.zero_le _
        have hV_pos : (0 : ℚ) < (virtualBorrowShares : ℕ) := by
          exact_mod_cast virtualBorrowShares_pos
        linarith
      have hS_minus_nonneg : 0 ≤ S - shQ := by
        have hsh_le : shQ ≤ (w.state.debtShares.totalSupply : ℚ) := by
          have hcast : (sh : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
            exact_mod_cast hSh_le_total
          simpa [shQ] using hcast
        dsimp [S, shQ] at hsh_le ⊢
        have hV_nn : (0 : ℚ) ≤ (virtualBorrowShares : ℕ) := by
          exact_mod_cast Nat.zero_le virtualBorrowShares
        linarith
      have hY_nn : 0 ≤ Y := by
        dsimp [Y]; exact_mod_cast Nat.zero_le _
      have hR_nn : 0 ≤ R := by
        dsimp [R]
        have hTBA_nn : (0 : ℚ) ≤ (w.state.totalBorrowAssets : ℚ) := by
          exact_mod_cast Nat.zero_le _
        have hvBA_nn : (0 : ℚ) ≤ (virtualBorrowAssets : ℕ) := by
          exact_mod_cast Nat.zero_le virtualBorrowAssets
        linarith
      exact assetCovered_after_burn_rate_le
        (Yold := Y) (Ynew := Y) (C := C) (p := p)
        (R := R) (S := S) (cost := cost) (burned := shQ)
        hAC_u le_rfl hY_nn hR_nn hS_pos hS_minus_nonneg hRate
    have hRewriteR :
        (w.state.totalBorrowAssets : ℚ) - (repayCost w.state sh : ℚ)
          + virtualBorrowAssets = R - cost := by
      dsimp [R, cost]; ring
    have hRewriteS :
        (w.state.debtShares.totalSupply : ℚ) - (sh : ℚ)
          + virtualBorrowShares = S - shQ := by
      dsimp [S, shQ]; ring
    rw [hRewriteR, hRewriteS]
    exact hGoalShape

/-- Under positive price, an `AssetCovered` state cannot execute
`writeOff`: exhausted collateral with positive debt shares contradicts
the per-user coverage inequality. -/
private lemma writeOff_impossible_of_assetCovered
    {w w' : World} {borrower : Addr}
    (_hp : 0 < w.oracle.read_q)
    (hAC : AssetCovered w)
    (hwo : writeOff w borrower = some w') :
    False := by
  rw [AssetCovered_iff_shareMul] at hAC
  obtain ⟨hCol, hShares_pos, _, _, _, _⟩ := writeOff_extract hwo
  have hAC_b := hAC borrower
  rw [hCol] at hAC_b
  simp only [Nat.cast_zero, zero_mul] at hAC_b
  have hLHS_pos :
      0 <
        (w.state.debtShares.balances borrower : ℚ)
          * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets) := by
    have hShares_pos_q :
        (0 : ℚ) < (w.state.debtShares.balances borrower : ℚ) := by
      exact_mod_cast hShares_pos
    have hR_pos :
        0 < (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets := by
      have hTBA_nn : (0 : ℚ) ≤ (w.state.totalBorrowAssets : ℚ) := by
        exact_mod_cast Nat.zero_le _
      have hvBA_pos : (0 : ℚ) < (virtualBorrowAssets : ℕ) := by
        exact_mod_cast virtualBorrowAssets_pos
      linarith
    exact mul_pos hShares_pos_q hR_pos
  nlinarith

/-! ## Step-level

Budgeted user-op preservation.  Environment actions are excluded by
`NoPriceMove` and `NoAccrual`; their `AllHealthy → AssetCovered`
preservation lives in `AllHealthyToAssetCovered.lean`
(`accrueInterest_preserves_assetCovered` and
`priceTick_preserves_assetCovered`).

The two action-level step budgets `LiquidateStepBudget` and
`BurnStepBudget` are mutually independent and supplied separately:
`LiquidateStepBudget` carries the borrower-local
`HealableLiquidationBudget`, `BurnStepBudget` carries
`RepayDoesNotHitVirtualBorrowAsset` for the share-burn actions
(`userRepay` / `userLiquidate`). -/

theorem step_preserves_assetCovered
    {a : Action} {w w' : World}
    (hp : 0 < w.oracle.read_q)
    (h_pm : NoPriceMove a)
    (h_acc : NoAccrual a)
    (hbk : Bookkeep w)
    (hAC : AssetCovered w)
    (h_liq : LiquidateStepBudget a w)
    (h_burn : BurnStepBudget a w)
    (hstep : step a w = some w') :
    AssetCovered w' := by
  cases a with
  | userSupply user assets =>
    obtain ⟨shares, hsup⟩ := step_userSupply_some hstep
    exact supply_preserves_assetCovered hAC hsup
  | userWithdraw user shares =>
    obtain ⟨assets, hw⟩ := step_userWithdraw_some hstep
    exact withdraw_preserves_assetCovered hAC hw
  | userSupplyCollateral user c =>
    exact supplyCollateral_preserves_assetCovered
      (le_of_lt hp) hAC (step_userSupplyCollateral_some hstep)
  | userWithdrawCollateral user c =>
    exact withdrawCollateral_preserves_assetCovered
      hAC (step_userWithdrawCollateral_some hstep)
  | userBorrow user assets =>
    obtain ⟨shares, hb⟩ := step_userBorrow_some hstep
    exact borrow_preserves_assetCovered hAC hb
  | userRepay user shares =>
    obtain ⟨assets, hr⟩ := step_userRepay_some hstep
    have hRepayBudget : RepayDoesNotHitVirtualBorrowAsset w shares := h_burn
    exact repay_preserves_assetCovered hbk hAC hRepayBudget hr
  | userLiquidate lq borrower shares =>
    obtain ⟨seized, hl⟩ := step_userLiquidate_some hstep
    have hHealBudget : HealableLiquidationBudget w borrower := h_liq
    have hRepayBudget : RepayDoesNotHitVirtualBorrowAsset w shares := h_burn
    exact liquidate_preserves_assetCovered hp hbk hAC hHealBudget hRepayBudget hl
  | userWriteOff borrower =>
    exact False.elim
      (writeOff_impossible_of_assetCovered hp hAC
        (step_userWriteOff_some hstep))
  | envAccrueInt Δ =>
    exact absurd h_acc (by simp [NoAccrual])
  | envPriceTick p' =>
    exact absurd h_pm (by simp [NoPriceMove])

end Market
