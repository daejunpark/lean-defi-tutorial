import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas

/-!
# Lending Market — AllHealthy preservation

`AllHealthy w := ∀ u, Healthy w u`, where `Healthy w u` asks the
debt at `u` to be no more than `w.state.collateral u · Oracle.read w.oracle · lltv`.
This file proves that every user op preserves `AllHealthy`.
`envAccrueInt` is excluded by `NoAccrual` and `envPriceTick` by
`NoPriceMove` — both break `AllHealthy` in general (this is exactly
why `AssetCovered` exists as a more durable layer; see
`AssetCovered.lean`).

## Main theorem
- `step_preserves_allHealthy`

The per-op preservation lemmas (`<op>_preserves_allHealthy`) are
public — they are reused by `AllHealthyToAssetCovered.lean` to chain
into `AssetCovered`.  The arithmetic / ledger-shape helpers below
are `private` to this file.
-/

namespace Market

open Util (ceilDiv ceilDiv_mul_ge ceilDiv_le_iff_le_mul)

/-! ## Helper lemmas (private — skip on first read) -/

private lemma ceilDiv_le_of_rate_le
    (Y num1 den1 num2 den2 : ℕ)
    (hden1 : 0 < den1) (hden2 : 0 < den2)
    (hrate : num1 * den2 ≤ num2 * den1) :
    ceilDiv (Y * num1) den1 ≤ ceilDiv (Y * num2) den2 := by
  rw [ceilDiv_le_iff_le_mul _ _ _ hden1]
  have hM : Y * num2 ≤ ceilDiv (Y * num2) den2 * den2 := ceilDiv_mul_ge _ hden2
  have h1 : Y * num1 * den2 ≤ Y * num2 * den1 := by
    have hr : Y * (num1 * den2) ≤ Y * (num2 * den1) := Nat.mul_le_mul_left Y hrate
    have e1 : Y * (num1 * den2) = Y * num1 * den2 := by ring
    have e2 : Y * (num2 * den1) = Y * num2 * den1 := by ring
    omega
  have h2 : Y * num2 * den1 ≤ ceilDiv (Y * num2) den2 * den2 * den1 :=
    Nat.mul_le_mul_right den1 hM
  have h3 : ceilDiv (Y * num2) den2 * den2 * den1
          = ceilDiv (Y * num2) den2 * den1 * den2 := by ring
  have h4 : Y * num1 * den2 ≤ ceilDiv (Y * num2) den2 * den1 * den2 := by omega
  exact Nat.le_of_mul_le_mul_right h4 hden2

private lemma ceilDiv_mono_left {a b c : ℕ} (h : a ≤ b) :
    ceilDiv a c ≤ ceilDiv b c := by
  unfold ceilDiv
  apply Nat.div_le_div_right
  omega

/-- Workhorse helper for "frame" cases: if the post-state's debt at
`u` is no greater than the pre-state's, and its collateral at `u`
is no less, then the per-state-and-price two-floor `HealthyOnState`
predicate is preserved.

In the new Fixed-form `HealthyOnState`, no oracle-price nonnegativity
hypothesis is needed — the predicate is over `Nat` mantissas, and
both `Fixed.mulFloor` steps are monotone in `s.collateral u`. -/
private lemma healthyOnState_preserved_of_debt_le_collat_ge
    {s s' : State} {u : Addr} {p : OraclePrice}
    (hd : debtOf s' u ≤ debtOf s u)
    (hc : s.collateral u ≤ s'.collateral u)
    (h : HealthyOnState s p u) :
    HealthyOnState s' p u := by
  unfold HealthyOnState at h ⊢
  -- The two `mulFloorAt`s reduce to chained Nat (mul + div) operations
  -- on `s.collateral u`, each of which is monotone.
  have h_cv_mantissa_le :
      (Fixed.mulFloorAt (Fixed.ofNat (s.collateral u)) p 0 (by omega)).mantissa
        ≤ (Fixed.mulFloorAt (Fixed.ofNat (s'.collateral u)) p 0 (by omega)).mantissa := by
    simp only [Fixed.mulFloorAt_mantissa, Fixed.ofNat_mantissa]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ hc)
  have h_mb_le :
      (Fixed.mulFloorAt
          (Fixed.mulFloorAt (Fixed.ofNat (s.collateral u)) p 0 (by omega))
          lltv 0 (by omega)).mantissa
        ≤ (Fixed.mulFloorAt
            (Fixed.mulFloorAt (Fixed.ofNat (s'.collateral u)) p 0 (by omega))
            lltv 0 (by omega)).mantissa := by
    simp only [Fixed.mulFloorAt_mantissa]
    exact Nat.div_le_div_right (Nat.mul_le_mul_right _ h_cv_mantissa_le)
  exact le_trans (le_trans hd h) h_mb_le

/-! ## Per-op preservation lemmas -/

lemma supply_preserves_allHealthy
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (hAH : AllHealthy w) (hsup : supply w user assets = some (w', shares)) :
    AllHealthy w' := by
  unfold supply at hsup
  split at hsup
  · simp at hsup
  · next loan' _ =>
    simp only [Option.some.injEq, Prod.mk.injEq] at hsup
    obtain ⟨rfl, _⟩ := hsup
    intro v
    exact hAH v

lemma withdraw_preserves_allHealthy
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (hAH : AllHealthy w) (hw : withdraw w user shares = some (w', assets)) :
    AllHealthy w' := by
  unfold withdraw at hw
  split at hw
  · simp at hw
  · next _ =>
    split at hw
    · simp at hw
    · next _ _ =>
      split at hw
      · simp at hw
      · next loan' _ =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hw
        obtain ⟨rfl, _⟩ := hw
        intro v
        exact hAH v

lemma supplyCollateral_preserves_allHealthy
    {w w' : World} {user : Addr} {c : ℕ}
    (hAH : AllHealthy w) (hsc : supplyCollateral w user c = some w') :
    AllHealthy w' := by
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
      have h : HealthyOnState w.state w.oracle.read v := hAH v
      set s' : State :=
        { w.state with
          collateralAsset := col'
          collateral := w.state.collateral.update user (w.state.collateral user + c) }
      have hd : debtOf s' v ≤ debtOf w.state v := Nat.le_refl _
      have hc : w.state.collateral v ≤ s'.collateral v := by
        show w.state.collateral v ≤ (w.state.collateral.update user (w.state.collateral user + c)) v
        rw [Finsupp.update_apply]
        by_cases huv : v = user
        · rw [if_pos huv, huv]; omega
        · rw [if_neg huv]
      show HealthyOnState s' w.oracle.read v
      exact healthyOnState_preserved_of_debt_le_collat_ge hd hc h

lemma withdrawCollateral_preserves_allHealthy
    {w w' : World} {user : Addr} {c : ℕ}
    (hAH : AllHealthy w) (hw : withdrawCollateral w user c = some w') :
    AllHealthy w' := by
  unfold withdrawCollateral at hw
  split at hw
  · simp at hw
  · split at hw
    · simp at hw
    · next col' _ =>
      split at hw
      · next hHealth =>
        simp only [Option.some.injEq] at hw
        rw [← hw]
        intro v
        by_cases huv : v = user
        · subst huv
          exact hHealth
        · have h : HealthyOnState w.state w.oracle.read v := hAH v
          unfold afterWithdrawCollateral
          set s' : State :=
            { w.state with
                collateralAsset := col'
                collateral :=
                  w.state.collateral.update user (w.state.collateral user - c) }
          have hd : debtOf s' v ≤ debtOf w.state v := Nat.le_refl _
          have hc : w.state.collateral v ≤ s'.collateral v := by
            show w.state.collateral v
                ≤ (w.state.collateral.update user (w.state.collateral user - c)) v
            rw [Finsupp.update_apply, if_neg huv]
          exact healthyOnState_preserved_of_debt_le_collat_ge hd hc h
      · simp at hw

lemma borrow_preserves_allHealthy
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (hAH : AllHealthy w)
    (hb : borrow w user assets = some (w', shares)) :
    AllHealthy w' := by
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
        obtain ⟨rfl, _⟩ := hb
        intro v
        by_cases huv : v = user
        · subst huv
          exact hHealth
        · have h : HealthyOnState w.state w.oracle.read v := hAH v
          unfold afterBorrow
          set s' : State :=
            { w.state with
              loanAsset := loan'
              debtShares := ERC20.mint w.state.debtShares user (borrowShareFor w.state assets)
              totalBorrowAssets := w.state.totalBorrowAssets + assets } with hs'_def
          have hbal :
              (ERC20.mint w.state.debtShares user (borrowShareFor w.state assets)).balances v
              = w.state.debtShares.balances v := by
            show (w.state.debtShares.balances +
                    Finsupp.single user (borrowShareFor w.state assets)) v
                = w.state.debtShares.balances v
            rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (Ne.symm huv)]
            omega
          have hdebt_le : debtOf s' v ≤ debtOf w.state v := by
            unfold debtOf repayCost
            show ceilDiv
                (s'.debtShares.balances v *
                 (s'.totalBorrowAssets + virtualBorrowAssets))
                (s'.debtShares.totalSupply + virtualBorrowShares)
              ≤ ceilDiv (w.state.debtShares.balances v *
                  (w.state.totalBorrowAssets + virtualBorrowAssets))
                  (w.state.debtShares.totalSupply + virtualBorrowShares)
            show ceilDiv
                ((ERC20.mint w.state.debtShares user (borrowShareFor w.state assets)).balances v *
                 (w.state.totalBorrowAssets + assets + virtualBorrowAssets))
                ((ERC20.mint w.state.debtShares user (borrowShareFor w.state assets)).totalSupply +
                 virtualBorrowShares)
              ≤ ceilDiv (w.state.debtShares.balances v *
                  (w.state.totalBorrowAssets + virtualBorrowAssets))
                  (w.state.debtShares.totalSupply + virtualBorrowShares)
            rw [hbal, mint_totalSupply]
            have eq1 : w.state.totalBorrowAssets + assets + virtualBorrowAssets
                     = (w.state.totalBorrowAssets + virtualBorrowAssets) + assets := by omega
            have eq2 : w.state.debtShares.totalSupply + borrowShareFor w.state assets +
                         virtualBorrowShares
                     = (w.state.debtShares.totalSupply + virtualBorrowShares) +
                         borrowShareFor w.state assets := by omega
            rw [eq1, eq2]
            apply ceilDiv_le_of_rate_le
            · have := virtualBorrowShares_pos; omega
            · have := virtualBorrowShares_pos; omega
            · have hbnd := borrowShareFor_bound w.state assets
              have e1 : (w.state.totalBorrowAssets + virtualBorrowAssets + assets) *
                          (w.state.debtShares.totalSupply + virtualBorrowShares)
                      = (w.state.totalBorrowAssets + virtualBorrowAssets) *
                          (w.state.debtShares.totalSupply + virtualBorrowShares)
                      + assets *
                          (w.state.debtShares.totalSupply + virtualBorrowShares) := by ring
              have e2 : (w.state.totalBorrowAssets + virtualBorrowAssets) *
                          (w.state.debtShares.totalSupply + virtualBorrowShares +
                            borrowShareFor w.state assets)
                      = (w.state.totalBorrowAssets + virtualBorrowAssets) *
                          (w.state.debtShares.totalSupply + virtualBorrowShares)
                      + (w.state.totalBorrowAssets + virtualBorrowAssets) *
                          borrowShareFor w.state assets := by ring
              have hcomm : (w.state.totalBorrowAssets + virtualBorrowAssets) *
                              borrowShareFor w.state assets
                         = borrowShareFor w.state assets *
                              (w.state.totalBorrowAssets + virtualBorrowAssets) := by ring
              omega
          have hcol_ge : w.state.collateral v ≤ s'.collateral v := Nat.le_refl _
          show HealthyOnState s' w.oracle.read v
          exact healthyOnState_preserved_of_debt_le_collat_ge hdebt_le hcol_ge h
      · simp at hb

/-- `userRepay` preserves `AllHealthy`.  Uses `virtualBorrowAssets = 1`
to handle the ℕ-truncation case (`repayCost > totalBorrowAssets`) cleanly:
under that axiom, the new per-share debt for any non-actor is bounded
by `1`, so existing positive `debtOf` values are preserved. -/
lemma repay_preserves_allHealthy
    {w w' : World} {user : Addr} {shares assets : ℕ}
    (hbk : Bookkeep w) (hAH : AllHealthy w)
    (hr : repay w user shares = some (w', assets)) :
    AllHealthy w' := by
  unfold repay at hr
  split at hr
  · simp at hr
  · next loan' _ =>
    split at hr
    · simp at hr
    · next debt' hburn =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, _⟩ := hr
      have hbalU := burn_amount_le hburn
      have hbalU_le := balance_le_totalSupply hbk.debtShareInv user
      have hkS : shares ≤ w.state.debtShares.totalSupply := by omega
      have hburnTS := burn_totalSupply hburn
      have hbk_debt' : ERC20.Invariant debt' :=
        ERC20.burn_preserves_invariant hbk.debtShareInv hburn
      have hvBSpos : 0 < virtualBorrowShares := virtualBorrowShares_pos
      intro v
      have h : HealthyOnState w.state w.oracle.read v := hAH v
      have hYbnd : debt'.balances v ≤ debt'.totalSupply :=
        balance_le_totalSupply hbk_debt' v
      have hYbnd' : debt'.balances v ≤ w.state.debtShares.totalSupply - shares := by
        rw [hburnTS] at hYbnd; exact hYbnd
      have hY_le : debt'.balances v ≤ w.state.debtShares.balances v := by
        by_cases huv : v = user
        · subst huv
          rw [burn_balances_self hburn]; omega
        · rw [burn_balances_other hburn huv]
      set s' : State :=
        { w.state with
          loanAsset := loan'
          debtShares := debt'
          totalBorrowAssets := w.state.totalBorrowAssets - repayCost w.state shares } with hs'_def
      have hcol_ge : w.state.collateral v ≤ s'.collateral v := Nat.le_refl _
      show HealthyOnState s' w.oracle.read v
      apply healthyOnState_preserved_of_debt_le_collat_ge ?_ hcol_ge h
      -- Goal: debtOf s' v ≤ debtOf w.state v
      show ceilDiv (s'.debtShares.balances v *
              (s'.totalBorrowAssets + virtualBorrowAssets))
              (s'.debtShares.totalSupply + virtualBorrowShares)
         ≤ ceilDiv (w.state.debtShares.balances v *
              (w.state.totalBorrowAssets + virtualBorrowAssets))
              (w.state.debtShares.totalSupply + virtualBorrowShares)
      show ceilDiv (debt'.balances v *
              (w.state.totalBorrowAssets - repayCost w.state shares + virtualBorrowAssets))
              (debt'.totalSupply + virtualBorrowShares)
         ≤ ceilDiv (w.state.debtShares.balances v *
              (w.state.totalBorrowAssets + virtualBorrowAssets))
              (w.state.debtShares.totalSupply + virtualBorrowShares)
      rw [virtualBorrowAssets_eq_one, hburnTS]
      by_cases hcost : repayCost w.state shares ≤ w.state.totalBorrowAssets
      · calc ceilDiv (debt'.balances v *
                        (w.state.totalBorrowAssets - repayCost w.state shares + 1))
                     (w.state.debtShares.totalSupply - shares + virtualBorrowShares)
            ≤ ceilDiv (w.state.debtShares.balances v *
                          (w.state.totalBorrowAssets - repayCost w.state shares + 1))
                       (w.state.debtShares.totalSupply - shares + virtualBorrowShares) := by
              exact ceilDiv_mono_left (Nat.mul_le_mul_right _ hY_le)
          _ ≤ ceilDiv (w.state.debtShares.balances v * (w.state.totalBorrowAssets + 1))
                       (w.state.debtShares.totalSupply + virtualBorrowShares) := by
              apply ceilDiv_le_of_rate_le
              · omega
              · omega
              · have hcb : repayCost w.state shares *
                              (w.state.debtShares.totalSupply + virtualBorrowShares)
                         ≥ shares * (w.state.totalBorrowAssets + virtualBorrowAssets) := by
                  unfold repayCost
                  apply ceilDiv_mul_ge
                  omega
                rw [virtualBorrowAssets_eq_one] at hcb
                have e1 :
                    (w.state.totalBorrowAssets - repayCost w.state shares + 1) *
                      (w.state.debtShares.totalSupply + virtualBorrowShares)
                    + repayCost w.state shares *
                      (w.state.debtShares.totalSupply + virtualBorrowShares)
                  = (w.state.totalBorrowAssets + 1) *
                      (w.state.debtShares.totalSupply + virtualBorrowShares) := by
                  rw [← Nat.add_mul]
                  have : w.state.totalBorrowAssets - repayCost w.state shares + 1 +
                         repayCost w.state shares = w.state.totalBorrowAssets + 1 := by omega
                  rw [this]
                have e2 :
                    (w.state.totalBorrowAssets + 1) *
                      (w.state.debtShares.totalSupply - shares + virtualBorrowShares)
                    + (w.state.totalBorrowAssets + 1) * shares
                  = (w.state.totalBorrowAssets + 1) *
                      (w.state.debtShares.totalSupply + virtualBorrowShares) := by
                  rw [← Nat.mul_add]
                  have : w.state.debtShares.totalSupply - shares + virtualBorrowShares +
                         shares = w.state.debtShares.totalSupply + virtualBorrowShares := by
                    omega
                  rw [this]
                have hcomm : (w.state.totalBorrowAssets + 1) * shares
                           = shares * (w.state.totalBorrowAssets + 1) := Nat.mul_comm _ _
                omega
      · push Not at hcost
        have htrunc : w.state.totalBorrowAssets - repayCost w.state shares = 0 := by omega
        rw [htrunc]
        by_cases hYnew : debt'.balances v = 0
        · rw [hYnew, Nat.zero_mul]
          unfold ceilDiv
          rw [Nat.div_eq_of_lt (by omega)]
          exact Nat.zero_le _
        · have hYnew_pos : 0 < debt'.balances v := by omega
          have hYold_pos : 0 < w.state.debtShares.balances v := by omega
          have hLHS_le : ceilDiv (debt'.balances v * (0 + 1))
                          (w.state.debtShares.totalSupply - shares + virtualBorrowShares) ≤ 1 := by
            rw [ceilDiv_le_iff_le_mul _ _ _ (by omega)]
            simp only [Nat.zero_add, Nat.mul_one, Nat.one_mul]
            omega
          have hRHS_ge : 1 ≤ ceilDiv
              (w.state.debtShares.balances v * (w.state.totalBorrowAssets + 1))
              (w.state.debtShares.totalSupply + virtualBorrowShares) := by
            unfold ceilDiv
            apply Nat.div_pos
            · have : 0 < w.state.debtShares.balances v * (w.state.totalBorrowAssets + 1) :=
                Nat.mul_pos hYold_pos (by omega)
              omega
            · omega
          omega

/-! ## Liquidate / writeOff: vacuous under `AllHealthy`

Both operations' guards contradict `AllHealthy w`:
* `liquidate` requires `¬ Healthy w borrower`, directly contradicting
  `AllHealthy w borrower`.
* `writeOff` requires `collateral borrower = 0 ∧ debtShares borrower > 0`.
  Under `AllHealthy w` and `0 ≤ Oracle.read w.oracle`, `debtOf borrower
  ≤ 0`, but `debtShares borrower > 0` forces `debtOf borrower ≥ 1`
  (via the `ceilDiv` lower bound).
-/

lemma liquidate_preserves_allHealthy
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (hAH : AllHealthy w)
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    AllHealthy w' := by
  obtain ⟨_, _, _, _, _, _, hUnhealthy, _⟩ := liquidate_extract hl
  exact absurd (hAH borrower) hUnhealthy

lemma writeOff_preserves_allHealthy
    {w w' : World} {borrower : Addr}
    (hAH : AllHealthy w) (hwo : writeOff w borrower = some w') :
    AllHealthy w' := by
  obtain ⟨hCol, hSh, _, _, _, _⟩ := writeOff_extract hwo
  -- AllHealthy at borrower gives `debtOf ≤ maxBorrow.mantissa`.  With
  -- `collateral borrower = 0`, both `Fixed.mulFloor` operations send
  -- `maxBorrow.mantissa` to 0, so `debtOf borrower = 0` — contradicting
  -- `debtShares.balances borrower > 0` (which forces `debtOf ≥ 1`).
  exfalso
  have hHealthy : HealthyOnState w.state w.oracle.read borrower := hAH borrower
  unfold HealthyOnState at hHealthy
  rw [hCol] at hHealthy
  simp only [Fixed.le_iff_mantissa, Fixed.mulFloorAt_mantissa, Fixed.ofNat_mantissa,
             Nat.zero_mul, Nat.zero_div] at hHealthy
  -- hHealthy now reads `debtOf w.state borrower ≤ 0`.
  have hdebt_zero : debtOf w.state borrower = 0 := by omega
  -- But `dsh borrower > 0` ⟹ `debtOf borrower ≥ 1`.
  have hdebt_pos : 0 < debtOf w.state borrower := by
    unfold debtOf repayCost Util.ceilDiv
    have hvBA := virtualBorrowAssets_pos
    have hvBS := virtualBorrowShares_pos
    have hnum :
        0 < w.state.debtShares.balances borrower *
              (w.state.totalBorrowAssets + virtualBorrowAssets) :=
      Nat.mul_pos hSh (by omega)
    have hden : 0 < w.state.debtShares.totalSupply + virtualBorrowShares := by omega
    apply Nat.div_pos
    · omega
    · exact hden
  omega

/-! ## Main theorem -/

theorem step_preserves_allHealthy {a : Action} {w w' : World}
    (h_pm : NoPriceMove a) (h_acc : NoAccrual a)
    (hbk : Bookkeep w) (hAH : AllHealthy w)
    (hstep : step a w = some w') :
    AllHealthy w' := by
  cases a with
  | userSupply u amt =>
    obtain ⟨_, hsup⟩ := step_userSupply_some hstep
    exact supply_preserves_allHealthy hAH hsup
  | userWithdraw u sh =>
    obtain ⟨_, hwd⟩ := step_userWithdraw_some hstep
    exact withdraw_preserves_allHealthy hAH hwd
  | userSupplyCollateral u c =>
    exact supplyCollateral_preserves_allHealthy hAH
      (step_userSupplyCollateral_some hstep)
  | userWithdrawCollateral u c =>
    exact withdrawCollateral_preserves_allHealthy hAH
      (step_userWithdrawCollateral_some hstep)
  | userBorrow u amt =>
    obtain ⟨_, hb⟩ := step_userBorrow_some hstep
    exact borrow_preserves_allHealthy hAH hb
  | userRepay u sh =>
    obtain ⟨_, hr⟩ := step_userRepay_some hstep
    exact repay_preserves_allHealthy hbk hAH hr
  | userLiquidate lq br sh =>
    obtain ⟨_, hl⟩ := step_userLiquidate_some hstep
    exact liquidate_preserves_allHealthy hAH hl
  | userWriteOff br =>
    exact writeOff_preserves_allHealthy hAH (step_userWriteOff_some hstep)
  | envAccrueInt Δ =>
    exact absurd h_acc (by simp [NoAccrual])
  | envPriceTick p' =>
    exact absurd h_pm (by simp [NoPriceMove])

end Market
