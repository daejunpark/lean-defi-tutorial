import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas
import Proofs.Accounting

/-!
# Lending Market — Phase C-1 headline theorems

User-facing safety properties of `liquidate` and `writeOff`, region
analysis for the borrower's state-space, and the budgeted healing
existence theorem.

## Contents

- **Headline safety**: `liquidate_requires_unhealth`,
  `liquidate_decreases_TBA`, `liquidate_profits_liquidator`,
  `writeOff_requires_exhausted_collateral`, `writeOff_clears_debt`.
  (`liquidate_burns_repaidShares` lives in `Lemmas.lean` since it is
  reused as a shape lemma.)
- **Region analysis**: `bad_debt_path_implies_unhealthy`,
  `liquidate_full_burn_fails_in_bad_debt_path`,
  `liquidate_bad_debt_path_dsh_pos`,
  `liquidate_preserves_bad_debt_path` (T3).
- **Healing existence**: the full-burn healing theorem
  `exists_full_liquidation_to_healthy`, with two private bridges
  (`healable_of_healableLiquidationBudget`,
  `fullLiquidationSeized_le_collateral_of_healableLiquidationBudget`).
  The market wallet's collateral availability is discharged via
  `MarketAccounting`, not as a separate hypothesis.

The region predicates `Healable` / `BadDebtPath` and the budget
predicate `HealableLiquidationBudget` are defined in `Defs.Predicates`.
-/

namespace Market

open Util (ceilDiv ceilDiv_mul_ge le_ceilDiv)

/-! ## Headline safety -/

theorem liquidate_requires_unhealth
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    ¬ Healthy w borrower :=
  (liquidate_extract hl).2.2.2.2.2.2.1

theorem liquidate_decreases_TBA
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    w'.state.totalBorrowAssets =
        w.state.totalBorrowAssets - repayCost w.state repaidShares :=
  (liquidate_extract hl).1

/-- Liquidator's profit: the value of seized collateral (in
loan-asset units, valued at the oracle price `p`) is at least the
loan asset deposited.  Holds under `0 < p`; consequence of
`liquidationIncentiveFactor ≥ 1` and the ceil rounding in
`seizedFor`. -/
theorem liquidate_profits_liquidator
    {w w' : World} {liquidator borrower : Addr} {repaidShares seized : ℕ}
    (hp : (0 : OraclePrice) < w.oracle.read)
    (hl : liquidate w liquidator borrower repaidShares = some (w', seized)) :
    (repayCost w.state repaidShares : ℚ) ≤ (seized : ℚ) * w.oracle.read_q := by
  obtain ⟨_, _, hSeized, _, _, _, _, _⟩ := liquidate_extract hl
  -- Lower bound: `seized * p ≥ repayCost * bonus ≥ repayCost`.
  have h_lower :=
    cost_bonus_le_seizedFor_mul_price (s := w.state)
      (p := w.oracle.read) (repaidShares := repaidShares) hp
  have hrepaid_nn : (0 : ℚ) ≤ (repayCost w.state repaidShares : ℕ) := by
    exact_mod_cast Nat.zero_le _
  have hbonus_ge : (1 : ℚ) ≤ liquidationIncentiveFactor_q :=
    liquidationIncentiveFactor_q_ge_one
  have hrb_ge : (repayCost w.state repaidShares : ℚ)
                  ≤ (repayCost w.state repaidShares : ℚ) * liquidationIncentiveFactor_q := by
    nlinarith [hrepaid_nn, hbonus_ge]
  rw [hSeized]
  show (repayCost w.state repaidShares : ℚ)
        ≤ (seizedFor w.state w.oracle.read repaidShares : ℚ) * w.oracle.read_q
  linarith

theorem writeOff_requires_exhausted_collateral
    {w w' : World} {borrower : Addr}
    (hwo : writeOff w borrower = some w') :
    w.state.collateral borrower = 0 ∧ 0 < w.state.debtShares.balances borrower :=
  ⟨(writeOff_extract hwo).1, (writeOff_extract hwo).2.1⟩

theorem writeOff_clears_debt
    {w w' : World} {borrower : Addr}
    (hwo : writeOff w borrower = some w') :
    w'.state.debtShares.balances borrower = 0 :=
  (writeOff_extract hwo).2.2.2.2.1

/-! ## Region analysis

`Healable` and `BadDebtPath` (defined in `Defs.Predicates`) partition the
borrower's state-space.  These four theorems describe how
`liquidate`'s outcome depends on the region. -/

/-- `BadDebtPath w b ⟹ ¬ Healthy w b`.  Consumes the structural
constraint `bonus · lltv < 1` from `Proofs.Lemmas`.

Mechanically: BadDebtPath says `C · p · S < Y · R · bonus`.
Multiply by `lltv > 0`: `C · p · lltv · S < Y · R · bonus · lltv ≤ Y · R`
(using `bonus · lltv < 1`).  Combined with the ceilDiv lower bound
`debtOf · S ≥ Y · R`, we get `debtOf · S > C · p · lltv · S`, hence
`debtOf > C · p · lltv` (since `S > 0`). -/
theorem bad_debt_path_implies_unhealthy
    {w : World} {b : Addr}
    (hBDP : BadDebtPath w b) :
    ¬ Healthy w b := by
  rw [BadDebtPath_iff_shareMul] at hBDP
  intro hH_fixed
  -- Pull the ℚ-form `debt ≤ coll · price · lltv` out of the two-floor
  -- `Healthy`, then derive the contradiction with the original algebra.
  have hH := Healthy.toQForm hH_fixed
  have hS_pos : 0 < w.state.debtShares.totalSupply + virtualBorrowShares := by
    have := virtualBorrowShares_pos; omega
  have hSq_pos : (0 : ℚ) <
      (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    have := virtualBorrowShares_pos
    have h1 : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
      exact_mod_cast Nat.zero_le _
    have h2 : (0 : ℚ) < (virtualBorrowShares : ℚ) := by exact_mod_cast this
    linarith
  have hSq_nn : (0 : ℚ) ≤
      (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := le_of_lt hSq_pos
  have hCD :
      w.state.debtShares.balances b *
        (w.state.totalBorrowAssets + virtualBorrowAssets)
      ≤ debtOf w.state b *
        (w.state.debtShares.totalSupply + virtualBorrowShares) := by
    unfold debtOf repayCost; exact ceilDiv_mul_ge _ hS_pos
  have hCD_q :
      (w.state.debtShares.balances b : ℚ) *
        ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
      ≤ (debtOf w.state b : ℚ) *
        ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
    have h := hCD
    have hcast : (((w.state.debtShares.balances b *
        (w.state.totalBorrowAssets + virtualBorrowAssets) : ℕ) : ℚ)
      ≤ ((debtOf w.state b *
        (w.state.debtShares.totalSupply + virtualBorrowShares) : ℕ) : ℚ)) := by
      exact_mod_cast h
    push_cast at hcast
    linarith
  have h1 : (debtOf w.state b : ℚ) *
              ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
            ≤ (w.state.collateral b : ℚ) * w.oracle.read_q * lltv_q *
              ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) :=
    mul_le_mul_of_nonneg_right hH hSq_nn
  have h2 : (w.state.debtShares.balances b : ℚ) *
              ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
            ≤ (w.state.collateral b : ℚ) * w.oracle.read_q * lltv_q *
              ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) :=
    le_trans hCD_q h1
  have hltv_pos : (0 : ℚ) < lltv_q := lltv_q_pos
  have h3 :
      (w.state.collateral b : ℚ) * w.oracle.read_q
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) * lltv_q
      < (w.state.debtShares.balances b : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
        * liquidationIncentiveFactor_q * lltv_q :=
    mul_lt_mul_of_pos_right hBDP hltv_pos
  have hbonus_lltv : liquidationIncentiveFactor_q * lltv_q < 1 :=
    liquidationIncentiveFactor_q_lltv_q_lt_one
  have hYR_nn :
      (0 : ℚ) ≤ (w.state.debtShares.balances b : ℚ) *
                  ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets) := by
    have hY : (0 : ℚ) ≤ (w.state.debtShares.balances b : ℚ) := by
      exact_mod_cast Nat.zero_le _
    have hR : (0 : ℚ) ≤ (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets := by
      have hvBA : (0 : ℚ) ≤ (virtualBorrowAssets : ℚ) := by
        exact_mod_cast Nat.zero_le _
      have hTBA : (0 : ℚ) ≤ (w.state.totalBorrowAssets : ℚ) := by
        exact_mod_cast Nat.zero_le _
      linarith
    exact mul_nonneg hY hR
  have h4 :
      (w.state.debtShares.balances b : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
        * liquidationIncentiveFactor_q * lltv_q
      ≤ (w.state.debtShares.balances b : ℚ)
        * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets) := by
    nlinarith [hbonus_lltv, hYR_nn]
  have hring :
      (w.state.collateral b : ℚ) * w.oracle.read_q * lltv_q *
        ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
      = (w.state.collateral b : ℚ) * w.oracle.read_q
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) * lltv_q := by
    ring
  linarith [h3, h4, h2, hring]

/-- In `BadDebtPath`, `liquidate` cannot succeed with full debt burn
(`sh = dsh b`).  Full burn requires `coll · p ≥ debtOf b · bonus`
(from the seized-≤-coll guard combined with `seized · p ≥ cost · bonus`
and `cost = debtOf b`), which directly contradicts `BadDebtPath`. -/
theorem liquidate_full_burn_fails_in_bad_debt_path
    {w : World} {lq b : Addr}
    (hp : (0 : OraclePrice) < w.oracle.read)
    (hBDP : BadDebtPath w b) :
    liquidate w lq b (w.state.debtShares.balances b) = none := by
  rw [BadDebtPath_iff_shareMul] at hBDP
  by_contra hne
  match hl_match : liquidate w lq b (w.state.debtShares.balances b) with
  | none => exact hne hl_match
  | some ⟨w', seized⟩ =>
    obtain ⟨_, _, hSeized, _, _, hSeizedLe, _, _⟩ := liquidate_extract hl_match
    have hcost_eq : repayCost w.state (w.state.debtShares.balances b) =
        debtOf w.state b := rfl
    set p : ℚ := w.oracle.read_q
    set cost : ℕ := repayCost w.state (w.state.debtShares.balances b)
    set bonus : ℚ := liquidationIncentiveFactor_q
    have hbonus_ge : (1 : ℚ) ≤ bonus := liquidationIncentiveFactor_q_ge_one
    have hp_q : (0 : ℚ) < p := by
      show (0 : ℚ) < ((w.oracle.read.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ 36
      apply div_pos
      · exact_mod_cast hp
      · positivity
    have hp_nn : (0 : ℚ) ≤ p := le_of_lt hp_q
    have hcost_nn : (0 : ℚ) ≤ (cost : ℚ) := by exact_mod_cast Nat.zero_le _
    have hbonus_nn : (0 : ℚ) ≤ bonus := le_trans zero_le_one hbonus_ge
    -- Lower bound from the new Fixed-form `seizedFor`.
    have hseized_p_ge : (cost : ℚ) * bonus ≤ (seized : ℚ) * p := by
      have h := cost_bonus_le_seizedFor_mul_price (s := w.state)
                  (p := w.oracle.read)
                  (repaidShares := w.state.debtShares.balances b) hp
      rw [hSeized]
      exact h
    have hSeizedLe_q : ((seized : ℕ) : ℚ) ≤ ((w.state.collateral b : ℕ) : ℚ) := by
      exact_mod_cast hSeizedLe
    have hcoll_p_ge : (w.state.collateral b : ℚ) * p ≥ (cost : ℚ) * bonus := by
      have h1 : ((seized : ℕ) : ℚ) * p ≤ ((w.state.collateral b : ℕ) : ℚ) * p :=
        mul_le_mul_of_nonneg_right hSeizedLe_q hp_nn
      linarith
    set Y : ℕ := w.state.debtShares.balances b
    set R : ℕ := w.state.totalBorrowAssets + virtualBorrowAssets
    set S : ℕ := w.state.debtShares.totalSupply + virtualBorrowShares
    have hS_pos : 0 < S := by
      show 0 < w.state.debtShares.totalSupply + virtualBorrowShares
      have := virtualBorrowShares_pos; omega
    have hSq_pos : (0 : ℚ) < (S : ℚ) := by exact_mod_cast hS_pos
    have hSq_nn : (0 : ℚ) ≤ (S : ℚ) := le_of_lt hSq_pos
    have hCD : Y * R ≤ debtOf w.state b * S := by
      show w.state.debtShares.balances b *
              (w.state.totalBorrowAssets + virtualBorrowAssets)
            ≤ debtOf w.state b *
              (w.state.debtShares.totalSupply + virtualBorrowShares)
      unfold debtOf repayCost; exact ceilDiv_mul_ge _ hS_pos
    have hCD_q : (Y : ℚ) * (R : ℚ) ≤ (debtOf w.state b : ℚ) * (S : ℚ) := by
      exact_mod_cast hCD
    have hbonus_nn : (0 : ℚ) ≤ bonus := le_trans zero_le_one hbonus_ge
    have hCD_q_bonus : (Y : ℚ) * (R : ℚ) * bonus ≤ (debtOf w.state b : ℚ) * (S : ℚ) * bonus :=
      mul_le_mul_of_nonneg_right hCD_q hbonus_nn
    have hcoll_p_S : (w.state.collateral b : ℚ) * p * (S : ℚ)
                  ≥ (cost : ℚ) * bonus * (S : ℚ) :=
      mul_le_mul_of_nonneg_right hcoll_p_ge hSq_nn
    have hcost_eq_q : (cost : ℚ) = (debtOf w.state b : ℚ) := by rw [hcost_eq]
    rw [hcost_eq_q] at hcoll_p_S
    have hBDP_q : (w.state.collateral b : ℚ) * p
                    * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
                  < (w.state.debtShares.balances b : ℚ)
                    * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
                    * liquidationIncentiveFactor_q := hBDP
    have hRq : ((R : ℕ) : ℚ) =
        (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets := by
      show ((w.state.totalBorrowAssets + virtualBorrowAssets : ℕ) : ℚ) =
          (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets
      push_cast; ring
    have hSq : ((S : ℕ) : ℚ) =
        (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
      show ((w.state.debtShares.totalSupply + virtualBorrowShares : ℕ) : ℚ) =
          (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares
      push_cast; rfl
    rw [← hRq, ← hSq] at hBDP_q
    have hring1 : (debtOf w.state b : ℚ) * (S : ℚ) * bonus
                = (debtOf w.state b : ℚ) * bonus * (S : ℚ) := by ring
    rw [hring1] at hCD_q_bonus
    linarith

/-- `liquidate` in `BadDebtPath` leaves the borrower with positive
debt-share balance.  Direct corollary of full-burn impossibility plus
the burn lower bound from ERC-20 semantics. -/
theorem liquidate_bad_debt_path_dsh_pos
    {w w' : World} {lq b : Addr} {sh seized : ℕ}
    (hp : (0 : OraclePrice) < w.oracle.read)
    (hBDP : BadDebtPath w b)
    (hl : liquidate w lq b sh = some (w', seized)) :
    0 < w'.state.debtShares.balances b := by
  have hsh_le : sh ≤ w.state.debtShares.balances b :=
    liquidate_repaidShares_le_borrower_balance hl
  by_cases hsh_eq : sh = w.state.debtShares.balances b
  · subst hsh_eq
    rw [liquidate_full_burn_fails_in_bad_debt_path hp hBDP] at hl
    simp at hl
  · have hsh_lt : sh < w.state.debtShares.balances b := by omega
    have hYpost : w'.state.debtShares.balances b
                  = w.state.debtShares.balances b - sh :=
      liquidate_burns_repaidShares hl
    rw [hYpost]; omega

/-- T3: `liquidate` preserves `BadDebtPath`.

Two ingredients: (1) `cost ≤ TBA` (no ℕ truncation in the post-state's
`R'`), derived from `BadDebtPath` plus the seized-≤-collateral guard;
(2) a polynomial identity over `ℚ` whose right-hand side is non-
negative, giving `S · m(w') ≥ (S − sh) · m(w) > 0`, hence `m(w') > 0`. -/
theorem liquidate_preserves_bad_debt_path
    {w w' : World} {lq b : Addr} {sh seized : ℕ}
    (hp : (0 : OraclePrice) < w.oracle.read)
    (hbk : Bookkeep w)
    (hBDP : BadDebtPath w b)
    (hl : liquidate w lq b sh = some (w', seized)) :
    BadDebtPath w' b := by
  rw [BadDebtPath_iff_shareMul] at hBDP
  rw [BadDebtPath_iff_shareMul]
  obtain ⟨hTBA, hShTotal, hSeized, hColB, _, hSeizedLe, _, hor⟩ := liquidate_extract hl
  have hsh_le_Y : sh ≤ w.state.debtShares.balances b :=
    liquidate_repaidShares_le_borrower_balance hl
  have hYpost : w'.state.debtShares.balances b
                = w.state.debtShares.balances b - sh :=
    liquidate_burns_repaidShares hl
  have hY_le_dshTotal := balance_le_totalSupply hbk.debtShareInv b
  have hvBS_pos : 0 < virtualBorrowShares := virtualBorrowShares_pos
  have hvBA_pos : 0 < virtualBorrowAssets := virtualBorrowAssets_pos
  have hsh_le_dshTotal : sh ≤ w.state.debtShares.totalSupply := by omega
  have hY_lt_S :
      w.state.debtShares.balances b
      < w.state.debtShares.totalSupply + virtualBorrowShares := by omega
  have hH2 : sh * (w.state.totalBorrowAssets + virtualBorrowAssets)
           ≤ repayCost w.state sh
             * (w.state.debtShares.totalSupply + virtualBorrowShares) := by
    unfold repayCost; apply ceilDiv_mul_ge; omega
  have hH2_q :
      (sh : ℚ) * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
      ≤ (repayCost w.state sh : ℚ)
        * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
    have hcast :
        ((sh * (w.state.totalBorrowAssets + virtualBorrowAssets) : ℕ) : ℚ)
        ≤ ((repayCost w.state sh
            * (w.state.debtShares.totalSupply + virtualBorrowShares) : ℕ) : ℚ) := by
      exact_mod_cast hH2
    push_cast at hcast; linarith
  have hbonus_ge : (1 : ℚ) ≤ liquidationIncentiveFactor_q :=
    liquidationIncentiveFactor_q_ge_one
  have hbonus_pos : (0 : ℚ) < liquidationIncentiveFactor_q :=
    lt_of_lt_of_le zero_lt_one hbonus_ge
  have hbonus_nn : (0 : ℚ) ≤ liquidationIncentiveFactor_q := le_of_lt hbonus_pos
  have hp_q : (0 : ℚ) < w.oracle.read_q := by
    show (0 : ℚ) < ((w.oracle.read.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ 36
    apply div_pos
    · exact_mod_cast hp
    · positivity
  have hp_nn : (0 : ℚ) ≤ w.oracle.read_q := le_of_lt hp_q
  -- The bound `cost · bonus ≤ seized · p` comes directly from the new
  -- Fixed-form `seizedFor`'s ceil rounding.
  have hH3_q :
      (repayCost w.state sh : ℚ) * liquidationIncentiveFactor_q
      ≤ (seized : ℚ) * w.oracle.read_q := by
    rw [hSeized]
    exact cost_bonus_le_seizedFor_mul_price hp
  have hSeized_le_C_q :
      ((seized : ℕ) : ℚ) ≤ ((w.state.collateral b : ℕ) : ℚ) := by
    exact_mod_cast hSeizedLe
  have hS_q_pos :
      (0 : ℚ) < (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    have h1 : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
      exact_mod_cast Nat.zero_le _
    have h2 : (0 : ℚ) < (virtualBorrowShares : ℚ) := by exact_mod_cast hvBS_pos
    linarith
  have hR_q_pos :
      (0 : ℚ) < (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets := by
    have h1 : (0 : ℚ) ≤ (w.state.totalBorrowAssets : ℚ) := by
      exact_mod_cast Nat.zero_le _
    have h2 : (0 : ℚ) < (virtualBorrowAssets : ℚ) := by exact_mod_cast hvBA_pos
    linarith
  have hY_lt_S_q :
      (w.state.debtShares.balances b : ℚ)
      < (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    have hcast :
        ((w.state.debtShares.balances b : ℕ) : ℚ)
        < ((w.state.debtShares.totalSupply + virtualBorrowShares : ℕ) : ℚ) := by
      exact_mod_cast hY_lt_S
    push_cast at hcast; linarith
  have hsh_le_Y_q : (sh : ℚ) ≤ (w.state.debtShares.balances b : ℚ) := by
    exact_mod_cast hsh_le_Y
  have hsh_le_dshTotal_q :
      (sh : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
    exact_mod_cast hsh_le_dshTotal
  have hcost_le_TBA : repayCost w.state sh ≤ w.state.totalBorrowAssets := by
    by_contra hcontra
    push Not at hcontra
    have hcost_ge_R :
        w.state.totalBorrowAssets + virtualBorrowAssets ≤ repayCost w.state sh := by
      rw [virtualBorrowAssets_eq_one]; omega
    have hcost_ge_R_q :
        ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
        ≤ (repayCost w.state sh : ℚ) := by
      have hcast :
          ((w.state.totalBorrowAssets + virtualBorrowAssets : ℕ) : ℚ)
          ≤ ((repayCost w.state sh : ℕ) : ℚ) := by exact_mod_cast hcost_ge_R
      push_cast at hcast; linarith
    have hSeized_pq_le :
        (seized : ℚ) * w.oracle.read_q
        ≤ (w.state.collateral b : ℚ) * w.oracle.read_q :=
      mul_le_mul_of_nonneg_right hSeized_le_C_q hp_nn
    have hcost_bonus_le_Cp :
        (repayCost w.state sh : ℚ) * liquidationIncentiveFactor_q
        ≤ (w.state.collateral b : ℚ) * w.oracle.read_q :=
      le_trans hH3_q hSeized_pq_le
    have hcost_bonus_S_le :
        (repayCost w.state sh : ℚ) * liquidationIncentiveFactor_q
          * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
        ≤ (w.state.collateral b : ℚ) * w.oracle.read_q
          * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) :=
      mul_le_mul_of_nonneg_right hcost_bonus_le_Cp (le_of_lt hS_q_pos)
    have hBDP_q :
        (w.state.collateral b : ℚ) * w.oracle.read_q
          * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
        < (w.state.debtShares.balances b : ℚ)
          * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
          * liquidationIncentiveFactor_q := hBDP
    have hcost_S_bonus_lt :
        (repayCost w.state sh : ℚ) * liquidationIncentiveFactor_q
          * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
        < (w.state.debtShares.balances b : ℚ)
          * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
          * liquidationIncentiveFactor_q :=
      lt_of_le_of_lt hcost_bonus_S_le hBDP_q
    have hcost_S_lt_YR :
        (repayCost w.state sh : ℚ)
          * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
        < (w.state.debtShares.balances b : ℚ)
          * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets) := by
      have heq : (repayCost w.state sh : ℚ) * liquidationIncentiveFactor_q
                  * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
                = (repayCost w.state sh : ℚ)
                  * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
                  * liquidationIncentiveFactor_q := by ring
      rw [heq] at hcost_S_bonus_lt
      exact lt_of_mul_lt_mul_right hcost_S_bonus_lt hbonus_nn
    have hRS_le_costS :
        ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
          * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
        ≤ (repayCost w.state sh : ℚ)
          * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) :=
      mul_le_mul_of_nonneg_right hcost_ge_R_q (le_of_lt hS_q_pos)
    have hRS_lt_YR :
        ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
          * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
        < (w.state.debtShares.balances b : ℚ)
          * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets) :=
      lt_of_le_of_lt hRS_le_costS hcost_S_lt_YR
    have heq2 :
        (w.state.debtShares.balances b : ℚ)
          * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
        = ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
          * (w.state.debtShares.balances b : ℚ) := by ring
    rw [heq2] at hRS_lt_YR
    have hS_lt_Y :
        ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares)
        < (w.state.debtShares.balances b : ℚ) :=
      lt_of_mul_lt_mul_left hRS_lt_YR (le_of_lt hR_q_pos)
    linarith
  rw [hor, hColB, hShTotal, hTBA, hYpost, hSeized]
  have hcast_C :
      ((w.state.collateral b - seizedFor w.state w.oracle.read sh : ℕ) : ℚ)
      = (w.state.collateral b : ℚ) - (seizedFor w.state w.oracle.read sh : ℚ) := by
    apply Nat.cast_sub
    rw [← hSeized]; exact hSeizedLe
  have hcast_S' :
      ((w.state.debtShares.totalSupply - sh : ℕ) : ℚ)
      = (w.state.debtShares.totalSupply : ℚ) - (sh : ℚ) :=
    Nat.cast_sub hsh_le_dshTotal
  have hcast_TBA' :
      ((w.state.totalBorrowAssets - repayCost w.state sh : ℕ) : ℚ)
      = (w.state.totalBorrowAssets : ℚ) - (repayCost w.state sh : ℚ) :=
    Nat.cast_sub hcost_le_TBA
  have hcast_Y' :
      ((w.state.debtShares.balances b - sh : ℕ) : ℚ)
      = (w.state.debtShares.balances b : ℚ) - (sh : ℚ) :=
    Nat.cast_sub hsh_le_Y
  rw [hcast_C, hcast_S', hcast_TBA', hcast_Y']
  set Y_q : ℚ := (w.state.debtShares.balances b : ℚ) with hY_q_def
  set R_q : ℚ := (w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets with hR_q_def
  set S_q : ℚ := (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares with hS_q_def
  set C_q : ℚ := (w.state.collateral b : ℚ) with hC_q_def
  set p_q : ℚ := w.oracle.read_q with hp_q_def
  set bonus_q : ℚ := liquidationIncentiveFactor_q with hbonus_q_def
  set cost_q : ℚ := (repayCost w.state sh : ℚ) with hcost_q_def
  set seized_q : ℚ := (seizedFor w.state w.oracle.read sh : ℚ) with hseized_q_def
  set sh_q : ℚ := (sh : ℚ) with hsh_q_def
  have hSshvBS :
      ((w.state.debtShares.totalSupply : ℚ) - sh_q + virtualBorrowShares) = S_q - sh_q := by
    show (w.state.debtShares.totalSupply : ℚ) - sh_q + virtualBorrowShares
        = ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) - sh_q
    ring
  have hRcost :
      ((w.state.totalBorrowAssets : ℚ) - cost_q + virtualBorrowAssets) = R_q - cost_q := by
    show (w.state.totalBorrowAssets : ℚ) - cost_q + virtualBorrowAssets
        = ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets) - cost_q
    ring
  rw [hSshvBS, hRcost]
  have hSpsh_pos : (0 : ℚ) < S_q - sh_q := by
    have hsh_lt_S_q : sh_q < S_q := by
      have h1 : sh_q ≤ (w.state.debtShares.totalSupply : ℚ) := hsh_le_dshTotal_q
      have h2 : (0 : ℚ) < (virtualBorrowShares : ℚ) := by exact_mod_cast hvBS_pos
      show sh_q < (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares
      linarith
    linarith
  have hSY_nn : (0 : ℚ) ≤ S_q - Y_q := by
    have h := hY_lt_S_q
    show (0 : ℚ) ≤ ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) - Y_q
    linarith
  have hH2_q' : sh_q * R_q ≤ cost_q * S_q := hH2_q
  have hH3_q' : cost_q * bonus_q ≤ seized_q * p_q := by
    have h := hH3_q
    rw [hSeized] at h
    exact h
  have hBDP_q' : C_q * p_q * S_q < Y_q * R_q * bonus_q := hBDP
  have hIdentity :
      S_q * ((Y_q - sh_q) * (R_q - cost_q) * bonus_q
              - (C_q - seized_q) * p_q * (S_q - sh_q))
      - (S_q - sh_q) * (Y_q * R_q * bonus_q - C_q * p_q * S_q)
      = S_q * (S_q - sh_q) * (seized_q * p_q - cost_q * bonus_q)
        + (S_q - Y_q) * bonus_q * (cost_q * S_q - sh_q * R_q) := by ring
  have hT1_nn : (0 : ℚ) ≤ S_q * (S_q - sh_q) * (seized_q * p_q - cost_q * bonus_q) := by
    apply mul_nonneg
    · exact mul_nonneg (le_of_lt hS_q_pos) (le_of_lt hSpsh_pos)
    · linarith [hH3_q']
  have hT2_nn : (0 : ℚ) ≤ (S_q - Y_q) * bonus_q * (cost_q * S_q - sh_q * R_q) := by
    apply mul_nonneg
    · exact mul_nonneg hSY_nn hbonus_nn
    · linarith [hH2_q']
  have hm_pos : (0 : ℚ) < Y_q * R_q * bonus_q - C_q * p_q * S_q := by linarith
  have hSm_pos :
      (0 : ℚ) < (S_q - sh_q) * (Y_q * R_q * bonus_q - C_q * p_q * S_q) :=
    mul_pos hSpsh_pos hm_pos
  have hSmN_pos :
      (0 : ℚ) < S_q * ((Y_q - sh_q) * (R_q - cost_q) * bonus_q
                        - (C_q - seized_q) * p_q * (S_q - sh_q)) := by
    have hD_nn :
        (0 : ℚ) ≤ S_q * ((Y_q - sh_q) * (R_q - cost_q) * bonus_q
                          - (C_q - seized_q) * p_q * (S_q - sh_q))
                  - (S_q - sh_q) * (Y_q * R_q * bonus_q - C_q * p_q * S_q) := by
      rw [hIdentity]; linarith
    linarith
  have hmN_pos :
      (0 : ℚ) < (Y_q - sh_q) * (R_q - cost_q) * bonus_q
                - (C_q - seized_q) * p_q * (S_q - sh_q) := by
    by_contra hX_nonpos
    push Not at hX_nonpos
    have hbad :
        S_q * ((Y_q - sh_q) * (R_q - cost_q) * bonus_q
                - (C_q - seized_q) * p_q * (S_q - sh_q)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (le_of_lt hS_q_pos) hX_nonpos
    linarith
  linarith

/-! ## Healing existence

Closed-form `HealableLiquidationBudget` (in `Defs.Predicates`) is tight enough to make
a full-burn liquidation feasible and to leave the borrower `Healthy`. -/

/-- Full liquidation burns the borrower's whole debt-share balance. -/
noncomputable def fullLiquidationShares (w : World) (b : Addr) : ℕ :=
  w.state.debtShares.balances b

/-- Loan-asset amount needed to fully repay a borrower. -/
noncomputable def fullLiquidationCost (w : World) (b : Addr) : ℕ :=
  repayCost w.state (fullLiquidationShares w b)

/-- Collateral seized by a full liquidation at the current oracle read. -/
noncomputable def fullLiquidationSeized (w : World) (b : Addr) : ℕ :=
  seizedFor w.state w.oracle.read (fullLiquidationShares w b)

/-- The liquidator can pay the full liquidation cost. -/
def LiquidatorHasFullRepayFunds (w : World) (lq b : Addr) : Prop :=
  fullLiquidationCost w b ≤ w.state.loanAsset.balances lq

/-- `HealableLiquidationBudget` strengthens the share-multiplied `Healable`
region predicate. -/
private lemma healable_of_healableLiquidationBudget
    {w : World} {b : Addr}
    (hp : 0 ≤ w.oracle.read_q)
    (hBudget : HealableLiquidationBudget w b) :
    Healable w b := by
  rw [Healable_iff_shareMul]
  set Y : ℕ := w.state.debtShares.balances b
  set R : ℕ := w.state.totalBorrowAssets + virtualBorrowAssets
  set S : ℕ := w.state.debtShares.totalSupply + virtualBorrowShares
  set D : ℕ := debtOf w.state b
  set C : ℕ := w.state.collateral b
  set p : ℚ := w.oracle.read_q
  set bonus : ℚ := liquidationIncentiveFactor_q
  have hS_pos : 0 < S := by
    dsimp [S]
    have := virtualBorrowShares_pos
    omega
  have hYR_le_DS_nat : Y * R ≤ D * S := by
    dsimp [Y, R, S, D]
    unfold debtOf repayCost
    exact ceilDiv_mul_ge _ hS_pos
  have hYR_le_DS : (Y : ℚ) * (R : ℚ) ≤ (D : ℚ) * (S : ℚ) := by
    exact_mod_cast hYR_le_DS_nat
  have hbonus_ge : (1 : ℚ) ≤ bonus := by
    simpa [bonus] using liquidationIncentiveFactor_q_ge_one
  have hbonus_nn : (0 : ℚ) ≤ bonus := le_trans zero_le_one hbonus_ge
  have hp' : 0 ≤ p := by simpa [p] using hp
  have hBudget' :
      bonus + p ≤ (C : ℚ) * p - (D : ℚ) * bonus := by
    simpa [HealableLiquidationBudget, Y, R, S, D, C, p, bonus] using hBudget
  have hDbonus_le_Cp : (D : ℚ) * bonus ≤ (C : ℚ) * p := by
    nlinarith [hBudget', hbonus_ge, hp']
  have hS_nn : (0 : ℚ) ≤ (S : ℚ) := by
    exact_mod_cast Nat.zero_le S
  have hLeft :
      (Y : ℚ) * (R : ℚ) * bonus ≤ (D : ℚ) * (S : ℚ) * bonus := by
    exact mul_le_mul_of_nonneg_right hYR_le_DS hbonus_nn
  have hRight :
      (D : ℚ) * bonus * (S : ℚ) ≤ (C : ℚ) * p * (S : ℚ) := by
    exact mul_le_mul_of_nonneg_right hDbonus_le_Cp hS_nn
  have h :
      (Y : ℚ) * (R : ℚ) * bonus ≤ (C : ℚ) * p * (S : ℚ) := by
    nlinarith
  simpa [Y, R, S, C, p, bonus] using h

/-- `HealableLiquidationBudget` leaves enough value slack for the full-liquidation
seized-collateral guard. -/
private lemma fullLiquidationSeized_le_collateral_of_healableLiquidationBudget
    {w : World} {b : Addr}
    (hp : (0 : OraclePrice) < w.oracle.read)
    (hBudget : HealableLiquidationBudget w b) :
    fullLiquidationSeized w b ≤ w.state.collateral b := by
  unfold fullLiquidationSeized fullLiquidationShares
  set p : ℚ := w.oracle.read_q
  set C : ℕ := w.state.collateral b
  set D : ℕ := debtOf w.state b
  set bonus : ℚ := liquidationIncentiveFactor_q
  have hp_q : 0 < p := by
    show (0 : ℚ) < ((w.oracle.read.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ 36
    apply div_pos
    · exact_mod_cast hp
    · positivity
  have hbonus_ge : (1 : ℚ) ≤ bonus := liquidationIncentiveFactor_q_ge_one
  have hBudget' :
      bonus + p ≤ (C : ℚ) * p - (D : ℚ) * bonus := hBudget
  have hDbonus_le_Cp : (D : ℚ) * bonus ≤ (C : ℚ) * p := by
    nlinarith [hBudget', hbonus_ge, hp_q]
  -- The new `seizedFor` upper bound: `seized · p ≤ cost · bonus + p`.
  have h_upper :=
    seizedFor_mul_price_le_cost_bonus_add_price (s := w.state)
      (p := w.oracle.read) (repaidShares := w.state.debtShares.balances b) hp
  -- With `cost = debtOf b` (full burn), this gives `seized · p ≤ D · bonus + p`.
  have hcost_eq : repayCost w.state (w.state.debtShares.balances b) = D := rfl
  rw [hcost_eq] at h_upper
  -- And `D · bonus + p ≤ C · p` from the budget plus `p ≤ p`.
  have h_chain :
      (seizedFor w.state w.oracle.read
          (w.state.debtShares.balances b) : ℚ) * p ≤ (C : ℚ) * p := by
    linarith [h_upper, hBudget']
  -- Cancel `p > 0` to get the desired Nat inequality.
  have h_q :
      ((seizedFor w.state w.oracle.read
          (w.state.debtShares.balances b) : ℕ) : ℚ) ≤ (C : ℕ) := by
    exact le_of_mul_le_mul_right h_chain hp_q
  exact_mod_cast h_q

/-- Under `HealableLiquidationBudget`, a liquidator that can pay the
full debt can execute a full-burn liquidation that restores `Healthy`.

The market wallet's collateral availability is discharged by the
`collateralBacked` conjunct of `MarketAccounting w`, since
`seized ≤ collateral b ≤ Σ collateral ≤ collateralAsset.balances marketAddress`. -/
theorem exists_full_liquidation_to_healthy
    {w : World} {lq b : Addr}
    (hp : (0 : OraclePrice) < w.oracle.read)
    (hUnhealthy : ¬ Healthy w b)
    (hBudget : HealableLiquidationBudget w b)
    (hLiquidatorFunds : LiquidatorHasFullRepayFunds w lq b)
    (hAccounting : MarketAccounting w) :
    ∃ sh w' seized,
      liquidate w lq b sh = some (w', seized) ∧ Healthy w' b := by
  let sh := fullLiquidationShares w b
  have hSeizedLe :
      seizedFor w.state w.oracle.read sh ≤ w.state.collateral b := by
    simpa [sh] using
      fullLiquidationSeized_le_collateral_of_healableLiquidationBudget
        (w := w) (b := b) hp hBudget
  have hLoan :
      repayCost w.state sh ≤ w.state.loanAsset.balances lq := by
    simpa [LiquidatorHasFullRepayFunds, fullLiquidationCost, sh] using
      hLiquidatorFunds
  -- Single-element bound: collat b ≤ Σ collat (Finsupp.sum_update_add at b 0).
  have hCollatLeSum :
      w.state.collateral b ≤ w.state.collateral.sum (fun _ x => x) := by
    have he := Finsupp.sum_update_add w.state.collateral b 0 (fun _ x => x)
      (fun _ => rfl) (fun _ _ _ => rfl)
    dsimp only at he
    omega
  have hSumLeBalance :
      w.state.collateral.sum (fun _ x => x)
        ≤ w.state.collateralAsset.balances marketAddress := by
    have := hAccounting.collateralBacked
    unfold CollateralBacked at this
    exact this
  have hMarket :
      seizedFor w.state w.oracle.read sh
        ≤ w.state.collateralAsset.balances marketAddress :=
    le_trans hSeizedLe (le_trans hCollatLeSum hSumLeBalance)
  have hLoanTransfer :
      ∃ loan',
        ERC20.transferFrom w.state.loanAsset lq marketAddress
          (repayCost w.state sh) = some loan' := by
    unfold ERC20.transferFrom
    rw [if_neg (not_lt_of_ge hLoan)]
    exact ⟨_, rfl⟩
  have hDebtBurn :
      ∃ debt',
        ERC20.burn w.state.debtShares b sh = some debt' := by
    unfold ERC20.burn
    have hnot : ¬ w.state.debtShares.balances b < sh := by
      simp [sh, fullLiquidationShares]
    rw [if_neg hnot]
    exact ⟨_, rfl⟩
  have hCollateralTransfer :
      ∃ col',
        ERC20.transferFrom w.state.collateralAsset marketAddress lq
          (seizedFor w.state w.oracle.read sh) = some col' := by
    unfold ERC20.transferFrom
    rw [if_neg (not_lt_of_ge hMarket)]
    exact ⟨_, rfl⟩
  obtain ⟨w', seized, hLiq⟩ :
      ∃ w' seized, liquidate w lq b sh = some (w', seized) := by
    unfold liquidate
    -- `hUnhealthy : ¬ Healthy w b` unfolds to `¬ HealthyOnState w.state w.oracle.read b`.
    change ¬ HealthyOnState w.state w.oracle.read b at hUnhealthy
    rw [if_neg hUnhealthy]
    rw [if_neg (not_lt_of_ge hSeizedLe)]
    obtain ⟨loan', hLoan'⟩ := hLoanTransfer
    rw [hLoan']
    obtain ⟨debt', hDebt'⟩ := hDebtBurn
    rw [hDebt']
    obtain ⟨col', hCol'⟩ := hCollateralTransfer
    rw [hCol']
    exact ⟨_, _, rfl⟩
  refine ⟨sh, w', seized, hLiq, ?_⟩
  have hBalZero : w'.state.debtShares.balances b = 0 := by
    have hBurn := liquidate_burns_repaidShares hLiq
    rw [hBurn]
    dsimp [sh, fullLiquidationShares]
    omega
  exact healthy_of_debtShares_balance_zero hBalZero

end Market
