import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas

/-!
# Lending Market — Tier-2 round-trips and Tier-3 health

The user-facing safety properties:

* **Round-trip (Tier 2)**: `supply` then `withdraw` returns at most
  what was deposited; `borrow` then `repay` returns at least what was
  withdrawn.  Both follow from the rounding direction of the
  conversion formulas (floor on the supply-shares-out side, ceiling
  on the debt-shares-out side).
* **Health (Tier 3)**: `borrow` and `withdrawCollateral` produce a
  world that is `Healthy` at the actor, observed at the oracle's
  current read.  Both follow directly from the operation's own guard.

## Main theorems
- `supply_withdraw_round_trip`
- `borrow_repay_round_trip`
- `borrow_healthy`
- `withdrawCollateral_healthy`

The `private` helpers (`assetFor_le`, `repayCost_ge`) are pure
arithmetic about `Nat.div_mul_le_self` / `ceilDiv_mul_ge`, used only
inside the round-trip proofs of this file — skip on first read.
-/

namespace Market

open Util (ceilDiv ceilDiv_mul_ge le_ceilDiv)

/-! ## Helper lemmas (private — skip on first read) -/

private lemma assetFor_le (A S d k : ℕ)
    (hkA : k * A ≤ d * S) (hSk : 0 < S + k) :
    k * (A + d) / (S + k) ≤ d := by
  have key : k * (A + d) ≤ d * (S + k) := by
    have e1 : k * (A + d) = k * A + d * k := by
      rw [Nat.mul_add, Nat.mul_comm k d]
    have e2 : d * (S + k) = d * S + d * k := Nat.mul_add d S k
    omega
  have h1 : k * (A + d) / (S + k) ≤ d * (S + k) / (S + k) :=
    Nat.div_le_div_right key
  have h2 : d * (S + k) / (S + k) = d := Nat.mul_div_cancel d hSk
  omega

private lemma repayCost_ge (A S d k : ℕ)
    (hkA : d * S ≤ k * A) (hSk : 0 < S + k) :
    d ≤ ceilDiv (k * (A + d)) (S + k) := by
  apply le_ceilDiv hSk
  have e1 : d * (S + k) = d * S + d * k := Nat.mul_add d S k
  have e2 : k * (A + d) = k * A + d * k := by
    rw [Nat.mul_add, Nat.mul_comm k d]
  omega

/-! ## Main theorems -/

theorem supply_withdraw_round_trip {w w1 w2 : World} {user : Addr} {d k a : ℕ}
    (hsup : supply w user d = some (w1, k))
    (hw : withdraw w1 user k = some (w2, a)) :
    a ≤ d := by
  obtain ⟨htA, htS, hk, _⟩ := supply_extract hsup
  obtain ⟨_, _, ha, _⟩ := withdraw_extract hw
  rw [ha]; unfold supplyAssetFor
  rw [htS, htA]
  have eq1 : w.state.totalSupplyAssets + d + virtualSupplyAssets =
             (w.state.totalSupplyAssets + virtualSupplyAssets) + d := by omega
  have eq2 : w.state.supplyShares.totalSupply + k + virtualSupplyShares =
             (w.state.supplyShares.totalSupply + virtualSupplyShares) + k := by omega
  rw [eq1, eq2]
  apply assetFor_le
  · rw [hk]; exact supplyShareFor_bound w.state d
  · have := virtualSupplyShares_pos; omega

theorem borrow_repay_round_trip
    {w w1 w2 : World} {user : Addr} {d k a : ℕ}
    (hb : borrow w user d = some (w1, k))
    (hr : repay w1 user k = some (w2, a)) :
    d ≤ a := by
  obtain ⟨htA, htS, hk, _, _⟩ := borrow_extract hb
  obtain ⟨_, _, ha, _⟩ := repay_extract hr
  rw [ha]; unfold repayCost
  rw [htS, htA]
  have eq1 : w.state.totalBorrowAssets + d + virtualBorrowAssets =
             (w.state.totalBorrowAssets + virtualBorrowAssets) + d := by omega
  have eq2 : w.state.debtShares.totalSupply + k + virtualBorrowShares =
             (w.state.debtShares.totalSupply + virtualBorrowShares) + k := by omega
  rw [eq1, eq2]
  apply repayCost_ge
  · rw [hk]; exact borrowShareFor_bound w.state d
  · have := virtualBorrowShares_pos; omega

theorem borrow_healthy
    {w w' : World} {user : Addr} {assets shares : ℕ}
    (hb : borrow w user assets = some (w', shares)) :
    Healthy w' user :=
  (borrow_extract hb).2.2.2.1

theorem withdrawCollateral_healthy
    {w w' : World} {user : Addr} {c : ℕ}
    (hw : withdrawCollateral w user c = some w') :
    Healthy w' user := by
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
        exact hHealth
      · simp at hw

end Market
