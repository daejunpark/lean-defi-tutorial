import Defs.Semantics

/-!
# Lending Market — Invariant predicates

State-level invariant predicates on `World`, each carrying its own
soundness story:

- `Bookkeep` — ERC-20 ledger invariants on the four sub-ledgers.
- `MarketAccounting` — loan- and collateral-asset accounting, plus
  the auxiliary fact `state.collateral marketAddress = 0`.
- `AllHealthy` — ∀-lift of the per-user `Healthy`.
- `AssetCovered` — last-line-of-defence ℚ-form coverage of `debtOf_q`
  by collateral value; the `*_iff_shareMul` bridges restate it
  division-free.
- `SupplySharePriceLE` — supply-share price monotonicity (between
  two worlds).

Preservation theorems for each invariant live in their dedicated
sibling files (`Bookkeep.lean`, `Accounting.lean`, `AllHealthy.lean`,
`AssetCovered.lean`, `SharePrice.lean`).
-/

namespace Market

structure Bookkeep (w : World) : Prop where
  loanAssetInv   : ERC20.Invariant w.state.loanAsset
  collatAssetInv : ERC20.Invariant w.state.collateralAsset
  supplyShareInv : ERC20.Invariant w.state.supplyShares
  debtShareInv   : ERC20.Invariant w.state.debtShares

/-- Loan-asset accounting: outstanding borrow assets do not exceed
supply assets.  A totals-arithmetic fact, not solvency in the
cash-flow sense. -/
def BorrowBacked (w : World) : Prop :=
  w.state.totalBorrowAssets ≤ w.state.totalSupplyAssets

/-- Collateral-asset accounting: the protocol's recorded per-user
collateral balances do not exceed the ERC-20 collateral balance held
at `marketAddress`.  Stated as a `Finsupp.sum` so the bound is over
*all* users, not pointwise. -/
def CollateralBacked (w : World) : Prop :=
  w.state.collateral.sum (fun _ c => c)
    ≤ w.state.collateralAsset.balances marketAddress

/-- Market-accounting bundle: loan-asset and collateral-asset
ledger soundness, plus the auxiliary `marketNotBorrower` fact
(`state.collateral marketAddress = 0`) that the
`user ≠ marketAddress` guard in `supplyCollateral` enables. -/
structure MarketAccounting (w : World) : Prop where
  borrowBacked      : BorrowBacked w
  collateralBacked  : CollateralBacked w
  marketNotBorrower : w.state.collateral marketAddress = 0

def AllHealthy (w : World) : Prop := ∀ u, Healthy w u

/-- Last line of defense: each user's ℚ-debt (`debtOf_q`) is covered
by their collateral value at the oracle's reported price.

Reads as "the user's pro-rata share of total borrowed assets does not
exceed their collateral value" — `debtOf_q` is the exact rational
quantity that `debtOf` rounds up to in ℕ.  Proofs convert to the
equivalent share-multiplied (division-free) form via
`assetCoveredAt_iff_shareMul`. -/
def AssetCovered (w : World) : Prop :=
  ∀ u, debtOf_q w.state u ≤ (w.state.collateral u : ℚ) * w.oracle.read_q

/-- Per-user cross-multiplied (division-free) equivalence underlying
`AssetCovered`, valid because `dshTotal + vBS > 0`
(`virtualBorrowShares_pos`).  The share-mul form is what `nlinarith`
chains naturally consume, so most proofs work via this bridge. -/
theorem assetCoveredAt_iff_shareMul (w : World) (u : Addr) :
    debtOf_q w.state u ≤ (w.state.collateral u : ℚ) * w.oracle.read_q
      ↔
    (w.state.debtShares.balances u : ℚ)
            * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
          ≤ (w.state.collateral u : ℚ) * w.oracle.read_q
            * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) := by
  unfold debtOf_q
  have hvBS_pos_q : (0 : ℚ) < (virtualBorrowShares : ℚ) := by
    exact_mod_cast virtualBorrowShares_pos
  have hTs_nn : (0 : ℚ) ≤ (w.state.debtShares.totalSupply : ℚ) := by
    exact_mod_cast Nat.zero_le _
  have hS_pos :
      (0 : ℚ) < (w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares := by
    linarith
  exact div_le_iff₀ hS_pos

/-- ∀-lifted version of `assetCoveredAt_iff_shareMul`. -/
theorem AssetCovered_iff_shareMul (w : World) :
    AssetCovered w ↔
    ∀ u, (w.state.debtShares.balances u : ℚ)
            * ((w.state.totalBorrowAssets : ℚ) + virtualBorrowAssets)
          ≤ (w.state.collateral u : ℚ) * w.oracle.read_q
            * ((w.state.debtShares.totalSupply : ℚ) + virtualBorrowShares) :=
  forall_congr' (assetCoveredAt_iff_shareMul w)

def SupplySharePriceLE (w w' : World) : Prop :=
  (w.state.totalSupplyAssets + virtualSupplyAssets) *
    (w'.state.supplyShares.totalSupply + virtualSupplyShares)
  ≤ (w'.state.totalSupplyAssets + virtualSupplyAssets) *
    (w.state.supplyShares.totalSupply + virtualSupplyShares)

theorem SupplySharePriceLE.refl (w : World) : SupplySharePriceLE w w :=
  Nat.le_refl _

theorem init_bookkeep : Bookkeep init where
  loanAssetInv   := initialLoanAsset_invariant
  collatAssetInv := initialCollateralAsset_invariant
  supplyShareInv := ERC20.init_invariant
  debtShareInv   := ERC20.init_invariant

theorem init_marketAccounting : MarketAccounting init where
  borrowBacked      := by simp [BorrowBacked, init, initState]
  collateralBacked  := by simp [CollateralBacked, init, initState]
  marketNotBorrower := by simp [init, initState]

end Market
