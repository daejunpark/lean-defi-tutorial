import Defs.States
import Defs.Semantics
import Defs.Invariants
import Defs.Predicates
import Proofs.Lemmas
import Proofs.Bookkeep
import Proofs.Accounting
import Proofs.SharePrice
import Proofs.AllHealthy
import Proofs.AssetCovered
import Proofs.AllHealthyToAssetCovered
import Proofs.RoundTrip
import Proofs.Liquidation
import Proofs.RepayBudget

/-!
# Lending Market — umbrella

A Morpho-Blue-style isolated lending market. Importing this module
brings in the full set of definitions and theorems.

## Definitions (`Defs/`)

| File           | Contents |
|----------------|----------|
| `Defs.States`     | Risk parameters, market/oracle/world state, `init` |
| `Defs.Semantics`  | Share-conversion formulas, every user operation, `accrueInterest`, liquidation, the `Action` inductive and `step` |
| `Defs.Invariants` | `Bookkeep`, `MarketAccounting`, `AllHealthy`, `AssetCovered`, `SupplySharePriceLE` |
| `Defs.Predicates` | Action filters and budget predicates (`NoBadDebt`, `AccrualBudget`, `PriceMoveBudget`, …); region predicates (`Healable`, `BadDebtPath`) |

## Proofs (`Proofs/`)

| File                              | Contents |
|-----------------------------------|----------|
| `Proofs.Lemmas`                   | Cross-file helpers: ERC-20 shape lemmas, conversion bounds, op/step extracts, liquidation-bonus theorems |
| `Proofs.Bookkeep`                 | `Bookkeep` preservation (per-op + step) |
| `Proofs.Accounting`               | `MarketAccounting` preservation |
| `Proofs.SharePrice`               | `SupplySharePriceLE` preservation |
| `Proofs.AllHealthy`               | `AllHealthy` preservation (per-op + step) |
| `Proofs.AssetCovered`             | `AssetCovered → AssetCovered` preservation under budgets |
| `Proofs.AllHealthyToAssetCovered` | Chain bridging `AllHealthy` to `AssetCovered` |
| `Proofs.RoundTrip`                | Tier-2 round-trip and Tier-3 health theorems |
| `Proofs.Liquidation`              | Headline safety theorems for `liquidate`/`writeOff`, region analysis, closed-form healing existence |
| `Proofs.RepayBudget`              | Repay-share threshold analysis (`maxSafeRepayShares`, `BorrowPriceFloor`) |
-/
