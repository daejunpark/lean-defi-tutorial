import Mathlib.Data.Finsupp.Basic
import Mathlib.Tactic.Ring
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Data.Rat.Floor
import Token
import Util.Fixed

/-!
# Lending Market — State, Oracle, World, configuration constants

Pure structural shape of the protocol: axioms (risk parameters,
market address, initial tokens), the `State` / `Oracle` / `World`
structures, and the Morpho-style liquidation bonus configuration
constants.

State-derived calculations (`debtOf`, `Healthy`, `borrowShareFor`,
…) and operations (`supply`, `liquidate`, `Action`, `step`) live in
`Semantics.lean`.  Invariants (`Bookkeep`, `AssetCovered`, …) live
in `Invariants.lean`.  Region/budget side-condition predicates live
in `Predicates.lean`.

## ℚ-side proof convenience

`toRat` is retained as a proof convenience: `lltv.toRat`,
`liquidationIncentiveFactor.toRat`, and `oracle.read.toRat` are
ℚ-valued aliases used by downstream proofs that reason in
cross-multiplied ℚ form.  These are *not* axioms — they are derived
values defined from the fixed-point axioms below.
-/

namespace Market

abbrev Addr := ERC20.Addr

/-! ### Axioms — risk parameters, market address, initial token states -/

axiom marketAddress : Addr

axiom virtualSupplyAssets : ℕ
axiom virtualSupplyShares : ℕ
axiom virtualBorrowAssets : ℕ
axiom virtualBorrowShares : ℕ
axiom virtualSupplyAssets_pos : 0 < virtualSupplyAssets
axiom virtualSupplyShares_pos : 0 < virtualSupplyShares
axiom virtualBorrowAssets_pos : 0 < virtualBorrowAssets
axiom virtualBorrowShares_pos : 0 < virtualBorrowShares

/-- Pin `virtualBorrowAssets = 1` (matching Morpho Blue's
`VIRTUAL_ASSETS = 1`). -/
axiom virtualBorrowAssets_eq_one : virtualBorrowAssets = 1

/-- Loan-to-value ratio, WAD-scaled.  `(0, 1)` in fixed-point form;
strictly less than `1` matches Morpho's `enableLltv` requirement
(`require(lltv < WAD)`). -/
axiom lltv : Wad
axiom lltv_pos : (0 : Wad) < lltv
axiom lltv_lt_one : lltv < (1 : Wad)

/-- ℚ form of `lltv`, derived from the fixed-point mantissa.  Used by
downstream proofs that reason in cross-multiplied ℚ form.

No `Coe Wad ℚ` is provided — every entry into ℚ-land is explicit via
`lltv_q`, `Oracle.read_q`, `liquidationIncentiveFactor_q`, or a direct
`.toRat`, preserving the plan §1 discipline that mixing scales never
happens silently. -/
noncomputable abbrev lltv_q : ℚ := lltv.toRat

theorem lltv_q_pos : 0 < lltv_q := by
  unfold lltv_q Fixed.toRat
  apply div_pos
  · have h : 0 < lltv.mantissa := lltv_pos
    exact_mod_cast h
  · positivity

theorem lltv_q_lt_one : lltv_q < 1 := by
  unfold lltv_q Fixed.toRat
  rw [div_lt_one (by positivity)]
  have h : lltv.mantissa < 10 ^ 18 := lltv_lt_one
  exact_mod_cast h

theorem lltv_q_le_one : lltv_q ≤ 1 := le_of_lt lltv_q_lt_one

theorem lltv_q_nonneg : 0 ≤ lltv_q := le_of_lt lltv_q_pos

axiom initialLoanAsset : ERC20.State
axiom initialLoanAsset_invariant : ERC20.Invariant initialLoanAsset

axiom initialCollateralAsset : ERC20.State
axiom initialCollateralAsset_invariant : ERC20.Invariant initialCollateralAsset

/-! ### Liquidation bonus configuration

Morpho Blue computes `liquidationIncentiveFactor` per-market on the
fly inside `liquidate`, using the LLTV:

```solidity
uint256 liquidationIncentiveFactor = UtilsLib.min(
    MAX_LIQUIDATION_INCENTIVE_FACTOR,
    WAD.wDivDown(WAD - LIQUIDATION_CURSOR.wMulDown(WAD - marketParams.lltv))
);
```

with `MAX_LIQUIDATION_INCENTIVE_FACTOR = 1.15·WAD` and
`LIQUIDATION_CURSOR = 0.3·WAD`.  We transcribe the formula faithfully
in fixed-point form (Morpho's `wMulDown` / `wDivDown` correspond to
`Fixed.mulFloor` / `Fixed.divFloor` at `target = 18`).

The structural constraint `bonus · lltv < 1` is a **theorem** of the
formula plus `lltv < 1` (proven in `Lemmas.lean` as
`liquidationIncentiveFactor_q_lltv_q_lt_one`) — not an additional
axiom.  This matches Morpho's deployment: governance picks LLTV bounds
and the formula's constants such that the constraint holds, but
Solidity carries no explicit `require(bonus * lltv < 1)` check. -/

/-- `MAX_LIQUIDATION_INCENTIVE_FACTOR = 1.15` (Wad).  Lifted from the
ℚ literal `1.15` via `Fixed.ofRat` (exact since `1.15` has finite
decimal representation within 18 places). -/
def MAX_LIQUIDATION_INCENTIVE_FACTOR : Wad := Fixed.ofRat 1.15

/-- `LIQUIDATION_CURSOR = 0.3` (Wad). -/
def LIQUIDATION_CURSOR : Wad := Fixed.ofRat 0.3

/-- Morpho.sol's per-market `liquidationIncentiveFactor` (from
`liquidate`), faithfully transcribed: every multiplication and
division is the floor-rounded Morpho `wMulDown` / `wDivDown`, the
subtractions are truncating, and `min` matches Morpho's `UtilsLib.min`.

Both operands are `Wad`-typed everywhere, so the same-scale
`Fixed.mulFloor` / `Fixed.divFloor` (= Morpho's `wMulDown` /
`wDivDown`) are used without explicit target/side-condition. -/
noncomputable def morphoLiquidationIncentiveFactor (lltv : Wad) : Wad :=
  min MAX_LIQUIDATION_INCENTIVE_FACTOR
      (Fixed.divFloor (1 : Wad)
         (1 - Fixed.mulFloor LIQUIDATION_CURSOR (1 - lltv)))

/-- Per-market bonus, bound to the protocol's `lltv` axiom via the
Morpho formula.  No longer an axiom; its properties (≥ 1, · lltv < 1)
are theorems in `Lemmas.lean`. -/
noncomputable abbrev liquidationIncentiveFactor : Wad :=
  morphoLiquidationIncentiveFactor lltv

/-- ℚ form of the bonus, for cross-multiplied algebra. -/
noncomputable abbrev liquidationIncentiveFactor_q : ℚ :=
  liquidationIncentiveFactor.toRat

/-! ### State -/

structure State where
  loanAsset         : ERC20.State
  collateralAsset   : ERC20.State
  supplyShares      : ERC20.State
  debtShares        : ERC20.State
  totalSupplyAssets : ℕ
  totalBorrowAssets : ℕ
  collateral        : Addr →₀ ℕ

noncomputable def initState : State where
  loanAsset         := initialLoanAsset
  collateralAsset   := initialCollateralAsset
  supplyShares      := ERC20.init
  debtShares        := ERC20.init
  totalSupplyAssets := 0
  totalBorrowAssets := 0
  collateral        := 0

/-! ### Oracle

Stores a Morpho-`ORACLE_PRICE_SCALE`-scaled price (`mantissa / 10^36`).
Read returns the typed price; downstream ℚ algebra goes through
`.toRat`. -/

structure Oracle where
  price : OraclePrice

def Oracle.read (o : Oracle) : OraclePrice := o.price

def Oracle.update (_o : Oracle) (p : OraclePrice) : Oracle := { price := p }

@[simp] lemma Oracle.read_update (o : Oracle) (p : OraclePrice) :
    (Oracle.update o p).read = p := rfl

/-- ℚ form of the oracle's current read, derived from the fixed-point
mantissa.  Used by downstream proofs that reason in cross-multiplied
ℚ form. -/
noncomputable abbrev Oracle.read_q (o : Oracle) : ℚ := o.read.toRat

@[simp] lemma Oracle.read_q_update (o : Oracle) (p : OraclePrice) :
    (Oracle.update o p).read_q = p.toRat := rfl

theorem Oracle.read_q_nonneg (o : Oracle) : 0 ≤ o.read_q :=
  Fixed.toRat_nonneg _

/-! ### World

Bundles the protocol-owned `state` with the externally-fed `oracle`. -/

structure World where
  state  : State
  oracle : Oracle

noncomputable def init : World where
  state  := initState
  oracle := { price := ⟨0⟩ }

end Market
