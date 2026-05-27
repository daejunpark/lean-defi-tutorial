import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Cast.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push
import Util.CeilDiv

/-!
# Decimal fixed-point arithmetic

`Fixed s` is a `Nat` mantissa tagged with a phantom scale `s : Nat`;
the value it denotes is `mantissa / 10^s`.  Scales are part of the
type, so values of different scales are distinct types and any
heterogeneous operation (addition, comparison) is rejected at compile
time.

Multiplication is *exact*: scales add, no information loss.  Returning
to a desired scale uses an explicit rounding operation, `floorTo`
(round down) or `ceilTo` (round up), mirroring Morpho's discipline of
making every rounding step visible.

The two named scales used by Morpho Blue:

- `Wad := Fixed 18` — `lltv`, `liquidationIncentiveFactor`, fee, IRM
- `OraclePrice := Fixed 36` — `oracle.price`
-/

structure Fixed (scale : Nat) where
  mantissa : Nat
deriving DecidableEq, Repr

abbrev Wad         := Fixed 18
abbrev OraclePrice := Fixed 36

namespace Fixed

variable {s s₁ s₂ : Nat}

/-! ### Same-scale algebra

No heterogeneous instances are defined.  `Fixed 18 + Fixed 36`,
`Fixed 18 ≤ Fixed 36`, etc. are compile-time type errors. -/

instance : Zero (Fixed s) := ⟨⟨0⟩⟩
/-- The fixed-point value `1.0` at scale `s` has mantissa `10^s`. -/
instance : One (Fixed s) := ⟨⟨10 ^ s⟩⟩
instance : Inhabited (Fixed s) := ⟨0⟩
instance : Add (Fixed s) := ⟨fun x y => ⟨x.mantissa + y.mantissa⟩⟩
/-- Truncating subtraction (matches Solidity's `uint256` arithmetic in the
no-underflow path; underflowing gives `0` rather than reverting — callers
are responsible for proving no underflow before reasoning about toRat). -/
instance : Sub (Fixed s) := ⟨fun x y => ⟨x.mantissa - y.mantissa⟩⟩
instance : Min (Fixed s) := ⟨fun x y => ⟨min x.mantissa y.mantissa⟩⟩
instance : LE  (Fixed s) := ⟨fun x y => x.mantissa ≤ y.mantissa⟩
instance : LT  (Fixed s) := ⟨fun x y => x.mantissa < y.mantissa⟩
instance (x y : Fixed s) : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.mantissa ≤ y.mantissa))
instance (x y : Fixed s) : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.mantissa < y.mantissa))

@[simp] lemma zero_mantissa : (0 : Fixed s).mantissa = 0 := rfl

@[simp] lemma one_mantissa : (1 : Fixed s).mantissa = 10 ^ s := rfl

@[simp] lemma sub_mantissa (x y : Fixed s) :
    (x - y).mantissa = x.mantissa - y.mantissa := rfl

@[simp] lemma min_mantissa (x y : Fixed s) :
    (min x y).mantissa = min x.mantissa y.mantissa := rfl

@[simp] lemma add_mantissa (x y : Fixed s) :
    (x + y).mantissa = x.mantissa + y.mantissa := rfl

@[simp] lemma le_iff_mantissa (x y : Fixed s) :
    x ≤ y ↔ x.mantissa ≤ y.mantissa := Iff.rfl

@[simp] lemma lt_iff_mantissa (x y : Fixed s) :
    x < y ↔ x.mantissa < y.mantissa := Iff.rfl

/-! ### Multiplication (exact; scales add) -/

def mul (x : Fixed s₁) (y : Fixed s₂) : Fixed (s₁ + s₂) :=
  ⟨x.mantissa * y.mantissa⟩

@[simp] lemma mul_mantissa (x : Fixed s₁) (y : Fixed s₂) :
    (x.mul y).mantissa = x.mantissa * y.mantissa := rfl

/-! ### Rounding to a smaller scale -/

def floorTo (target : Nat) (x : Fixed s) (_h : target ≤ s := by decide) :
    Fixed target :=
  ⟨x.mantissa / 10 ^ (s - target)⟩

def ceilTo (target : Nat) (x : Fixed s) (_h : target ≤ s := by decide) :
    Fixed target :=
  ⟨Util.ceilDiv x.mantissa (10 ^ (s - target))⟩

@[simp] lemma floorTo_mantissa (target : Nat) (x : Fixed s) (h : target ≤ s) :
    (x.floorTo target h).mantissa = x.mantissa / 10 ^ (s - target) := rfl

@[simp] lemma ceilTo_mantissa (target : Nat) (x : Fixed s) (h : target ≤ s) :
    (x.ceilTo target h).mantissa = Util.ceilDiv x.mantissa (10 ^ (s - target)) := rfl

/-! ### `Nat` ↔ `Fixed 0` (scale 0) -/

def ofNat (n : Nat) : Fixed 0 := ⟨n⟩

/-- Typed exit from `Fixed 0` to `Nat`.  Only defined at scale 0 — at
any other scale the mantissa is *not* the integer value it denotes, so
forcing the conversion to type-check at `Fixed 0` makes the round-trip
through the fixed-point library unambiguous.

Spec/op sites should use this in preference to direct `.mantissa`
field access whenever the result is meant to be a `Nat` quantity (e.g.
the seized collateral amount). -/
def toNat (x : Fixed 0) : Nat := x.mantissa

@[simp] lemma ofNat_mantissa (n : Nat) : (ofNat n).mantissa = n := rfl

@[simp] lemma toNat_mantissa (x : Fixed 0) : x.toNat = x.mantissa := rfl

@[simp] lemma toNat_ofNat (n : Nat) : (ofNat n).toNat = n := rfl

@[simp] lemma ofNat_toNat (x : Fixed 0) : ofNat x.toNat = x := by
  obtain ⟨_⟩ := x; rfl

/-! ### Bridge to ℚ

Used to derive ℚ-form versions of fixed-point statements; the existing
ℚ proofs go through `toRat` rather than being rewritten. -/

def toRat (x : Fixed s) : ℚ := (x.mantissa : ℚ) / (10 : ℚ) ^ s

/-- Lift a non-negative `ℚ` to fixed-point at scale `s` via floor.
The `0 ≤ q` precondition is an autoparam discharged by `norm_num`,
which handles every concrete non-negative ℚ literal automatically and
rejects negatives at compile time (rather than silently truncating
them to `0` via `Int.toNat`).

For exact representations the lift is exact:
`Fixed.ofRat (115/100) 18 = ⟨115 · 10^16⟩`.  Otherwise floor-rounds
toward zero, matching Solidity's `wMulDown` convention. -/
def ofRat (q : ℚ) (_h : 0 ≤ q := by norm_num) : Fixed s :=
  ⟨⌊q * (10 : ℚ) ^ s⌋.toNat⟩

@[simp] lemma ofRat_mantissa (q : ℚ) (h : 0 ≤ q) :
    (ofRat q h : Fixed s).mantissa = ⌊q * (10 : ℚ) ^ s⌋.toNat := rfl

@[simp] lemma toRat_zero : (0 : Fixed s).toRat = 0 := by
  simp [toRat]

@[simp] lemma toRat_one : (1 : Fixed s).toRat = 1 := by
  unfold toRat
  show ((10 ^ s : ℕ) : ℚ) / (10 : ℚ) ^ s = 1
  push_cast
  rw [div_self (by positivity)]

@[simp] lemma toRat_ofNat (n : Nat) : (ofNat n).toRat = (n : ℚ) := by
  simp [toRat, ofNat]

lemma toRat_nonneg (x : Fixed s) : 0 ≤ x.toRat := by
  unfold toRat
  apply div_nonneg
  · exact_mod_cast Nat.zero_le _
  · positivity

lemma toRat_mono {x y : Fixed s} (h : x ≤ y) : x.toRat ≤ y.toRat := by
  unfold toRat
  have h10 : (0 : ℚ) < (10 : ℚ) ^ s := by positivity
  have hq : ((x.mantissa : ℕ) : ℚ) ≤ ((y.mantissa : ℕ) : ℚ) := by exact_mod_cast h
  exact div_le_div_of_nonneg_right hq (le_of_lt h10)

lemma toRat_min (x y : Fixed s) : (min x y).toRat = min x.toRat y.toRat := by
  show ((min x.mantissa y.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ s = min x.toRat y.toRat
  by_cases h : x.mantissa ≤ y.mantissa
  · rw [min_eq_left h, min_eq_left (toRat_mono (s := s) h)]
    rfl
  · push Not at h
    have h' : y.mantissa ≤ x.mantissa := le_of_lt h
    rw [min_eq_right h', min_eq_right (toRat_mono (s := s) h')]
    rfl

/-- Truncating subtraction matches ℚ subtraction in the no-underflow case. -/
lemma toRat_sub_of_le {x y : Fixed s} (h : y ≤ x) :
    (x - y).toRat = x.toRat - y.toRat := by
  unfold toRat
  show ((x.mantissa - y.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ s
     = (x.mantissa : ℚ) / (10 : ℚ) ^ s - (y.mantissa : ℚ) / (10 : ℚ) ^ s
  have hq : ((x.mantissa - y.mantissa : ℕ) : ℚ)
          = ((x.mantissa : ℕ) : ℚ) - ((y.mantissa : ℕ) : ℚ) := by
    rw [Nat.cast_sub h]
  rw [hq, sub_div]

lemma toRat_mul (x : Fixed s₁) (y : Fixed s₂) :
    (x.mul y).toRat = x.toRat * y.toRat := by
  show ((x.mantissa * y.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ (s₁ + s₂)
      = ((x.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ s₁
        * (((y.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ s₂)
  push_cast
  rw [pow_add]
  rw [div_mul_div_comm]

/-! ### Rounding bounds (single-unit slack at the target scale)

To avoid the "motive is not type correct" failure when rewriting `s`
in a goal that still mentions `x : Fixed s`, each proof first destructs
`x` so the goal speaks only of `Nat` mantissas. -/

private lemma pow10_pos_q (n : Nat) : (0 : ℚ) < (10 : ℚ) ^ n := by positivity
private lemma pow10_pos_n (n : Nat) : 0 < (10 : ℕ) ^ n := by positivity

lemma floorTo_toRat_le (target : Nat) (x : Fixed s) (h : target ≤ s) :
    (x.floorTo target h).toRat ≤ x.toRat := by
  obtain ⟨m⟩ := x
  set k := s - target with hk_def
  have hs_eq : s = target + k := by omega
  have h10k_q : (0 : ℚ) < (10 : ℚ) ^ k := pow10_pos_q k
  have h10t_q : (0 : ℚ) < (10 : ℚ) ^ target := pow10_pos_q target
  have hcore : (m / 10 ^ k) * (10 ^ k) ≤ m := Nat.div_mul_le_self _ _
  have hcore_q : ((m / 10 ^ k : ℕ) : ℚ) * (10 : ℚ) ^ k ≤ (m : ℚ) := by
    exact_mod_cast hcore
  show ((m / 10 ^ k : ℕ) : ℚ) / (10 : ℚ) ^ target ≤ (m : ℚ) / (10 : ℚ) ^ s
  rw [hs_eq, pow_add, div_le_div_iff₀ h10t_q (mul_pos h10t_q h10k_q)]
  nlinarith [hcore_q, h10t_q, h10k_q]

lemma toRat_lt_floorTo_add_unit (target : Nat) (x : Fixed s) (h : target ≤ s) :
    x.toRat < (x.floorTo target h).toRat + (1 : ℚ) / (10 : ℚ) ^ target := by
  obtain ⟨m⟩ := x
  set k := s - target with hk_def
  have hs_eq : s = target + k := by omega
  have h10k_n : 0 < (10 : ℕ) ^ k := pow10_pos_n k
  have h10k_q : (0 : ℚ) < (10 : ℚ) ^ k := pow10_pos_q k
  have h10t_q : (0 : ℚ) < (10 : ℚ) ^ target := pow10_pos_q target
  have hmod : m % (10 ^ k) < 10 ^ k := Nat.mod_lt _ h10k_n
  have hdvd : 10 ^ k * (m / 10 ^ k) + m % 10 ^ k = m := Nat.div_add_mod _ _
  have hkey : m < (m / 10 ^ k + 1) * 10 ^ k := by nlinarith
  have hkey_q : (m : ℚ)
              < ((m / 10 ^ k : ℕ) : ℚ) * (10 : ℚ) ^ k + (10 : ℚ) ^ k := by
    have := (Nat.cast_lt (α := ℚ)).mpr hkey
    push_cast at this
    linarith
  show (m : ℚ) / (10 : ℚ) ^ s
      < ((m / 10 ^ k : ℕ) : ℚ) / (10 : ℚ) ^ target + 1 / (10 : ℚ) ^ target
  rw [show ((m / 10 ^ k : ℕ) : ℚ) / (10 : ℚ) ^ target + 1 / (10 : ℚ) ^ target
        = (((m / 10 ^ k : ℕ) : ℚ) + 1) / (10 : ℚ) ^ target from
      (add_div _ _ _).symm, hs_eq, pow_add,
      div_lt_div_iff₀ (mul_pos h10t_q h10k_q) h10t_q]
  nlinarith [hkey_q, h10t_q, h10k_q]

lemma ceilTo_toRat_ge (target : Nat) (x : Fixed s) (h : target ≤ s) :
    x.toRat ≤ (x.ceilTo target h).toRat := by
  obtain ⟨m⟩ := x
  set k := s - target with hk_def
  have hs_eq : s = target + k := by omega
  have h10k_n : 0 < (10 : ℕ) ^ k := pow10_pos_n k
  have h10k_q : (0 : ℚ) < (10 : ℚ) ^ k := pow10_pos_q k
  have h10t_q : (0 : ℚ) < (10 : ℚ) ^ target := pow10_pos_q target
  have hcore : m ≤ Util.ceilDiv m (10 ^ k) * (10 ^ k) :=
    Util.ceilDiv_mul_ge _ h10k_n
  have hcore_q : (m : ℚ)
                ≤ ((Util.ceilDiv m (10 ^ k) : ℕ) : ℚ) * (10 : ℚ) ^ k := by
    exact_mod_cast hcore
  show (m : ℚ) / (10 : ℚ) ^ s
      ≤ ((Util.ceilDiv m (10 ^ k) : ℕ) : ℚ) / (10 : ℚ) ^ target
  rw [hs_eq, pow_add, div_le_div_iff₀ (mul_pos h10t_q h10k_q) h10t_q]
  nlinarith [hcore_q, h10t_q, h10k_q]

/-! ### Multiplication / division with rounding to a chosen scale

Two related APIs:

* **Same-scale** (the common case, mirroring Morpho's
  `wMulDown` / `wDivDown` etc.): both arguments at scale `s`, result at
  scale `s`.  Names: `mulFloor`, `mulCeil`, `divFloor`, `divCeil`.
* **Cross-scale** (the general case): two arbitrary scales, explicit
  `target`.  Names: `mulFloorAt`, `mulCeilAt`, `divFloorAt`, `divCeilAt`.

The same-scale versions are 2-argument wrappers around the `*At`
forms with `target := s` and the side condition discharged once.

Mantissa-level interpretation (cross-scale):

| Helper                 | `result.mantissa`                                        | Side condition           |
|------------------------|----------------------------------------------------------|--------------------------|
| `mulFloorAt x y t`     | `x.mantissa * y.mantissa / 10^(s₁ + s₂ - t)`            | `t ≤ s₁ + s₂`            |
| `mulCeilAt  x y t`     | `ceilDiv (x.mantissa * y.mantissa) (10^(s₁ + s₂ - t))`  | `t ≤ s₁ + s₂`            |
| `divFloorAt x y t`     | `x.mantissa * 10^(s₂ + t - s₁) / y.mantissa`            | `s₁ ≤ s₂ + t`            |
| `divCeilAt  x y t`     | `ceilDiv (x.mantissa * 10^(s₂ + t - s₁)) y.mantissa`    | `s₁ ≤ s₂ + t`            |

`divFloorAt`/`divCeilAt` return `0` when `y.mantissa = 0` (Lean's
convention for `Nat` division), making them total. -/

def mulFloorAt (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : target ≤ s₁ + s₂ := by decide) : Fixed target :=
  (x.mul y).floorTo target h

def mulCeilAt (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : target ≤ s₁ + s₂ := by decide) : Fixed target :=
  (x.mul y).ceilTo target h

def divFloorAt (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (_h : s₁ ≤ s₂ + target := by decide) : Fixed target :=
  ⟨x.mantissa * 10 ^ (s₂ + target - s₁) / y.mantissa⟩

def divCeilAt (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (_h : s₁ ≤ s₂ + target := by decide) : Fixed target :=
  ⟨Util.ceilDiv (x.mantissa * 10 ^ (s₂ + target - s₁)) y.mantissa⟩

/-! #### Same-scale shorthands

These are the everyday `wMulDown` / `wDivDown` / `wMulUp` / `wDivUp`
analogues — both arguments and result at the same scale `s`. -/

def mulFloor (x y : Fixed s) : Fixed s := mulFloorAt x y s (by omega)
def mulCeil  (x y : Fixed s) : Fixed s := mulCeilAt  x y s (by omega)
def divFloor (x y : Fixed s) : Fixed s := divFloorAt x y s (by omega)
def divCeil  (x y : Fixed s) : Fixed s := divCeilAt  x y s (by omega)

@[simp] lemma mulFloorAt_mantissa (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : target ≤ s₁ + s₂) :
    (mulFloorAt x y target h).mantissa =
      x.mantissa * y.mantissa / 10 ^ (s₁ + s₂ - target) := rfl

@[simp] lemma mulCeilAt_mantissa (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : target ≤ s₁ + s₂) :
    (mulCeilAt x y target h).mantissa =
      Util.ceilDiv (x.mantissa * y.mantissa) (10 ^ (s₁ + s₂ - target)) := rfl

@[simp] lemma divFloorAt_mantissa (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : s₁ ≤ s₂ + target) :
    (divFloorAt x y target h).mantissa =
      x.mantissa * 10 ^ (s₂ + target - s₁) / y.mantissa := rfl

@[simp] lemma divCeilAt_mantissa (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : s₁ ≤ s₂ + target) :
    (divCeilAt x y target h).mantissa =
      Util.ceilDiv (x.mantissa * 10 ^ (s₂ + target - s₁)) y.mantissa := rfl

@[simp] lemma mulFloor_mantissa (x y : Fixed s) :
    (mulFloor x y).mantissa = x.mantissa * y.mantissa / 10 ^ s := by
  show (mulFloorAt x y s _).mantissa = _
  rw [mulFloorAt_mantissa, show s + s - s = s by omega]

@[simp] lemma mulCeil_mantissa (x y : Fixed s) :
    (mulCeil x y).mantissa = Util.ceilDiv (x.mantissa * y.mantissa) (10 ^ s) := by
  show (mulCeilAt x y s _).mantissa = _
  rw [mulCeilAt_mantissa, show s + s - s = s by omega]

@[simp] lemma divFloor_mantissa (x y : Fixed s) :
    (divFloor x y).mantissa = x.mantissa * 10 ^ s / y.mantissa := by
  show (divFloorAt x y s _).mantissa = _
  rw [divFloorAt_mantissa, show s + s - s = s by omega]

@[simp] lemma divCeil_mantissa (x y : Fixed s) :
    (divCeil x y).mantissa = Util.ceilDiv (x.mantissa * 10 ^ s) y.mantissa := by
  show (divCeilAt x y s _).mantissa = _
  rw [divCeilAt_mantissa, show s + s - s = s by omega]

/-! ### `toRat` bridges for `mulFloorAt` / `mulCeilAt`

Derived from `floorTo_toRat_le` / `ceilTo_toRat_ge` and `toRat_mul`.
Division-side bridges (`divFloorAt_toRat_le`, slack, `divCeilAt_toRat_ge`)
are stated below directly on mantissas because there is no exact
division op to delegate to.

Same-scale shorthands (`mulFloor_toRat_le` etc.) follow at the end of
each block — they are 2-argument convenience versions that delegate
to the `*At` form. -/

lemma mulFloorAt_toRat_le (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : target ≤ s₁ + s₂) :
    (mulFloorAt x y target h).toRat ≤ x.toRat * y.toRat := by
  unfold mulFloorAt
  have hfl := floorTo_toRat_le target (x.mul y) h
  rwa [toRat_mul] at hfl

lemma toRat_mul_lt_mulFloorAt_add_unit (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : target ≤ s₁ + s₂) :
    x.toRat * y.toRat < (mulFloorAt x y target h).toRat + (1 : ℚ) / (10 : ℚ) ^ target := by
  unfold mulFloorAt
  have h_slack := toRat_lt_floorTo_add_unit target (x.mul y) h
  rwa [toRat_mul] at h_slack

lemma toRat_mul_le_mulCeilAt (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : target ≤ s₁ + s₂) :
    x.toRat * y.toRat ≤ (mulCeilAt x y target h).toRat := by
  unfold mulCeilAt
  have hce := ceilTo_toRat_ge target (x.mul y) h
  rwa [toRat_mul] at hce

/-- Same-scale `mulFloor`-bound (Morpho's `wMulDown` toRat ≤ exact). -/
lemma mulFloor_toRat_le (x y : Fixed s) :
    (mulFloor x y).toRat ≤ x.toRat * y.toRat :=
  mulFloorAt_toRat_le x y s (by omega)

lemma toRat_mul_lt_mulFloor_add_unit (x y : Fixed s) :
    x.toRat * y.toRat < (mulFloor x y).toRat + (1 : ℚ) / (10 : ℚ) ^ s :=
  toRat_mul_lt_mulFloorAt_add_unit x y s (by omega)

lemma toRat_mul_le_mulCeil (x y : Fixed s) :
    x.toRat * y.toRat ≤ (mulCeil x y).toRat :=
  toRat_mul_le_mulCeilAt x y s (by omega)

/-! ### `toRat` bridges for `divFloorAt` / `divCeilAt`

All three are stated under `0 < y.mantissa` so `y.toRat > 0` and
ℚ-division is meaningful.  Algebra rests on the identity

  `x.toRat / y.toRat = (x.mantissa * 10^k) / (10^target * y.mantissa)`

where `k = s₂ + target - s₁` (`s₁ + k = s₂ + target` by the
hypothesis `s₁ ≤ s₂ + target`).  After this rewrite both bounds
reduce to one-step Nat-division facts on `x.mantissa * 10^k` and
`y.mantissa`.

Same-scale shorthands (`divFloor_toRat_le` etc.) follow at the end. -/

private lemma toRat_div_eq_aux (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : s₁ ≤ s₂ + target) (hy : 0 < y.mantissa) :
    let k := s₂ + target - s₁
    x.toRat / y.toRat
      = ((x.mantissa : ℚ) * (10 : ℚ) ^ k)
        / ((10 : ℚ) ^ target * (y.mantissa : ℚ)) := by
  set k := s₂ + target - s₁ with hk_def
  have hsum : s₂ + target = s₁ + k := by omega
  have hpow_eq :
      (10 : ℚ) ^ s₂ * (10 : ℚ) ^ target = (10 : ℚ) ^ s₁ * (10 : ℚ) ^ k := by
    rw [← pow_add, ← pow_add, hsum]
  have h10s1_q : (0 : ℚ) < (10 : ℚ) ^ s₁ := pow10_pos_q s₁
  have h10s2_q : (0 : ℚ) < (10 : ℚ) ^ s₂ := pow10_pos_q s₂
  have h10t_q : (0 : ℚ) < (10 : ℚ) ^ target := pow10_pos_q target
  have hyq : (0 : ℚ) < (y.mantissa : ℚ) := by exact_mod_cast hy
  show ((x.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ s₁
        / (((y.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ s₂)
      = ((x.mantissa : ℚ) * (10 : ℚ) ^ k)
        / ((10 : ℚ) ^ target * (y.mantissa : ℚ))
  rw [div_div_eq_mul_div, div_mul_eq_mul_div, div_div,
      div_eq_div_iff (mul_pos h10s1_q hyq).ne' (mul_pos h10t_q hyq).ne']
  calc ((x.mantissa : ℕ) : ℚ) * (10 : ℚ) ^ s₂ * ((10 : ℚ) ^ target * (y.mantissa : ℚ))
      = ((x.mantissa : ℕ) : ℚ) * (y.mantissa : ℚ)
          * ((10 : ℚ) ^ s₂ * (10 : ℚ) ^ target) := by ring
    _ = ((x.mantissa : ℕ) : ℚ) * (y.mantissa : ℚ)
          * ((10 : ℚ) ^ s₁ * (10 : ℚ) ^ k) := by rw [hpow_eq]
    _ = ((x.mantissa : ℚ) * (10 : ℚ) ^ k) * ((10 : ℚ) ^ s₁ * (y.mantissa : ℚ)) := by
          ring

lemma divFloorAt_toRat_le (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : s₁ ≤ s₂ + target) (hy : 0 < y.mantissa) :
    (divFloorAt x y target h).toRat ≤ x.toRat / y.toRat := by
  set k := s₂ + target - s₁ with hk_def
  have h10t_q : (0 : ℚ) < (10 : ℚ) ^ target := pow10_pos_q target
  have hyq : (0 : ℚ) < (y.mantissa : ℚ) := by exact_mod_cast hy
  have hcore :
      (x.mantissa * 10 ^ k / y.mantissa) * y.mantissa ≤ x.mantissa * 10 ^ k :=
    Nat.div_mul_le_self _ _
  have hcore_q :
      ((x.mantissa * 10 ^ k / y.mantissa : ℕ) : ℚ) * (y.mantissa : ℚ)
        ≤ ((x.mantissa : ℕ) : ℚ) * (10 : ℚ) ^ k := by
    have := (Nat.cast_le (α := ℚ)).mpr hcore
    push_cast at this
    exact this
  rw [toRat_div_eq_aux x y target h hy]
  show ((x.mantissa * 10 ^ k / y.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ target
      ≤ ((x.mantissa : ℚ) * (10 : ℚ) ^ k)
        / ((10 : ℚ) ^ target * (y.mantissa : ℚ))
  rw [div_le_div_iff₀ h10t_q (mul_pos h10t_q hyq)]
  nlinarith [hcore_q, h10t_q, hyq, pow10_pos_q k]

lemma toRat_div_lt_divFloorAt_add_unit (x : Fixed s₁) (y : Fixed s₂)
    (target : Nat) (h : s₁ ≤ s₂ + target) (hy : 0 < y.mantissa) :
    x.toRat / y.toRat
      < (divFloorAt x y target h).toRat + (1 : ℚ) / (10 : ℚ) ^ target := by
  set k := s₂ + target - s₁ with hk_def
  have h10t_q : (0 : ℚ) < (10 : ℚ) ^ target := pow10_pos_q target
  have h10k_q : (0 : ℚ) < (10 : ℚ) ^ k := pow10_pos_q k
  have hyq : (0 : ℚ) < (y.mantissa : ℚ) := by exact_mod_cast hy
  -- Strict Nat-division bound: `a < (a / b + 1) * b` for `0 < b`.
  have hcore :
      x.mantissa * 10 ^ k
        < (x.mantissa * 10 ^ k / y.mantissa + 1) * y.mantissa := by
    have h_mod := Nat.div_add_mod (x.mantissa * 10 ^ k) y.mantissa
    have h_mod_lt := Nat.mod_lt (x.mantissa * 10 ^ k) hy
    nlinarith [h_mod, h_mod_lt]
  have hcore_q :
      ((x.mantissa : ℕ) : ℚ) * (10 : ℚ) ^ k
        < (((x.mantissa * 10 ^ k / y.mantissa : ℕ) : ℚ) + 1)
          * ((y.mantissa : ℕ) : ℚ) := by
    have := (Nat.cast_lt (α := ℚ)).mpr hcore
    push_cast at this
    linarith
  rw [toRat_div_eq_aux x y target h hy]
  show ((x.mantissa : ℚ) * (10 : ℚ) ^ k)
        / ((10 : ℚ) ^ target * (y.mantissa : ℚ))
      < ((x.mantissa * 10 ^ k / y.mantissa : ℕ) : ℚ) / (10 : ℚ) ^ target
        + 1 / (10 : ℚ) ^ target
  rw [← add_div,
      div_lt_div_iff₀ (mul_pos h10t_q hyq) h10t_q]
  nlinarith [hcore_q, h10t_q, hyq, h10k_q]

lemma divCeilAt_toRat_ge (x : Fixed s₁) (y : Fixed s₂) (target : Nat)
    (h : s₁ ≤ s₂ + target) (hy : 0 < y.mantissa) :
    x.toRat / y.toRat ≤ (divCeilAt x y target h).toRat := by
  set k := s₂ + target - s₁ with hk_def
  have h10t_q : (0 : ℚ) < (10 : ℚ) ^ target := pow10_pos_q target
  have h10k_q : (0 : ℚ) < (10 : ℚ) ^ k := pow10_pos_q k
  have hyq : (0 : ℚ) < (y.mantissa : ℚ) := by exact_mod_cast hy
  have hcore :
      x.mantissa * 10 ^ k
        ≤ Util.ceilDiv (x.mantissa * 10 ^ k) y.mantissa * y.mantissa :=
    Util.ceilDiv_mul_ge _ hy
  have hcore_q :
      ((x.mantissa : ℕ) : ℚ) * (10 : ℚ) ^ k
        ≤ ((Util.ceilDiv (x.mantissa * 10 ^ k) y.mantissa : ℕ) : ℚ)
          * ((y.mantissa : ℕ) : ℚ) := by
    have := (Nat.cast_le (α := ℚ)).mpr hcore
    push_cast at this
    linarith
  rw [toRat_div_eq_aux x y target h hy]
  show ((x.mantissa : ℚ) * (10 : ℚ) ^ k)
        / ((10 : ℚ) ^ target * (y.mantissa : ℚ))
      ≤ ((Util.ceilDiv (x.mantissa * 10 ^ k) y.mantissa : ℕ) : ℚ)
        / (10 : ℚ) ^ target
  rw [div_le_div_iff₀ (mul_pos h10t_q hyq) h10t_q]
  nlinarith [hcore_q, h10t_q, hyq, h10k_q]

/-! ### Same-scale `divFloor` / `divCeil` toRat bridges -/

lemma divFloor_toRat_le (x y : Fixed s) (hy : 0 < y.mantissa) :
    (divFloor x y).toRat ≤ x.toRat / y.toRat :=
  divFloorAt_toRat_le x y s (by omega) hy

lemma toRat_div_lt_divFloor_add_unit (x y : Fixed s) (hy : 0 < y.mantissa) :
    x.toRat / y.toRat < (divFloor x y).toRat + (1 : ℚ) / (10 : ℚ) ^ s :=
  toRat_div_lt_divFloorAt_add_unit x y s (by omega) hy

lemma divCeil_toRat_ge (x y : Fixed s) (hy : 0 < y.mantissa) :
    x.toRat / y.toRat ≤ (divCeil x y).toRat :=
  divCeilAt_toRat_ge x y s (by omega) hy

/-! ### Monotonicity -/

lemma mul_le_mul_left (x : Fixed s₁) {y z : Fixed s₂} (h : y ≤ z) :
    x.mul y ≤ x.mul z := by
  have h' : y.mantissa ≤ z.mantissa := h
  simp only [le_iff_mantissa, mul_mantissa]
  exact Nat.mul_le_mul_left _ h'

lemma mul_le_mul_right {x y : Fixed s₁} (z : Fixed s₂) (h : x ≤ y) :
    x.mul z ≤ y.mul z := by
  have h' : x.mantissa ≤ y.mantissa := h
  simp only [le_iff_mantissa, mul_mantissa]
  exact Nat.mul_le_mul_right _ h'

lemma floorTo_mono (target : Nat) {x y : Fixed s}
    (h : target ≤ s) (hxy : x ≤ y) :
    x.floorTo target h ≤ y.floorTo target h := by
  have hxy' : x.mantissa ≤ y.mantissa := hxy
  simp only [le_iff_mantissa, floorTo_mantissa]
  exact Nat.div_le_div_right hxy'

lemma ceilTo_mono (target : Nat) {x y : Fixed s}
    (h : target ≤ s) (hxy : x ≤ y) :
    x.ceilTo target h ≤ y.ceilTo target h := by
  have hxy' : x.mantissa ≤ y.mantissa := hxy
  simp only [le_iff_mantissa, ceilTo_mantissa, Util.ceilDiv]
  apply Nat.div_le_div_right
  omega

end Fixed

/-! ### Compile-time type-safety regression pins

Adding (or comparing) values of different scales is a compile-time
type error.  `#check_failure` makes a regression a build failure: if
someone accidentally adds a cross-scale `HAdd` / `HLE` / `HLT`
instance, one of these commands will start to succeed and the file
will refuse to elaborate. -/

section TypeSafetyPins

#check_failure (fun (a : Wad) (p : OraclePrice) => a + p)
#check_failure (fun (a : Wad) (p : OraclePrice) => p + a)
#check_failure (fun (a : Wad) (p : OraclePrice) => a ≤ p)
#check_failure (fun (a : Wad) (p : OraclePrice) => a < p)

end TypeSafetyPins
