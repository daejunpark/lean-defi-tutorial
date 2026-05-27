import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Group.Nat

/-!
# Ceiling division on `ℕ`

Shared helper used by both ERC-4626 and Lending modules.  Lean's `/`
on `ℕ` is floor; ceiling division is encoded as `(a + b - 1) / b`.
-/

namespace Util

def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

lemma ceilDiv_mul_ge (a : ℕ) {b : ℕ} (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  rw [Nat.mul_comm]
  have h := Nat.div_add_mod (a + b - 1) b
  have hlt : (a + b - 1) % b < b := Nat.mod_lt _ hb
  omega

lemma le_ceilDiv {k a b : ℕ} (hb : 0 < b) (h : k * b ≤ a) : k ≤ ceilDiv a b := by
  unfold ceilDiv
  apply (Nat.le_div_iff_mul_le hb).mpr
  omega

lemma ceilDiv_le_iff_le_mul (X b M : ℕ) (hb : 0 < b) :
    ceilDiv X b ≤ M ↔ X ≤ M * b := by
  unfold ceilDiv
  constructor
  · intro h
    have hdm := Nat.div_add_mod (X + b - 1) b
    have hmod := Nat.mod_lt (X + b - 1) hb
    have hbq : b * ((X + b - 1) / b) ≤ b * M := Nat.mul_le_mul_left b h
    have hbm : b * M = M * b := Nat.mul_comm _ _
    omega
  · intro h
    by_contra hgt
    push Not at hgt
    have hmul : b * (M + 1) ≤ b * ((X + b - 1) / b) := Nat.mul_le_mul_left b hgt
    have hself : b * ((X + b - 1) / b) ≤ X + b - 1 := by
      have h1 := Nat.div_mul_le_self (X + b - 1) b
      have h2 : (X + b - 1) / b * b = b * ((X + b - 1) / b) := Nat.mul_comm _ _
      omega
    have heq : b * (M + 1) = M * b + b := by ring
    omega

end Util
