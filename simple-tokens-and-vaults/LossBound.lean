import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Vault

/-!
# Round-trip loss under a price cap

A `deposit a → redeem shares` round-trip on `Vault` loses strictly
less than `ε · a` of the deposit, provided

* **price cap** (state property): `vaultTokenPrice s ≤ P`;
* **deposit floor** (deposit property, parameterized by `P` and `ε`):
  `(P + 1) / ε ≤ a`.

In exact arithmetic the round-trip is lossless. The two `floor`s in
the conversion formulas together waste at most `price + 1` assets,
*independent of `a`*. The price cap bounds that absolute slack by
`P + 1`; the deposit floor turns it into a sub-`ε` relative loss.
-/

namespace ERC4626

/-- Vault-token price `(B + vA) / (T + vT)` in `ℚ` — assets per vault
token, with the virtual offsets included. -/
noncomputable def vaultTokenPrice (s : State) : ℚ :=
  ((vaultAssets s + virtualAssets : ℕ) : ℚ)
    / ((s.vaultToken.totalSupply + virtualTokens : ℕ) : ℚ)

private lemma deposit_postState
    {s s' : State} {user : Addr} {a shares : ℕ}
    (hd : deposit s user a = some (s', shares)) :
    shares = vaultTokenFor s a ∧
    s'.vaultToken.totalSupply = s.vaultToken.totalSupply + shares ∧
    vaultAssets s' = vaultAssets s + a := by
  unfold deposit at hd
  split at hd
  · simp at hd
  case _ huv =>
    split at hd
    · simp at hd
    case _ assetToken' htransferFrom =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨hs', hk⟩ := hd
      subst hs'
      refine ⟨hk.symm, ?_, ?_⟩
      · show s.vaultToken.totalSupply + vaultTokenFor s a
              = s.vaultToken.totalSupply + shares
        rw [hk]
      · show assetToken'.balances vault = s.assetToken.balances vault + a
        exact ERC20.transferFrom_balances_receiver huv htransferFrom

private lemma redeem_postState
    {s s' : State} {user : Addr} {shares assets_back : ℕ}
    (hr : redeem s user shares = some (s', assets_back)) :
    assets_back = assetFor s shares := by
  unfold redeem at hr
  split at hr
  · simp at hr
  case _ vaultToken' _ =>
    split at hr
    · simp at hr
    case _ assetToken' _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      exact hr.2.symm

/-- **Round-trip loss bound.** Under a price cap `P` and a matched
deposit floor `(P + 1) / ε ≤ a`, the `deposit → redeem` round-trip
loses strictly less than `ε · a` of the deposit. -/
theorem deposit_then_redeem_loss
    {s s' s'' : State} {user : Addr} {a shares assets_back : ℕ} {P ε : ℚ}
    (h_ε_pos : 0 < ε)
    (h_price_cap : vaultTokenPrice s ≤ P)
    (h_a_min : (P + 1) / ε ≤ (a : ℚ))
    (hd : deposit s user a = some (s', shares))
    (hr : redeem s' user shares = some (s'', assets_back)) :
    (a : ℚ) - (assets_back : ℚ) < ε * (a : ℚ) := by
  obtain ⟨hsh, hTpost, hBpost⟩ := deposit_postState hd
  have ha_back : assets_back = assetFor s' shares := redeem_postState hr
  set T := s.vaultToken.totalSupply
  set B := vaultAssets s
  set vT := virtualTokens
  set vA := virtualAssets
  -- Positivity, in ℕ and ℚ.
  have hBvA_pos_ℕ : 0 < B + vA := by have := virtualAssets_pos; omega
  have hTvT_pos_ℕ : 0 < T + vT := by have := virtualTokens_pos; omega
  have hden_pos_ℕ : 0 < T + shares + vT := by omega
  have hTvT_pos_ℚ : (0 : ℚ) < ((T + vT : ℕ) : ℚ) := by exact_mod_cast hTvT_pos_ℕ
  have hden_pos_ℚ : (0 : ℚ) < ((T + shares + vT : ℕ) : ℚ) := by exact_mod_cast hden_pos_ℕ
  -- Strict floor bounds, expressed in terms of the scalar returns
  -- `shares` and `assets_back` (rather than `vaultTokenFor`/`assetFor`).
  have hk_lower_ℕ : a * (T + vT) < (shares + 1) * (B + vA) := by
    rw [hsh]
    show a * (T + vT) < (vaultTokenFor s a + 1) * (B + vA)
    unfold vaultTokenFor
    have h1 := Nat.div_add_mod (a * (T + vT)) (B + vA)
    have h2 : a * (T + vT) % (B + vA) < B + vA := Nat.mod_lt _ hBvA_pos_ℕ
    nlinarith [h1, h2]
  have ha'_lower_ℕ :
      shares * (B + a + vA) < (assets_back + 1) * (T + shares + vT) := by
    rw [ha_back]
    show shares * (B + a + vA) < (assetFor s' shares + 1) * (T + shares + vT)
    have hunfold : assetFor s' shares
                  = shares * (B + a + vA) / (T + shares + vT) := by
      unfold assetFor; rw [hBpost, hTpost]
    rw [hunfold]
    have h1 := Nat.div_add_mod (shares * (B + a + vA)) (T + shares + vT)
    have h2 : shares * (B + a + vA) % (T + shares + vT) < T + shares + vT :=
      Nat.mod_lt _ hden_pos_ℕ
    nlinarith [h1, h2]
  -- Cast to ℚ.
  have hk_lower_ℚ :
      ((a * (T + vT) : ℕ) : ℚ) < (((shares + 1) * (B + vA) : ℕ) : ℚ) := by
    exact_mod_cast hk_lower_ℕ
  have ha'_lower_ℚ :
      ((shares * (B + a + vA) : ℕ) : ℚ)
        < (((assets_back + 1) * (T + shares + vT) : ℕ) : ℚ) := by
    exact_mod_cast ha'_lower_ℕ
  -- Key cross-multiplied bound. The `a · shares` cross-terms cancel
  -- via `ring`, leaving the two floor slacks to sum.
  have hkey :
      ((a : ℚ) - (assets_back : ℚ)) * ((T + shares + vT : ℕ) : ℚ)
        < ((B + vA : ℕ) : ℚ) + ((T + shares + vT : ℕ) : ℚ) := by
    push_cast at hk_lower_ℚ ha'_lower_ℚ ⊢
    nlinarith [hk_lower_ℚ, ha'_lower_ℚ,
               sq_nonneg ((a : ℚ) - assets_back), sq_nonneg ((shares : ℚ))]
  -- Divide by `(T + shares + vT) > 0` to expose
  -- `a - assets_back < (B + vA) / (T + shares + vT) + 1`.
  have hpremul :
      ((a : ℚ) - assets_back - 1) * ((T + shares + vT : ℕ) : ℚ)
        < ((B + vA : ℕ) : ℚ) := by
    have : ((a : ℚ) - assets_back - 1) * ((T + shares + vT : ℕ) : ℚ)
            = ((a : ℚ) - assets_back) * ((T + shares + vT : ℕ) : ℚ)
                - ((T + shares + vT : ℕ) : ℚ) := by ring
    linarith [hkey]
  have hloss_quot :
      (a : ℚ) - (assets_back : ℚ) - 1
        < ((B + vA : ℕ) : ℚ) / ((T + shares + vT : ℕ) : ℚ) :=
    (lt_div_iff₀ hden_pos_ℚ).mpr hpremul
  -- Loosen the denominator: `shares ≥ 0` makes
  -- `T + shares + vT ≥ T + vT`.
  have hBvA_nn : (0 : ℚ) ≤ ((B + vA : ℕ) : ℚ) := by exact_mod_cast Nat.zero_le _
  have h_T_le : ((T + vT : ℕ) : ℚ) ≤ ((T + shares + vT : ℕ) : ℚ) := by
    push_cast
    linarith [show (0 : ℚ) ≤ (shares : ℚ) from by exact_mod_cast Nat.zero_le shares]
  have h_quot_le :
      ((B + vA : ℕ) : ℚ) / ((T + shares + vT : ℕ) : ℚ)
        ≤ ((B + vA : ℕ) : ℚ) / ((T + vT : ℕ) : ℚ) :=
    div_le_div_of_nonneg_left hBvA_nn hTvT_pos_ℚ h_T_le
  have h_price : ((B + vA : ℕ) : ℚ) / ((T + vT : ℕ) : ℚ) ≤ P := h_price_cap
  -- Side condition: `(P + 1) / ε ≤ a` and `ε > 0` give `P + 1 ≤ ε · a`.
  have h_a_min_mul : P + 1 ≤ ε * (a : ℚ) := by
    rw [mul_comm]; exact (div_le_iff₀ h_ε_pos).mp h_a_min
  -- Chain.
  linarith [hloss_quot, h_quot_le, h_price, h_a_min_mul]

end ERC4626
