import YM.Integration.WilsonIndependentConditionedBankApplied

/-! The paid low term enters the two linear thermal remainders at the same dose. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonIndependentConditionedBankStableCost
open WilsonIndependentConditionedBankReport (debit)

private theorem power (δ:ℝ)(positive:0<δ)(small:δ ≤ 1)(n N:ℕ)(η:ℝ)
    (room:(n:ℝ)+η ≤ N):
    (δ^n)⁻¹*δ^(-η) ≤ (δ^N)⁻¹:=by
  rw [←Real.rpow_natCast δ n,←Real.rpow_natCast δ N,
      ←Real.rpow_neg positive.le,←Real.rpow_neg positive.le,←Real.rpow_add positive]
  exact Real.rpow_le_rpow_of_exponent_ge positive small (by linarith)

def gross (q:ℕ)(S I B₀ B₁ V:ℝ):ℝ:=
  max ((q+1:ℕ)*S*I) (2*(q+1:ℕ)*S*(B₀+B₁)+3*V*B₀*B₁)

theorem original (δ g ξ η:ℝ)(q h₀ h₁:ℕ)(S I B₀ B₁ V:ℝ)(s b₀ b₁ v:ℝ)
    (positive:0<δ)(small:δ ≤ 1)(gain:0 ≤ ξ)(half:2*η ≤ 1)
    (s0:0 ≤ s)(I0:0 ≤ I)(S0:0 ≤ S)(B0:0 ≤ B₀)(B1:0 ≤ B₁)(V0:0 ≤ V)
    (low:s ≤ S*δ^ξ)(a₀:|b₀| ≤ B₀*((δ^h₀)⁻¹*δ^(-η)))
    (a₁:|b₁| ≤ B₁*((δ^h₁)⁻¹*δ^(-η)))(price:|v| ≤ V*(δ^(h₀+h₁))⁻¹):
    debit q g s I b₀ b₁ v ≤ gross q S I B₀ B₁ V*
      (δ^ξ+|g|^(q+1)*(δ^(2*(h₀+h₁)+1))⁻¹):=by
  let H:=h₀+h₁
  let j:=2*H+1
  have e0:0 ≤ δ^ξ:=Real.rpow_nonneg positive.le _
  have e1:δ^ξ ≤ 1:=Real.rpow_le_one positive.le small gain
  have sS:s ≤ S:=low.trans (mul_le_of_le_one_right S0 e1)
  have h0:(h₀:ℝ)+η ≤ j:=by dsimp [j,H];push_cast;linarith
  have h1:(h₁:ℝ)+η ≤ j:=by dsimp [j,H];push_cast;linarith
  have t0:|b₀| ≤ B₀*(δ^j)⁻¹:=a₀.trans <| mul_le_mul_of_nonneg_left
    (power δ positive small h₀ j η h0) B0
  have t1:|b₁| ≤ B₁*(δ^j)⁻¹:=a₁.trans <| mul_le_mul_of_nonneg_left
    (power δ positive small h₁ j η h1) B1
  have together:b₀+b₁ ≤ (B₀+B₁)*(δ^j)⁻¹:=by
    rw [add_mul];exact add_le_add ((le_abs_self _).trans t0) ((le_abs_self _).trans t1)
  have mid:s*(b₀+b₁) ≤ S*((B₀+B₁)*(δ^j)⁻¹):=
    (mul_le_mul_of_nonneg_left together s0).trans
      (mul_le_mul_of_nonneg_right sS (by positivity))
  have combine:(δ^(-η))*(δ^(-η))=δ^(-(2*η)):=by rw [←Real.rpow_add positive];congr 1;ring
  have Hroom:((2*H:ℕ):ℝ)+2*η ≤ j:=by dsimp [j]; push_cast;linarith
  have Bpow:(V*(δ^H)⁻¹)*(B₀*((δ^h₀)⁻¹*δ^(-η)))*(B₁*((δ^h₁)⁻¹*δ^(-η)))
      =V*B₀*B₁*((δ^(2*H))⁻¹*δ^(-(2*η))):=by
    rw [←combine];simp only [two_mul,H,pow_add,mul_inv_rev];ring
  have full:|v| *b₀*b₁  ≤  V*B₀*B₁*(δ^j)⁻¹:=calc
    |v| *b₀*b₁  ≤  |v| * |b₀| * |b₁| :=by simpa only [abs_mul,abs_abs] using le_abs_self (|v| *b₀*b₁)
    _  ≤  _ :=mul_le_mul (mul_le_mul price a₀ (abs_nonneg _) (by positivity)) a₁
      (abs_nonneg _) (by positivity)
    _ = _ :=Bpow
    _  ≤  _ :=mul_le_mul_of_nonneg_left (power δ positive small (2*H) j (2*η) Hroom) (by positivity)
  have single:s*I ≤ (S*δ^ξ)*I:=mul_le_mul_of_nonneg_right low I0
  calc
    debit q g s I b₀ b₁ v = (q+1:ℕ)*(s*I) +
        2*(q+1:ℕ)* |g|^(q+1)*(s*(b₀+b₁)) + 3* |g|^(q+1)*(|v| *b₀*b₁):=by unfold debit;ring
    _  ≤  (q+1:ℕ)*((S*δ^ξ)*I) +
        2*(q+1:ℕ)* |g|^(q+1)*(S*((B₀+B₁)*(δ^j)⁻¹)) +
        3* |g|^(q+1)*(V*B₀*B₁*(δ^j)⁻¹):=by
          gcongr
    _ = (q+1:ℕ)*S*I*δ^ξ +
        (2*(q+1:ℕ)*S*(B₀+B₁)+3*V*B₀*B₁)*(|g|^(q+1)*(δ^j)⁻¹):=by ring
    _  ≤  gross q S I B₀ B₁ V*δ^ξ +
        gross q S I B₀ B₁ V*(|g|^(q+1)*(δ^j)⁻¹):=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) e0)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
    _ = _:=by rw [mul_add]

end YM.Integration.WilsonIndependentConditionedBankStableCost
