import YM.Integration.WilsonSeparatedPrefixKineticEdge

/-! A single fixed polynomial covers every numerical chart expense on the collar,
including the number of dated hearings. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixKineticCash
open WilsonCoeffUV.Bank WilsonSeparatedPrefixKineticEdge

def fee (n:ℕ):ℝ:=(n+2:ℝ)+32*(n+1:ℝ)*2^n

lemma quote (n:ℕ){M t:ℝ}(M1:1 ≤ M)(t0:0 ≤ t)(t1:t ≤ 1):
    fare n M (t^(n+2)) t ≤ t^(n+2)*fee n*M^(n+4):=by
  have m0:0 ≤ M:=zero_le_one.trans M1
  have m3:1 ≤ M^3:=one_le_pow₀ M1
  have times:t^(n+2) ≤ t^(n+1):=pow_le_pow_of_le_one t0 t1 (by omega)
  have low:M ≤ M^3:=by simpa only [pow_one] using pow_le_pow_right₀ M1 (by decide:1 ≤ 3)
  have gross:optical n M (t^(n+2)) t ≤ 32*t^(n+1)*M^3:=by
    have a:t^(n+2) ≤ t^(n+1)*M^3:=times.trans (le_mul_of_one_le_right (pow_nonneg t0 _) m3)
    have b:t^(n+1)*M ≤ t^(n+1)*M^3:=mul_le_mul_of_nonneg_left low (pow_nonneg t0 _)
    unfold optical;nlinarith only [a,b]
  have first:M^(n+2) ≤ M^(n+4):=pow_le_pow_right₀ M1 (by omega)
  have second:M^4 ≤ M^(n+4):=pow_le_pow_right₀ M1 (by omega)
  calc
    _ ≤ t*(t^(n+1)*((n:ℝ)+2)*M^(n+1)*M+
        (32*t^(n+1)*M^3)*((n:ℝ)+1)*2^n*M):=by unfold fare;gcongr
    _=t^(n+2)*((n:ℝ)+2)*M^(n+2)+t^(n+2)*(32*((n:ℝ)+1)*2^n)*M^4:=by ring
    _ ≤ t^(n+2)*((n:ℝ)+2)*M^(n+4)+t^(n+2)*(32*((n:ℝ)+1)*2^n)*M^(n+4):=by gcongr
    _=_:=by unfold fee;ring

theorem shelf (n e:ℕ)(C:Credit){B:ℝ}(B1:1 ≤ B):∃S:Credit,∀z a days,1 ≤ z→1 ≤ a→a ≤ B*z→0 ≤ days→days ≤ B*z→
    let M:=(e+2:ℝ)*C.buy a
    1 ≤ M ∧ 4*M ≤ S.buy z ∧ days*2^(n+2)*fee n*M^(n+4) ≤ S.buy z:=by
  let b:=(e+2:ℝ)*C.x*B^C.d
  let D:=C.d*(n+4)+1
  let price:=max 1 (max (4*b) (B*(2:ℝ)^(n+2)*fee n*b^(n+4)))
  refine ⟨⟨D,price,le_max_left ..⟩,?_⟩
  intro z a days z1 a1 aa d0 dd M
  have B0:0 ≤ B:=zero_le_one.trans B1
  have z0:0 ≤ z:=zero_le_one.trans z1
  have b0:0 ≤ b:=by dsimp [b];positivity [C.good]
  have f0:0 ≤ fee n:=by unfold fee;positivity
  have M1:1 ≤ M:=by dsimp [M];exact one_le_mul_of_one_le_of_one_le (by linarith [Nat.cast_nonneg (α:=ℝ) e]) (C.purchase a1)
  have wage:M ≤ b*z^C.d:=by
    calc
      _ ≤ ((e:ℝ)+2)*C.buy (B*z):=mul_le_mul_of_nonneg_left (C.elder a1 aa) (by positivity)
      _ = _:=by dsimp [b,Credit.buy];rw [mul_pow];ring
  have grade:C.d ≤ D:=by dsimp [D];nlinarith
  refine ⟨M1,?_,?_⟩
  · have c:4*b ≤ price:=(le_max_left ..).trans (le_max_right ..)
    calc
      _ ≤ 4*(b*z^C.d):=mul_le_mul_of_nonneg_left wage (by norm_num)
      _ ≤ price*z^D:=by rw [←mul_assoc];gcongr
  · have c:B*(2:ℝ)^(n+2)*fee n*b^(n+4) ≤ price:=(le_max_right ..).trans (le_max_right ..)
    calc
      _ ≤ (B*z)*(2:ℝ)^(n+2)*fee n*(b*z^C.d)^(n+4):=by gcongr
      _=(B*(2:ℝ)^(n+2)*fee n*b^(n+4))*z^D:=by dsimp [D];rw [mul_pow,pow_succ (z) (C.d*(n+4)),pow_mul];ring
      _ ≤ price*z^D:=mul_le_mul_of_nonneg_right c (pow_nonneg z0 _)

end YM.Integration.WilsonSeparatedPrefixKineticCash
end
