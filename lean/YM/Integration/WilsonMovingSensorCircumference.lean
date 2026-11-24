import YM.Integration.WilsonMovingSensorHeat

/-! All sensors at least as large as the original logarithmic collar pay the
winding exponent, even when their circumference is chosen independently. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMovingSensorCircumference
open Function Filter Lattice RG Wilson Precision Laurent Bloch Next.Foundations WilsonCoeffUV.Bank.Ticket
open PhysicalNext.Repeat.Legato WilsonCoeffUV WilsonCoeffUV.Bank
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos WilsonCoeffUV.Winding
open WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Blue
open scoped Classical Topology BigOperators

open FullVolume WilsonCoeffUV.Winding
open scoped Classical BigOperators
open Laurent Bloch

variable {G:Gauge}

private theorem thin {B:ℝ} (positive:0<B) :
    ∀ᶠ x:ℝ in atTop,16*B*(1+Real.log x) ≤ x := by
  have small := Real.isLittleO_log_id_atTop.bound (c:=(32*B)⁻¹) (by positivity)
  filter_upwards [small,eventually_ge_atTop (max 0 (32*B))] with x hx large
  have xp:0≤x:=(le_max_left ..).trans large
  have lb:32*B≤x:=(le_max_right ..).trans large
  have cost:Real.log x≤(32*B)⁻¹*x := (le_abs_self _).trans (by simpa [Real.norm_eq_abs,abs_of_nonneg xp] using hx)
  have paid:=mul_le_mul_of_nonneg_left cost (show 0≤32*B by positivity)
  have exact:(32*B)*((32*B)⁻¹*x)=x:=by field_simp
  rw [exact] at paid
  nlinarith

private theorem dimensions (n:Side) : Real.log (Fintype.card (Co n (Hooks G)):ℝ) ≤
    4*Real.log (n.val:ℝ)+|Real.log (Fintype.card (Hooks G):ℝ)| := by
  have hp:0<(n.val:ℝ):=by exact_mod_cast n.property
  have num:(Fintype.card (Co n (Hooks G)):ℝ)=(n.val:ℝ)^4*(Fintype.card (Hooks G):ℝ):=by
    change (Fintype.card (Site n × Hooks G):ℝ)=_;rw [Fintype.card_prod,Lattice.site_card];push_cast;rfl
  rw [num]
  by_cases h:(Fintype.card (Hooks G):ℝ)=0
  · rw [h,mul_zero,Real.log_zero,abs_zero,add_zero];apply mul_nonneg (by norm_num) (Real.log_nonneg _)
    exact_mod_cast Nat.one_le_of_lt n.property
  · rw [Real.log_mul (by positivity) h, Real.log_pow];norm_num only [Nat.cast_ofNat];linarith only [le_abs_self (Real.log (Fintype.card (Hooks G):ℝ))]

/-- The width and coefficient are exactly those of the priced folded update.
Its original logarithmic lower side suffices simultaneously for every larger sensor. -/
theorem original (r H:ℕ) (U:Credit) : ∀ᶠ b:ℝ in atTop, ∀(n:Side),
    (Real.log b)^2≤(n.val:ℝ) → ∀ {s:ℝ}, 0<s →
    (perchA s r)⁻¹≤1+Real.log (Real.log b) →
    (H:ℝ)*Real.log b + (r+1:ℕ)*Real.log (Fintype.card (Co n (Hooks G)):ℝ) +
      Real.log (2*windPay s (U.buy (1+Real.log (Real.log b))) r) ≤ (perchA s r/16)*n.val := by
  obtain ⟨C,k,Cpos,wind⟩:=WilsonMovingSensorHeat.wind r U
  let dim:=|Real.log (Fintype.card (Hooks G):ℝ)|
  let A:=|Real.log (2*C)|
  let B:ℝ:=H+(r+1:ℕ)*(8+dim)+A+k+1
  have dp:0≤dim:=abs_nonneg _
  have ap:0≤A:=abs_nonneg _
  have bp:0<B := by dsimp only [B];positivity
  filter_upwards [Real.tendsto_log_atTop.eventually (thin bp),Real.tendsto_log_atTop.eventually_ge_atTop 1] with b bound large
  intro n collar s spos width
  let l:=Real.log b
  let z:=1+Real.log l
  let u:=Real.sqrt (n.val:ℝ)
  let t:=perchA s r
  have tp:0<t:=perch_pos spos r
  have l1:1≤l:=large
  have lp:0<l:=lt_of_lt_of_le zero_lt_one l1
  have z1:1≤z:=by dsimp only [z];linarith [Real.log_nonneg l1]
  have zl:z≤l:=by dsimp only [z];linarith [Real.log_le_sub_one_of_pos lp]
  have up:0≤u:=Real.sqrt_nonneg _
  have us:u^2=(n.val:ℝ):=Real.sq_sqrt (by positivity)
  have lu:l≤u:=by change l^2≤(n.val:ℝ) at collar;nlinarith
  have u1:1≤u:=l1.trans lu
  have g:=wind spos z1 width
  have gain: Real.log (2*windPay s (U.buy z) r) ≤ (A+k)*u := by
    have ex:=Real.log_le_log (by linarith only [g.1] : 0<2*windPay s (U.buy z) r)
      (mul_le_mul_of_nonneg_left g.2 (show (0:ℝ)≤2 by norm_num))
    have zp:0<z:=lt_of_lt_of_le zero_lt_one z1
    have expand : Real.log (2*(C*z^k)) = Real.log (2*C)+(k:ℝ)*Real.log z := by
      rw [←mul_assoc,Real.log_mul (by positivity) (by positivity),Real.log_pow]
    rw [expand] at ex
    have lg:Real.log z≤u:=(Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hA:Real.log (2*C)≤A*u:=(le_abs_self _).trans (le_mul_of_one_le_right ap u1)
    nlinarith [mul_le_mul_of_nonneg_left lg (Nat.cast_nonneg k)]
  have dim_price:Real.log (Fintype.card (Co n (Hooks G)):ℝ)≤(8+dim)*u:=by
    have dn:=dimensions (G:=G) n
    have ln:Real.log (n.val:ℝ)≤2*u:=by
      rw [←us,Real.log_pow];norm_num only [Nat.cast_ofNat];linarith [Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one u1)]
    have d0:=le_mul_of_one_le_right dp u1
    change _≤4*Real.log (n.val:ℝ)+dim at dn
    linarith
  have whole: (H:ℝ)*l + (r+1:ℕ)*Real.log (Fintype.card (Co n (Hooks G)):ℝ) + Real.log (2*windPay s (U.buy z) r)≤B*u:= by
    have first:=mul_le_mul_of_nonneg_left lu (Nat.cast_nonneg H)
    have angular:=mul_le_mul_of_nonneg_left dim_price (Nat.cast_nonneg (r+1))
    dsimp only [B];nlinarith
  have credit:16*B≤t*u := by
    calc 16*B = t*((16*B)*t⁻¹) := by field_simp
         _ ≤ t*(16*B*z) := by gcongr
         _ ≤ t*l := mul_le_mul_of_nonneg_left bound tp.le
         _ ≤ t*u := mul_le_mul_of_nonneg_left lu tp.le
  apply whole.trans
  nlinarith [mul_le_mul_of_nonneg_right credit up,congrArg (fun v:ℝ=>t*v) us]

end YM.Integration.WilsonMovingSensorCircumference
end
