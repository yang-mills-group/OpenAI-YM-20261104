import YM.MatchingLedger.Compass.Deck

/-! # Order-two reset *precise* on this convention.

Notice the log positions monitor. Present absolute retick and coupling powers on actual
`A.S` all steps, representative-independent. Spacing MS-bar pole conventions NOT being
absorbed in this internal formal `α`. This is real germs only. Rate constants can blow with
stage premises. Does not identify variation of C across realizations of ANY of these two steps,
just issue adjacent reset. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace YM.MatchingLedger.Compass.Income
open Function Filter Set MeasureTheory Precision RG Tree Wilson Lattice Work Exterior Pressure
open Sail Weather OPE Pins Home Spring.Fares Pert.Asymptotics
open scoped ContDiff Topology BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge} (C:Family G)(h:C.Makes)(hG:G.Simple)
section numeric
variable {s g₀ g₁ b₀ b₁ a ε δ:ℝ}
/-- polynomial tangent identity. -/
def clockwork (α g : ℝ) := g-α/2*g^3
lemma offbeat {α g:ℝ}: clockwork α (-g)= -clockwork α g:= by unfold clockwork; ring
private lemma roots {x y:ℝ}(hy:0<y)(hx:|x|≤ 1/2)(hh:(1+x)*y^2=1) : |y - (1-x/2)| ≤ 5* |x| *|x|:=by
   have hl : 1/2 ≤ 1+x:=by linarith only [(abs_le.mp hx).1]
   have hk : y^2 ≤2:= by nlinarith only [mul_le_mul_of_nonneg_right hl (sq_nonneg y),hh]
   have hY:y≤2:=by nlinarith only [hy,hk]
   have hp₀ : 1≤y+1:= le_add_of_nonneg_left hy.le
   have hp:y-1=-x*(y^2/(y+1)):=by field_simp; linarith only [hh]
   have hq : |y-1|≤2*|x|:=by
      rw [hp,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0≤y^2/(y+1)),mul_comm 2]
      exact mul_le_mul_of_nonneg_left ((div_le_self (sq_nonneg y) hp₀).trans hk) (abs_nonneg _)
   rw [show y-(1-x/2)=-(y-1)*x*((2*y+1)/(2*(y+1))) by field_simp; nlinarith only [hh],abs_mul,abs_mul,abs_neg,abs_of_pos (by positivity : 0 < (2*y+1)/(2*(y+1)))]
   have hv: (2*y+1)/(2*(y+1))≤5/2:= (div_le_iff₀ (by positivity)).mpr (by linarith only [hy]);
   exact (mul_le_mul (mul_le_mul_of_nonneg_right hq (abs_nonneg x)) hv (by positivity) (by positivity)).trans_eq (by ring)
def payday (u δ g : ℝ) := 5*g^5*u^2+δ*g^3/2
lemma counters (h : |b₀-b₁-a| ≤ δ)(hξ: |b₀-b₁|≤ ε)(hN : b₀*g₀^2=1)(hk:b₁*g₁^2=1)(hs:0<g₀)(ht:0<g₁)(ht':g₁≤ s)(hZ: ε*s^2 ≤ 1/2) :
    ‖g₀-clockwork a g₁‖≤ payday ε δ s:=by
  let x:=(b₀-b₁)*g₁^2; let y:=g₀/g₁; have hu:0<s:= ht.trans_le ht'; have hv:0≤ε:= (abs_nonneg _).trans hξ
  have hp:0≤δ:= (abs_nonneg _).trans h; have he: (1+x)* y^2=1:=by unfold x y; field_simp; rw [show (1+(b₀-b₁)*g₁^2)= b₀*g₁^2 from (by linarith only [hk])]; nlinarith only [mul_le_mul_of_nonneg_right hN.le (sq_nonneg g₁), mul_le_mul_of_nonneg_right hN.ge (sq_nonneg g₁)]
  have hz: |x| ≤ ε * s^2:=by unfold x; rw [abs_mul,abs_of_nonneg (sq_nonneg g₁)]; exact mul_le_mul hξ (pow_le_pow_left₀ ht.le ht' _) (sq_nonneg _) hv
  have hx : |g₀-g₁*(1-x/2)|≤5*s^5*ε^2:=by
    rw [show g₀-g₁*(1-x/2)=g₁*(y-(1-x/2)) by unfold y; field_simp, abs_mul, abs_of_pos ht]
    exact (mul_le_mul ht' ((roots (x:=x) (by unfold y; positivity : 0<y) (hz.trans hZ) he).trans (mul_le_mul (mul_le_mul_of_nonneg_left hz (by norm_num : (0:ℝ) ≤ 5)) hz (abs_nonneg _) (by positivity))) (abs_nonneg _) hu.le).trans_eq (by ring)
  apply le_trans (norm_sub_le_norm_sub_add_norm_sub g₀ (g₁*(1-x/2)) (clockwork a g₁)) _
  apply add_le_add hx; rw [show g₁*(1-x/2)-clockwork a g₁= -(b₀-b₁-a)*(g₁^3/2) from by unfold clockwork x; ring, Real.norm_eq_abs,abs_mul,abs_neg,abs_of_nonneg (by positivity : 0 ≤ g₁^3/2)]
  exact (mul_le_mul h (div_le_div_of_nonneg_right (pow_le_pow_left₀ ht.le ht' _) zero_le_two) (by positivity) hp).trans_eq (by ring)
end numeric
local notation "c_" => G.slopeConstant
local notation "ρ" => C.path.levels
local notation "g_"=>regulatorRun C

def latency (i:ℕ) := (1+G.slopeConstant)*(C.S.block i).val +1
variable {T:Harvest C.path.levels} (X:Profile C T)
include X hG
lemma forward {m n:ℕ}(hm:m<n): |T.alpha n m|+1 ≤ latency C m:=by
  let V:= C.path.levels.clock; let W:= V.params (m+1); let j:= V.J (m+1)
  let u:= T.alpha n m; let L:ℝ:= (C.S.block m).val; let w:=Real.log L
  have hL:(3:ℝ) ≤ L:= by unfold L; exact_mod_cast C.S.block_large m
  have hv:= X.drift n m hm; have hz:1 ≤ (j:ℝ):=by exact_mod_cast (le_trans (by decide:1≤4) (V.adm (m+1)))
  have ht:0<w:= Real.log_pos (by linarith); have hh: W.drift≤ w:= (div_le_one ht).mp (le_trans (show W.drift/w ≤ ((j:ℝ)^2)⁻¹ from (ρ).fits.driftSmall m) (inv_le_one_of_one_le₀ (one_le_pow₀ hz)))
  have he: w ≤ L:= Real.log_le_self (by linarith only [hL]); have hc:0<c_:= Gauge.slopeConstant_pos hG
  have h : |u|≤ |u+c_*w|+c_*w:= by
    calc
      _ = |u+c_*w-c_*w| := by rw [add_sub_cancel_right]
      _ ≤ _ := (abs_sub ..).trans_eq (by rw [abs_of_pos (mul_pos hc ht)])
  unfold latency; nlinarith only [hv,hh,he,h,mul_le_mul_of_nonneg_left he hc.le] -- normalization

local notation "∂i" => allot
lemma beats {m n:ℕ}(hm:m<n)(p:ℕ) :
    |C.path.β n p m-C.path.β n p (m+1)-T.alpha n m| ≤ allot (ice C m) ∧
         |C.path.β n p m-C.path.β n p (m+1)| ≤ latency C m:=by
   let e:=allot (ice C m); have he : _ := X.turn n m p hm; have ht:= forward C hG X hm; let v:= C.path.β n p m - C.path.β n p (m+1); let u:= T.alpha n m
   have hi: |v-u|≤e:= he.trans (Real.rpow_le_rpow_of_nonpos (ice_pos C m) (rises C hG m) (by norm_num : (-(8/100):ℝ) ≤0))
   have hs:e≤1:= Real.rpow_le_one_of_one_le_of_nonpos (ice_strict C m).le (by norm_num)
   exact ⟨hi,abs_le.mpr (by rcases abs_le.mp hi with ⟨hu,hv⟩; constructor <;> linarith only [hu,hv, hs, ht,le_abs_self u,neg_le_abs u])⟩ -- edit
variable (P:Pins.Prepared (Home.invite G) C.path.levels)
include P
omit X in
lemma finance (p:ℝ) (hp:p<3+ 4/25) : ∀ᶠ m:ℕ in atTop, latency C m*(2*ħ C m)^2 ≤ 1/2 ∧ payday (latency C m) (allot (ice C m)) (2*ħ C m) ≤ ħ C m ^ p := by
  let w:= latency C; let t(m:ℕ):=2*ħ C m
  have he:Fare C 0 w:= (Fare.times C (Fare.fixed C hG _) (length_cost C hG P)).add (Fare.fixed C hG _) (age C hG) -- parse
  have hT:Fare C (-(1/2)) (ħ C):= by simpa only [Real.rpow_one, neg_div] using (fair C hG 1).pays (age C hG)
  have hu:Fare C (-(1/2)) t:=by simpa only [zero_add] using! ((Fare.fixed C hG 2).mul hT)
  have ht:= (he.mul (hu.pow 2 (age C hG))).tends (by norm_num) (age C hG)
  have h₁:= ((Fare.fixed C hG (5:ℝ)).mul (hu.pow 5 (age C hG))).mul (he.pow 2 (age C hG))
  have h₂:Fare C _ (fun x:ℕ=> allot (ice C x)*t x^3/2):= ((betaLedger C hG (-(8/100):ℝ)).pays (age C hG) |>.mul (hu.pow 3 (age C hG))|>.mul (Fare.fixed C hG 2⁻¹)).congr (Eventually.of_forall (fun m=> (div_eq_mul_inv ..).symm)) -- adjust
  have heq: Fare C _ (fun m=> payday (w m) (allot (ice C m)) (t m)):= h₁.addMax h₂ (age C hG)
  filter_upwards [ht.eventually_le_const (by norm_num : (0:ℝ)< 1/2), spends C hG heq (p:=p) (by rw [max_lt_iff]; push_cast; constructor<;>linarith only [hp])] with i hi hQ
  exact ⟨hi,(le_abs_self _).trans hQ⟩
include h
lemma rebudget (p:ℝ)(hp:p<3+4/25): ∀ᶠ i:ℕ in atTop,∀ n q:ℕ,i<n→ let u:= (g_) n q i;let v:=(g_) n q (i+1); let d:=T.alpha n i; ‖u-clockwork d v‖ ≤ ħ C i ^ p ∧ ‖v-clockwork (-d) u‖ ≤ ħ C i ^ p:=by
   filter_upwards [finance C hG P p hp] with i ⟨he,hQ⟩ n q hi u v d
   let D:=ice C i; let B:= C.path.β n q i; let K:= C.path.β n q (i+1); let y:=2*ħ C i; let e:=latency C i
   have hD:0<D:= ice_pos C i
   obtain ⟨hU,hV⟩:=beats C hG X hi q
   have hu: u≤ y:= (into_band C h hi.le q).2; have hv : v ≤ y:= (into_band C h hi q).2.trans (mul_le_mul_of_nonneg_left (show ħ C (i+1)≤ħ C i from inv_anti₀ (Real.sqrt_pos.mpr hD) (Real.sqrt_le_sqrt (rises C hG i))) zero_le_two)
   have hz: |K-B-(-d)|≤allot D:= by rw [show K-B- - d= -(B-K-d) by ring,abs_neg]; exact hU
   exact ⟨(counters hU hV (epoch C h hi.le q) (epoch C h hi q) (runs_pos C h hi.le q) (runs_pos C h hi q) hv he).trans hQ, (counters hz ((abs_sub_comm K B).trans_le hV) (epoch C h hi q) (epoch C h hi.le q) (runs_pos C h hi q) (runs_pos C h hi.le q) hu he).trans hQ⟩
end YM.MatchingLedger.Compass.Income
