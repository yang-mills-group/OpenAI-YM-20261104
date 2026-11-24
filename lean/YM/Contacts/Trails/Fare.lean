import YM.Contacts.Trails.Weather
/-! # Weighted amplification. Does not change direction test order.
     Along actual reopened histories. Early polymer leases exactly the token.
 -/
noncomputable section
set_option autoImplicit false
namespace YM.PhysicalNext.Repeat.Legato.Euro
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Concert ThroughLaunch Pressure Testing Contacts.Allium Contacts.Allium.Grant
open Contacts.Bounty.Trophy.Lore Contacts.Bounty.Trophy Contacts.Revest Contacts.Revest.Outlay
open Push.SectorMeasure Terrain ConnectedActivityE6 Blaze Contacts.Milling Sequin
variable {X:Gauge} (u: Passage G){m n i j x k N r:ℕ}{t z a:ℝ}
local notation "C" => u.A.B.a
local notation "S" => u.A.B.a.S
local notation "W" => u.A.B.a.clock
local notation "U" => u.T
local notation "H" => u.A.B.a.clock.hatBeta
namespace Fare
abbrev floor₀ :ℝ := Real.exp (-(Real.log 3)/2)
def carry :ℝ:= (1-floor₀)⁻¹
lemma basics : 0<floor₀ ∧ floor₀<1 ∧ 1≤carry ∧ 1+floor₀*carry = carry:= by
   have hv:floor₀<1:=Real.exp_lt_one_iff.mpr (by linarith only [Real.log_pos (by norm_num : (1:ℝ)<3)])
   have hh: 0<floor₀:= Real.exp_pos _; have he:0 < 1-floor₀:= sub_pos.mpr hv; refine ⟨hh,hv,?_,?_⟩; · exact one_le_inv₀ he|>.2 (by linarith)
   unfold carry; field_simp; ring -- verify
abbrev wheel (i:ℕ):ℝ:=march (u.L.L ((C).clock.J (i+1)))
lemma wheelH : 0<wheel u i ∧ wheel u i ≤ floor₀:= by
   unfold wheel; rw [show march _= _ from marchD u i]; exact ⟨Real.exp_pos _,Real.exp_le_exp.mpr (by linarith only [log_height u i])⟩
abbrev tune (u: Passage G)(a:ℝ)(i:ℕ):ℝ:= (u.A.B.a.clock.hatBeta i) ^ (-a)
def ticket (a:ℝ)(i j:ℕ):= carry*tune u a i+ Real.exp (-((u.A.B.a.S.scale j)-(u.A.B.a.S.scale i))/2)* (u.A.B.a.clock.allowance j)
lemma era (i:ℕ):0<tune u a i:=Real.rpow_pos_of_pos (zero_lt_one.trans ((C).fits.delayed _)) _
lemma income : 0 ≤ ticket u a i j:= add_nonneg (mul_nonneg (zero_le_one.trans basics.2.2.1) (era ..|>.le)) (mul_nonneg (Real.exp_pos _).le (cash u _).1.le)
local notation "Φ" => ticket u a
local notation "ℓ" => (u.A.B.a.S.scale)
local notation "Q" => tune u a
variable (hG:G.Simple)(ha: 0 ≤ a)
include hG ha
lemma shift (hb:t ≤ Φ (i+1) j) : retreat u.A i a t ≤ Φ i j:= by
   have hh: Q (i+1) ≤ Q i:= Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans ((C).fits.delayed _)) ((monotone_hat u hG) (Nat.le_succ _)) (neg_nonpos.mpr ha)
   let τ:=wheel u i; let y(i):= Real.exp (-(ℓ j-ℓ i)/2); have ht:τ * y (i+1) =y i:= by
       rw [show τ= _ from marchD u i,←Real.exp_add]; unfold y; rw [Schedule.scale_succ]; congr 1; ring -- may y under rw order reverse
   let m:= (C).clock.allowance j; change Q i+τ*t ≤ _; refine (add_le_add_right (mul_le_mul_of_nonneg_left hb (wheelH u).1.le) (Q i)).trans ?_; change Q i+τ*(carry*Q _+y _*m)≤ carry*Q i+ _; rw [mul_add,← mul_assoc τ (y (i+1)),ht];
   have hc:= mul_le_mul_of_nonneg_left hh (zero_le_one.trans basics.2.2.1); have hq:= mul_le_mul (wheelH u (i:=i)).2 hc (mul_nonneg (zero_le_one.trans basics.2.2.1) (era ..|>.le)) basics.1.le; change Q i+ (_+ y i*m) ≤ _+ y i*m; rw [←add_assoc]; apply add_le_add_left; linarith only [hq,show (1+floor₀*carry)*(Q i)=carry*Q i from congr_arg (· * (Q i)) basics.2.2.2] -- τ reducible
lemma unfair (hi:i ≤ j): Euro.grow u a i j ≤ Φ i j:= by
   induction hi using Nat.decreasingInduction with
   | self=>
     rw [Euro.self u _ j,ticket,sub_self]; simp [mul_nonneg (zero_le_one.trans basics.2.2.1) ((era u j (a:=a)).le)]
   | of_succ i hi ih=> rw [Euro.base u j a i hi]; exact (min_le_right ..).trans (shift u hG ha ih)
lemma column (hi:i < j): retreat u.A i a (Euro.grow u a (i+1) j) ≤ Φ i j:= shift u hG ha (unfair u hG ha hi)
lemma paid (h: 2*a*Real.log (H i) ≤ ℓ j-ℓ i) : Φ i j ≤ (1+carry)*tune u a i:= by
    let f:= Real.exp (-(ℓ j-ℓ i)/2); have hf:f≤Q i:= by unfold tune; rw [Real.rpow_def_of_pos (zero_lt_one.trans ((C).fits.delayed _))]; exact Real.exp_le_exp.mpr (by linarith)
    have he:= mul_le_of_le_one_right ((show 0<f from Real.exp_pos _).le) (cash u j).2; rw [ticket]; change _+ f*_≤_; rw [add_mul,one_mul,add_comm (Q i)]; exact add_le_add_right (le_trans he hf) _ -- inference
end Fare
end YM.PhysicalNext.Repeat.Legato.Euro
