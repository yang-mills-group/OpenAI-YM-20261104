import YM.Contacts.Trails.Fare
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
local notation "θ" => (u.A.B.a.S.scale)
local notation "B" => G.slopeConstant
local notation "μ" => (fun i=>Real.log (H i))
variable (h:G.Simple) (b:ℝ)
lemma blocks (he:i ≤ j): Real.log 3 * ((j-i:ℕ):ℝ) ≤ θ j-θ i:= by
   induction he with
   | refl=>simp
   | @step j he ih=> change i ≤ j at he; change _ * ((j+1-i:ℕ):ℝ) ≤ θ (j+1)-θ i; rw [Schedule.scale_succ, Nat.cast_sub (show i≤ j+1 from (by omega)),Nat.cast_add,Nat.cast_one]; rw [Nat.cast_sub he] at ih; -- rw cast tactic? 
                      linarith only [log_height u j,ih] -- fail
include h
lemma develops : Tendsto H atTop atTop:= tendsto_atTop_add_const_left _ _ ((u.A.B.a.S.divergent).const_mul_atTop (Gauge.slopeConstant_pos h))
lemma chop (b:ℝ): ∀ᶠ m:ℕ in atTop, b * Real.log (H m) ≤ H m:= by
   by_cases hb:0<b; swap; · exact Eventually.of_forall fun m=> le_trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) (Real.log_nonneg ((C).fits.delayed m).le)) (by linarith [(C).fits.delayed m]);
   filter_upwards [(develops u h).eventually (Real.isLittleO_log_id_atTop.def (show 0<b⁻¹ by positivity))] with m hm; have hx:= (C).fits.delayed m; simp only [Real.norm_eq_abs,id_eq,abs_of_pos (Real.log_pos hx),abs_of_pos (zero_lt_one.trans hx)] at hm; apply le_trans (mul_le_mul_of_nonneg_left hm hb.le); exact le_of_eq (by field_simp) -- use norm etc
-- all positions, not deck with exact layout cap.D
lemma space : ∀ᶠ i:ℕ in atTop, ∀ j:ℕ, i≤ j → θ j-θ i ≤ b*Real.log (H i) → window u i j:= by
   let T:=Real.log 3; have ht:0<T:=Real.log_pos (by norm_num); filter_upwards [chop u h (16*b/T)] with i hi j h hh; unfold window; unfold T at ht; have hx:= Fare.blocks u h; apply le_of_mul_le_mul_left («a»:=Real.log 3) _ ht; rw [div_mul_eq_mul_div] at hi; have hV:= (div_le_iff₀ ht).1 hi; push_cast; linarith only [hx,hV,hh]
variable {b}
open Contacts.Barrage.Reserve
abbrev μL (p:ℕ):= Real.log (H p)
-- mesh step itself relative to log hat (coupling). stronger than Recipe; consequence from Mirage. 
variable (p: Mirage u.M.K u.A.B.a u.M.O)
include p
lemma lowlength : ∀ᶠ i in atTop, Real.log ((u.A.B.a.S.block i).val:ℝ) ≤ Real.log (H i):= by
   filter_upwards [(develops u h).eventually (Contacts.Model.Province.Costing.longpole 1)] with i hi; let E:= coordinate u p h; let q:= E.harbor i; have hx:= Real.log_le_sub_one_of_pos (x:=((u.A.B.a.S.block i).val:ℝ)) (by positivity); exact hx.trans (sub_one_lt _|>.le.trans (q.trans ( (by change lush (H i) ≤ _; simpa only [one_mul] using hi)))) -- fix
-- quantitative mesh horizon selection.
lemma chooses (hb:0<b): ∀ᶠ i in atTop, ∃ j,i< j ∧ θ j-θ i ∈ Icc (b*μL u i) ((b+2)*μL u i) ∧ window u i j:= by
   obtain ⟨r,hr⟩:=eventually_atTop.mp (lowlength u h p); filter_upwards [(develops u h).eventually_ge_atTop 2, chop u h (B*b), space u h (b+2), eventually_ge_atTop r] with i hi hc hs hl
   let t:=H i; have ht:i=i:=rfl; have ht':1<t:= one_lt_two.trans_le hi; let z:=μL u i;
   let P(j): Prop:= i≤ j ∧ θ i+b*z ≤ θ j; have hp:∃ j,P j:= ( ((S).divergent.eventually_ge_atTop _).and (eventually_ge_atTop i)).exists.imp fun i ⟨h,h'⟩=> ⟨h',h⟩
   let j:=Nat.find hp; obtain ⟨HE,hu⟩:= Nat.find_spec hp; have he:P j:=⟨HE,hu⟩; have hh:0<z:= Real.log_pos ht'; have hj:i<j:= lt_of_le_of_ne he.1 (fun h=> by have h' : θ i+b*z ≤ θ i:= le_trans he.2 (le_of_eq (congr_arg _ h.symm)); linarith only [mul_pos hb hh,h']);
   let s:= j-1; have hv:s+1=j:=(by unfold s; omega); have hs':θ s< θ i+b*z:= lt_of_not_ge fun x=> (Nat.find_min hp (show s<j by omega) ⟨by omega,x⟩).elim; have hZ: (H s) ≤ 2*t:= by
      let x:=G.slopeConstant; have hc₂:= mul_le_mul_of_nonneg_left hs'.le (Gauge.slopeConstant_pos h).le; unfold t Calendar.hatBeta; unfold Calendar.hatBeta at hc; change _+_*(θ s) ≤ 2*((C).clock.bar+ x *(θ i)); change x * b * z ≤ (C).clock.bar+x * θ i at hc; change x * θ s ≤ x *(θ i+b*z) at hc₂; change (C).clock.bar+ x*θ s ≤ _; nlinarith only [hc₂,hc]
   have hℓ: Real.log ((S).block s).val ≤2*z:= by
       apply (hr s (by omega)).trans; apply (Real.log_le_log (zero_lt_one.trans ((C).fits.delayed _)) hZ).trans; rw [Real.log_mul (by norm_num) (zero_lt_one.trans ht').ne']; linarith only [Real.log_le_log (x:=2) (by norm_num) hi] -- binder
   have hA: θ j-θ i ≤ (b+2)*z:= by rw [← hv,Schedule.scale_succ]; linarith only [hs',hℓ]
   exact ⟨j, hj,⟨by linarith only [he.2],hA⟩, hs j hj.le hA⟩
end Fare
end YM.PhysicalNext.Repeat.Legato.Euro
