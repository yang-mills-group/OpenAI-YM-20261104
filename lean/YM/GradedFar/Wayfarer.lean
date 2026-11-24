import YM.GradedFar.Foresight
/-!
# Step-by-step traveling price

Paths may be extended to full cap forecast. First normalize engineering weights on rows.
Then account for growth of updated normalization, even off-grade, through telescoping. Uses
actual (G.1) compact statements as inputs. Doesn't assume any receding version.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.GradedFar.Neighbor
open Function Filter Set PowerSeries
open Extraction Table Spec OPE.Orbits Climb Trace.Pilot PhysMS
open FVA2 XSpace XSpace.Normalize MS MS.Native MS.Land MS.Book MS.Book.Program MS.Book.Convolve MS.Fleet MS.Tide
open FVA2.Scale FVA2.Dframe FVA2.O.Score FVA2.Register FVA2.GradedFar YM.FVA2.GradedFar.Cart
open scoped Topology BigOperators Classical
variable {G:Gauge}{C:Family G}{fo:Extraction.Order}{S:Table C.book}
   (P:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ) (h p:ℕ)
local notation "g"=> strength G
local notation "γ" => fun (T:ℝ)=> -Real.log T
local notation "ϕ" => GroupS.ψ Z.criterion M ν
local notation "Kt" => GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "D'" => stretching G h
local notation "op" => stamp G h
local notation "U'" => fun (r s:ℝ)=> LinearEquiv.toLinearMap (relative P r s h)
local notation "W" => Operation G h

lemma opstamp (A: Sec G h→ₗ[ℂ] Sec G h) : opField A= ‖op A‖:= rfl
lemma repeated (r:ℝ) : U' r r=1:= by ext1 x; exact (assign P r h).symm_apply_apply _
lemma fold (r s t:ℝ) : U' r s * U' s t = U' r t:= by
 ext1 x; change (assign P r h).symm (assign P s h (relative P s t h x))=_; rw [atHome]; rfl

-- Series normalization. Only a variable route argument; instantiate P from prescription later.
def ℳ (h:ℕ)(r T:ℝ): Operation G h := stretching G h (Real.log T) * (stamp G h ((relative P r (r*T) h).toLinearMap))
lemma setting (r T:ℝ) : op (U' r (r*T)) = D' (γ T) * ℳ P h r T:= by
 rw [ℳ,← mul_assoc,stretch_mul,neg_add_cancel,flat,one_mul]
lemma stamp_step {r T x:ℝ}(hT:1 ≤ T)(hx:x∈ Icc (1:ℝ) 2):
    ℳ P h r (T*x) = D' (Real.log x) * ℳ P h r T * op (U' (r*T) (r*T*x)):=by
 rw [ℳ,mul_comm T,Real.log_mul (zero_lt_one.trans_le hx.1).ne' (zero_lt_one.trans_le hT).ne',mul_comm x T,← mul_assoc r T x,
    ℳ, ← stretch_mul]; have hA:=fold P h r (r*T) (r*T*x); dsimp only at hA; rw [← hA, price]; dsimp only; simp only [mul_assoc]
lemma road_cap {x:ℝ}(hx: x∈ Icc (1:ℝ) 2) : x∈ Icc (1/2:ℝ) 2:= ⟨le_trans (by norm_num) hx.1,hx.2⟩

variable {t:ℝ→ℝ} {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "B'" => fare Z M ν h p
local notation "J'" => ticker Z M ν p
local notation "v'" => fun r=> (t r:ℂ)

include H in
lemma cost_bill (h0:Stamp P Z M ν t h 1): ∀ᶠ r in trail,∀ x,x∈ Icc (1:ℝ) 2→
    ‖op (U' r (r*x))‖ ≤ 2^h+1:=by
 obtain ⟨b,hb,hv⟩:= h0
 have he: Tendsto (fun r=> b*(g r)^2) trail (𝓝 0):=by simpa using ((Coupling.conforms hG (strength_coupling hG)).pow (2:ℕ)).const_mul b
 filter_upwards [hv, he.eventually_le_const zero_lt_one] with r hr H' x hx
 specialize hr x (road_cap hx); rw [first_crop Z M ν H,opstamp,map_sub (stamp G h)] at hr
 change ‖op (U' r (r*x)) - stretching G h (-Real.log x)‖ ≤ _ at hr
 have hx': ‖D' (γ x)‖ ≤ 2^h:= (stretch_up G h hx.1).trans (pow_le_pow_left₀ (zero_le_one.trans hx.1) hx.2 _)
 simpa only [add_comm (1:ℝ),sub_add_cancel] using (norm_add_le (op (U' r (r*x))-(D' (γ x))) (D' (γ x))).trans
   (add_le_add (hr.trans H') hx')

def Error (t:ℝ→ℝ)(b r T:ℝ): Prop:= ‖ℳ P h r T - B' (γ T) (t r)‖ ≤ b ∧ ‖(t (r*T):ℂ)-J' (γ T) (t r)‖ ≤ b
lemma Error.mono {P:ℝ→tower S}{t:ℝ→ℝ}{b c r T:ℝ}{Z}{M}{ν}{h p}(e:Error P Z M ν h p t b r T)(w:b≤c):
    Error P Z M ν h p t c r T:=⟨e.1.trans w,e.2.trans w⟩
include H
omit H in
lemma short_frame {T r k:ℝ}(hT:1≤T)(H:opField (U' r (r*T) - cropK Kt (γ T) p (t r) h) ≤ k):
    ‖ℳ P h r T-B' (γ T) (t r)‖≤ k:=by
 rw [opstamp,map_sub (stamp G h),used] at H; unfold ℳ; rw [show D' (Real.log T)*op (U' r (r*T))-B' (γ T) (t r)=
       D' (Real.log T)*(op (U' r (r*T))-D' (γ T)*B' (γ T) (t r)) from by rw [mul_sub,← mul_assoc,stretch_mul,add_neg_cancel,flat,one_mul] ]; apply le_trans (norm_mul_le ..)
 exact (mul_le_mul (stretch_down G h hT) H (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

variable {U B:ℝ}(hU:0<U)(hB:0<B)
include hU hB
set_option maxHeartbeats 380000 in
lemma short_price (h0:Stamp P Z M ν t h 1)(hm:Stamp P Z M ν t h p)(hc:DialStamp Z M ν t p): ∃ C:ℝ,0≤C ∧
    ∀ᶠ r in trail,∀ T,Wide G U B r T →∀ x, x∈ Icc (1:ℝ) 2 →
      Error P Z M ν h p t (C*(g r)^p) (r*T) x ∧ ‖op (U' (r*T) (r*T*x))‖≤2^h+1:=by
 obtain ⟨b,hb,hS⟩:= hm; obtain ⟨w,hw,hW⟩:=hc; let A:= (max b w)*2^(p+1); refine ⟨A,by dsimp only [A]; positivity,?_⟩
 filter_upwards [out_radius hG (U:=U) (B:=B) _ (hS.and (hW.and (cost_bill P Z M ν h H h0))), strength_positive hG,
    fund_up (hG:=hG) hU hB, (Coupling.conforms hG (strength_coupling hG)).eventually_le_const zero_lt_one]
    with r hr hg hv HH T hT x hx
 obtain ⟨hs,H',hs'⟩:= hr T hT.1 hT.2; specialize hv T hT
 have ha(c:ℝ)(he: c ≤ max b w): c*g (r*T)^(p+1) ≤ A*g r^p:=by
    have hm:= hb.trans (le_max_left b w); refine (mul_le_mul he (pow_le_pow_left₀ hv.1.le hv.2 _) (by have hh:=hv.1; positivity) hm).trans ?_
    unfold A; rw [mul_pow, ←mul_assoc]; exact mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hg.le HH (by omega)) (by positivity)
 refine ⟨⟨short_frame P Z M ν h p hx.1 ((hs x (road_cap hx)).trans (ha b (le_max_left ..))),?_⟩,hs' x hx⟩
 specialize H' x (road_cap hx); rw [op_crop] at H'; exact H'.trans (ha w (le_max_right ..))
end YM.Integration.GradedFar.Neighbor
