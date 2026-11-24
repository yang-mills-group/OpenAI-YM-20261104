import YM.GradedFar.Wayfarer
/-! # Recurrence for G1 step upgrades, includes any placements T upwards -/
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
variable {t:ℝ→ℝ} {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "B'" => fare Z M ν h p
local notation "J'" => ticker Z M ν p
local notation "v'" => fun r=> (t r:ℂ)
local notation "Θ" => Error P Z M ν h p t

lemma opt {E:Type*} [NormedAddCommGroup E] (p q r:E) : ‖p-q‖ ≤ ‖p-r‖+‖r-q‖:= by
 simpa only [sub_add_sub_cancel] using norm_add_le (p-r) (r-q)
-- preserve every operator. T recurrence multiplier depending only on h. no valuation shift cost omitted.
include H in
set_option maxHeartbeats 400000 in
lemma passage {b c d r T x:ℝ}(hT:1≤T)(hx:x∈ Icc (1:ℝ) 2)(hA: Θ b r T)(hv:FormalPlan Z M ν h p t c r T)
    (he:Θ d (r*T) x)(hw:‖op (U' (r*T) (r*T*x))‖≤2^h+1): Θ ((2^h+3)*b+c+2*d) r (T*x):=by
 let t':=v' r; let s:=r*T; let t₁:=v' s; let t₂:=v' (s*x); let z:=J' (γ T) t'; let z':=J' (γ (T*x)) t'
 have Hb: 0≤b:= (norm_nonneg _).trans hA.1; have Hd:0≤d:= (norm_nonneg _).trans he.1
 let u:= op (U' (r*T) (r*T*x)); let u':= B' (γ T) t'; let v:=B' (γ x) z; let vΔ:=ℳ P h s x
 have H₁ : ‖vΔ-v‖ ≤ d+b:= (opt _ _ (B' (γ x) t₁)).trans (add_le_add he.1 ((hv.transfer x hx).trans hA.2))
 have H₂ : ‖ℳ P h r (T*x)-u'*vΔ‖ ≤ b*(2^h+1):= by
   let D:=D' (Real.log x)
   have hP:u'*vΔ=D*u'*u:=by
     change u' * (D * u)=_; unfold u' t'; rw [kept Z M ν H,mul_assoc]
   rw [stamp_step P h hT hx,hP]; change ‖D* _ *u-D* _ *u‖ ≤ _; rw [← sub_mul,← mul_sub]; exact
     (norm_mul_le ..).trans ((mul_le_mul ((norm_mul_le ..).trans ((mul_le_mul (stretch_down G h hx.1) hA.1 (norm_nonneg _) zero_le_one).trans_eq (one_mul _))) hw (norm_nonneg _) Hb))
 have H₃:= (opt (ℳ P h r (T*x)) (u'*v) (u'*vΔ)).trans (add_le_add H₂ (show ‖u'*vΔ-u'*v‖ ≤ 2*(d+b) from by
   rw [← mul_sub]; exact (norm_mul_le ..).trans (mul_le_mul hv.cost H₁ (norm_nonneg _) (by norm_num))))
 constructor
 · exact (opt _ _ (u'*v)).trans ((add_le_add H₃ (hv.surplus x hx)).trans_eq (by ring))
 rw [← mul_assoc r]
 have h4: ‖t₂-J' (γ x) z‖ ≤ d+2*b:= (opt _ _ (J' (γ x) t₁)).trans (add_le_add he.2
   ((hv.hear x hx).trans (mul_le_mul_of_nonneg_left hA.2 (by norm_num))))
 exact (opt _ _ (J' (γ x) z)).trans ((add_le_add h4 (hv.corner x hx)).trans (by nlinarith only [Hb,Hd,pow_nonneg (by norm_num : (2:ℝ)≥0) h]))
variable {U B:ℝ}(hU:0<U)(hB:0<B)
include H in
lemma rally {b c r:ℝ}(hg:0<g r)(hv:∀ T,Wide G U B r T → FormalPlan Z M ν h p t (b*g r^p) r T)
    (hs:∀ T,Wide G U B r T →∀ x, x∈ Icc (1:ℝ) 2→ Θ (c*g r^p) (r*T) x ∧ ‖op (U' (r*T) (r*T*x))‖ ≤ 2^h+1)
    (hb:0≤b)(hc:0≤c)(k:ℕ)(hk:(2:ℝ)^h+4 ≤ 2^k) {T:ℝ}(hT:Wide G U B r T): Θ ((b+2*c)*T^k*g r^p) r T:=by
 let w:=(b+2*c)*g r^p; have hw:0 ≤ w:= by dsimp only [w]; positivity
 have hh: ∀ n:ℕ,∀ t,Wide G U B r t → t≤(2:ℝ)^n → Θ (w*t^k) r t:=by
   have ha(T:ℝ)(hx:Wide G U B r T)(ht:T≤2): Θ (w*T^k) r T:=by
     obtain H₀:= (hs 1 ⟨le_rfl,hx.1.trans hx.2⟩ T ⟨hx.1,ht⟩).1; rw [mul_one] at H₀
     exact H₀.mono ((mul_le_mul_of_nonneg_right (by linarith only [hc,hb] : c ≤ b+2*c) (by positivity : 0 ≤ g r^p)).trans
          (le_mul_of_one_le_right hw (one_le_pow₀ hx.1)))
   intro n
   induction n with
   | zero=> exact fun t ht hs=> ha t ht (hs.trans (by norm_num))
   | succ n ih=>
      intro T hx hx'; by_cases he:T≤2; · exact ha T hx he
      let u:=T/2; have hh:u*2=T:= by dsimp only [u]; ring
      have h₀:1≤u:=by dsimp only [u]; linarith
      have hp:Wide G U B r u:= ⟨h₀,(show u≤T by linarith only [h₀,hh]).trans hx.2⟩
      specialize ih u hp (by rw [pow_succ] at hx'; linarith only [hx',hh]); obtain ⟨hP,H'⟩:= hs u hp 2 (by constructor <;> norm_num)
      rw [← hh]; refine (passage P Z M ν h p H h₀ (by constructor <;> norm_num) ih (hv u hp) hP H').mono ?_
      have hz: w ≤ w*u^k:=le_mul_of_one_le_right hw (one_le_pow₀ h₀)
      calc
        _ ≤ (2^h+4)*(w*u^k) := by
              have ho : w=b*g r^p+ 2*(c*g r^p):= by dsimp only [w]; ring
              linarith only [hz,ho]
        _ ≤ 2^k*(w*u^k) := mul_le_mul_of_nonneg_right hk (hw.trans hz)
        _ = _:=by rw [mul_pow]; ring
 obtain ⟨n,_,hn⟩:= exists_nat_pow_near hT.1 (show (1:ℝ)<2 by norm_num); rw [mul_right_comm]; exact hh _ T hT hn.le
end YM.Integration.GradedFar.Neighbor
