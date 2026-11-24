import YM.GradedFar.Wayfare
/-!
# Growing physical version of G.1

Purchase from required earlier **compact** version of (G.1) on field and clock, with
`H` Main.Match on the same formal book. Last leg covers every stretch in the interval.
Includes useful inverse estimate (can tolerate buying a higher accuracy first).
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
   (P:ℝ→tower S) (Z:WilsonPrescription G) (M:MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))) (ν:ℝ) (h:ℕ)
local notation "g"=> strength G
local notation "γ" => fun (T:ℝ)=> -Real.log T
local notation "ϕ" => GroupS.ψ Z.criterion M ν
local notation "Kt" => GroupS.gaugeN Z.scheme Z.criterion M ν
local notation "D'" => stretching G h
local notation "op" => stamp G h
local notation "U'" => fun (r s:ℝ)=> LinearEquiv.toLinearMap (relative P r s h)
local notation "W" => Operation G h
variable {t:ℝ→ℝ} {hG:G.Simple}{σ:MS.Land.Prescription (Press.portDeck G)} (H:Main.Match Z hG M σ true)
local notation "Θ" => Error P Z M ν h

-- more demanding >0 on geometry B,C'. show sufficient for downstream `...`. norm bills and forecasts.
def G1Wide (t:ℝ→ℝ)(U B:ℝ) :=
    (∀ᶠ r in trail,∀ T:ℝ, Wide G U B r T → opField (U' r (r*T)) ≤ 2*T^h ∧ opField (U' (r*T) r) ≤ 2) ∧
    ∀ L:ℕ, ∀ᶠ p:ℕ in atTop,∀ᶠ r in trail,∀ T:ℝ, Wide G U B r T →
      opField (U' r (r*T)-cropK Kt (γ T) p (t r) h) ≤ g r^L ∧ ‖(t (r*T):ℂ)-crop p (t r) (ϕ (γ T))‖≤ g r^L
lemma G1Wide.forecast {P:ℝ→tower S}{Z M ν h}{U B:ℝ}(hv:G1Wide P Z M ν h t U B):
    FrameForecast P t (GroupS.gaugeN Z.scheme Z.criterion M ν) h U B:=
    ⟨⟨2,by norm_num,hv.1.mono (fun _ hr T h H=> (hr T ⟨h,H⟩).1)⟩,fun L=>(hv.2 L).mono (fun i hi=>
       ⟨1,zero_le_one,hi.mono (fun _ hr T h hh=>(hr T ⟨h,hh⟩).1.trans_eq (one_mul _).symm)⟩)⟩

lemma remit {r T A1 A2:ℝ}(hT:Wide G A1 A2 r T)(hP : ‖ℳ P h r T-1‖≤1/2):
      opField (U' r (r*T)) ≤ 2*T^h ∧ opField (U' (r*T) r) ≤ 2 := by
 have hu: ‖ℳ P h r T‖≤ 2:= by
   have hv:= norm_add_le (ℳ P h r T-1) 1; rw [sub_add_cancel] at hv; linarith only [hv,hP,id_cost (G:=G) h]
 let u:= U' r (r*T); let v:= U' (r*T) r
 have H₀: ℳ P h r T * op v=D' (Real.log T):= by
   have hp: op u * op v=1:= by rw [← price,show u*v=1 from (fold P h r (r*T) r).trans (repeated P h _),stamp_one]
   change (D' _ * op u)*op v=_; rw [mul_assoc,hp,mul_one]
 have hI : ℳ P h r T * op v- (ℳ P h r T-1)*op v=op v:=by rw [sub_mul,one_mul, sub_sub_cancel]
 simp only [opstamp]; constructor
 · rw [setting P h]; exact (norm_mul_le ..).trans ((mul_le_mul (stretch_up G h hT.1) hu (norm_nonneg _)
     (pow_nonneg (zero_le_one.trans hT.1) _)).trans_eq (mul_comm ..))
 change ‖op v‖ ≤ 2; have hA:=norm_sub_le (ℳ P h r T*op v) ((ℳ P h r T-1)*op v); rw [hI,H₀] at hA; obtain Hv:=
    hA.trans (add_le_add (stretch_down G h hT.1) ((norm_mul_le ..).trans (mul_le_mul_of_nonneg_right hP (norm_nonneg _))))
 linarith only [Hv]
variable (ht:Coupling G t)(hf:∀ p,1 ≤ p→ Stamp P Z M ν t h p)(hw:∀ p,1≤p→ DialStamp Z M ν t p)
    {U B:ℝ}(hU:0<U)(hB:0<B)
include ht hf hw H hU hB
private lemma rates (L:ℕ): ∀ᶠ p:ℕ in atTop,∀ᶠ r in trail,∀ T:ℝ, Wide G U B r T →
      opField (U' r (r*T)-cropK Kt (γ T) p (t r) h) ≤ g r^L ∧ Θ p t (g r^L) r T:=by
 obtain ⟨k,_,hk⟩:= exists_nat_pow_near (show (1:ℝ)≤2^h+4 from by linarith only [pow_nonneg (by norm_num:(2:ℝ)≥0) h]) (show (1:ℝ)<2 by norm_num)
 filter_upwards [eventually_ge_atTop 1, spent (hG:=hG) hU hB L (k+1+h), spent (hG:=hG) hU hB L (k+1)] with
    p hp h₁ h₂
 obtain ⟨b,hb,hP⟩:= paid Z M ν h p H ht hU hB hp; obtain ⟨c,hc,hC⟩:= short_price P Z M ν h p H hU hB (hf 1 le_rfl) (hf p hp) (hw p hp)
 let F:=fare Z M ν h p
 let x:=b+2*c; have hx:0≤x:=by dsimp only [x]; positivity
 filter_upwards [hP,hC,h₁ x hx,h₂ x hx,strength_positive hG] with r HB HD Hv Hv' hg T hT
 obtain e:= rally P Z M ν h p H hg HB HD hb hc _ hk.le hT
 refine ⟨?_,e.mono (Hv' T hT)⟩; rw [opstamp,map_sub (stamp G h), used,setting P h, ← mul_sub]
 refine (norm_mul_le ..).trans ((mul_le_mul (stretch_up G h hT.1) e.1 (norm_nonneg _) (pow_nonneg (zero_le_one.trans hT.1) _)).trans ?_)
 refine le_trans (b:= x*T^(k+1+h)*(g r)^p) ?_ (Hv T hT); unfold x; exact le_of_eq (by ring)

/-- The growing-scale purchase. Instantiated later with our original physical election. -/
theorem extension : G1Wide P Z M ν h t U B :=by
 obtain H':= rates P Z M ν h H ht hf hw hU hB
 refine ⟨ ?_,fun L => (H' L).mono fun p hp=> hp.mono (fun r hr T hT=> ?_)⟩
 · obtain ⟨p,hp,he⟩:=((eventually_ge_atTop 1).and (H' 1)).exists
   obtain ⟨b,hb,hP⟩:= paid Z M ν h p H ht hU hB hp 
   filter_upwards [he,hP,(Coupling.conforms hG (strength_coupling hG)).eventually_le_const (by norm_num:(0:ℝ)<1/4)]
      with r hr H H₀ T hT; apply remit P h hT; let v:= fare Z M ν h p (γ T) (t r)
   exact (opt (ℳ P h r T) 1 v).trans ((add_le_add (hr T hT).2.1 (H T hT).eye).trans (by rw [pow_one]; linarith only [H₀]))
 · exact ⟨(hr T hT).1,by rw [op_crop]; exact (hr T hT).2.2⟩
end YM.Integration.GradedFar.Neighbor
