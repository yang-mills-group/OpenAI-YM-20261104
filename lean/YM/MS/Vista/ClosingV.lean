import YM.MS.Vista.Closing
/-!
# Summary marker-limits. Compare endpoint ℓ absolute.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Orbit.LogReal
open scoped Topology ContDiff Interval
variable {I W E:Type}{G:Gauge}{L:I→Side}{M:Visa I}{f g:I→ℂ}{X Y:Glade G I}
    {b:Bool}
lemma cash_plus (h:cash_out M L f)(he: cash_out M L g): cash_out M L ( f + g ):= by obtain ⟨U,hU,k,H⟩:=h; obtain ⟨V,hV,j,hJ⟩:=he; let P:=Boot (P:=After M L) (M:=M) soonM; refine ⟨ U+V,by linarith,j+k,fun i=>?_⟩; obtain hx:= P.one_le i; have hv : Dwind L i≥0:= Real.rpow_nonneg ( δ_p L i|>.le ) _; apply (norm_add_le .. )|>.trans; rw [add_mul,add_mul]; apply add_le_add ( ( H i ).trans ?_ ) ( ( hJ i ).trans ?_ ) <;> (gcongr; omega) -- use known S vs P
lemma cash_neg (h: cash_out M L f): cash_out M L (-f):= by unfold cash_out; simp only [ Pi.neg_apply, norm_neg ]; exact h
lemma cash_sub (h:cash_out M L f)(he:cash_out M L g): cash_out M L ( f-g ):= by rw [sub_eq_add_neg]; exact cash_plus h (cash_neg he)
local notation "Ξ"=> Mid M L
lemma rent_end (i:I): Beef Ξ ( Vista.curtain (M:=M) i ) = Dwind L i:= by unfold Beef goodM; rw [myEnd]
abbrev zeroW (X: Glade G I) (L:I→Side)(i:I):ℂ:= X i (tickA L i) []
lemma bookZ (p:I): (Ξ).price.basic (Vista.curtain (M:=M) p)=(Boot (P:=After M L) (M:=M) soonM).basic p:= rfl
lemma cash_step (he:ΔMark M L false ( X-Y )): cash_out M L ( zeroW X L-zeroW Y L ):= by
   obtain hp:= Vane.scalar_bill ( he 0 ); rw [RateΔ,gain0,mul_one] at hp; obtain ⟨V,hV,k,hK⟩:= hp; refine ⟨V,hV,k,fun i=>?_⟩; obtain h:=hK ( Vista.curtain (M:=M) i ); dsimp only at h; rw [ bookZ,rent_end ] at h; convert h using 2; change _ - _= X i (τ (until0 L i)) []- Y i (τ (until0 L i)) []; rw [τ_h] -- conversion with ℝ cast
-- clock→heat length. Include actual ℝ endpoint equality finite Boot $θ.
lemma past_lvl {f:ℝ→ℂ} (i:ℂ) (hp:Tendsto (f ∘ τ) atTop (𝓝 i)): Tendsto f atTop (𝓝 i):= by
   let v(x):= Real.log (1+x); obtain h:Tendsto v atTop atTop:= tendsto_log_atTop.comp ( tendsto_atTop_add_const_left atTop 1 tendsto_id ); apply (hp.comp h).congr'; filter_upwards [eventually_ge_atTop (0:ℝ)] with i hi; change f (τ (v i))= _; simp only [τ,v,exp_log (show 0<1+i from by linarith), add_sub_cancel_left ] -- function theorem names
abbrev FinalScore (V:Visa I)(L:I→Side)(F: Glade G I): Prop := (∀ i,Vane.Allow F i ) ∧ cash_out V L ( Vane.blade F - zeroW F L )
lemma arrival_F (ht: LookS (warp0 G I X) (bend G I Y))(hp: paid (After M L).price (fun p=>‖Vane.scalar (bend G I Y) p‖ ) (Tail M L * Beef (After M L))): FinalScore M L X:= by
    obtain ⟨h,H⟩:= Δ_paid ht hp; have he(i:I):= past_lvl ( f:=fun t=> X i t [] ) (Vane.blade (warp0 G I X) i) ( h i ); have hm(i:I): Vane.Allow X i := tendsto_nhds_limUnder ⟨_,he i⟩; have hx (i:I): zeroW X L i= EndN (V:=M) (warp0 G I X) L i:= by change X i (tickA L i) []=X i (τ (until0 L i)) []; rw [τ_h]
    rw [ ← funext hx ] at H; refine ⟨ hm,?_⟩; rw [show Vane.blade X= _ from funext fun i=> tendsto_nhds_unique ( hm i ) ( he i ) ]; exact H
variable [LinearOrder W]{P K:Planet G I}{ V S:Rake.Site G I}{Y Y':H_defect G I}{Q:ℕ→I→Law G}
    {Q': Seeds G I W}{X U:Rake.Dance G I W}{A:I→Cover}
local notation "Ζ0"=> outside L
local notation "Ϝ"=>enterV L b
variable (hS:Circuit (outside L) P Q A Q' V Y X)(hS': Circuit (enterV L b) K Q A Q' S Y' U)
  ( hx:Gate M V Q')(hf:Budget M L K P)( hz:Place M L b A)
include hS hS' hx hf hz
lemma signal (T: Finset W)(ht:T.Nonempty)(i:ℕ): FinalScore M L ( U T i ) ∧ FinalScore M L (X T i) ∧ cash_out M L ( Vane.blade ( U T i )- Vane.blade ( X T i ) ):= by
    obtain ⟨_,_,_,B⟩:= last_m hS hS' hx hf hz; obtain he:= arrival_F (hot hS' hf.fix ht i) (Vane.scalar_bill ( B i T ht )); obtain hp:= arrival_F (L:=L) ( hot hS hf.logw ht i ) ( lunar ( ζ_cover hS hx hf|>.2 i T ht )); refine ⟨ he,hp,?_⟩; let X0:= X T i; let Y0:= U T i; change cash_out M L ( Vane.blade Y0-Vane.blade X0 ); rw [ show (Vane.blade Y0-Vane.blade X0)=(( Vane.blade Y0-zeroW Y0 L )-( Vane.blade X0-zeroW X0 L ))+(zeroW Y0 L-zeroW X0 L ) from (by abel) ]; exact cash_plus ( cash_sub he.2 hp.2 ) ( cash_step ( Peak hS hS' hx hf hz ht i ))
end YM.MS.Vista
