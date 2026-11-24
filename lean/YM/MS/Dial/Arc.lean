import YM.MS.Milk.Feed
/-!
# Negative time domination in continuum frame.Purpose: separated continuity; also grants actual PT regulator statements on sequences of profile samples converging to fixed physical positions. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Dial
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Osc Snap City Job Geo Land Local.Physical Port Tide Vista Vane -- alias
open scoped Topology ContDiff
variable {I W E:Type} {G:Gauge} {v t:ℝ}{a b:ℤ}{l:Filter I} {r:ℕ}
set_option quotPrecheck false
local notation "Υ" => east ( frameF I v ) false
local notation "Ω"=> ( Υ ).price
open Wire Belt
abbrev PoleP (v:ℝ):= ( east ( frameF I v ) false ).time
def slotL (h:t≤0)(i:I): PoleP ( I:=I ) v:= ⟨i,t,h⟩
lemma length_Ω (h:t≤0) (i:I): (Ω).length ( slotL ( v:=v ) h i )= exp t:= coldE .. -- argument placeholder
lemma size_Ω (h:t≤0) (i:I): (Ω).basic (slotL h i)=(1+|v|)*(1+|t|):= rfl
lemma weight_Ω (h:t≤0)(i:I)(p:QP): ( Ω ).weight (slotL h i) p=1+exp t*‖p‖:= by rw [ Scale.weight,length_Ω ] -- warm p
variable {F H:Dance G I W}{Y:ℝ→ Glade G I} -- disam
variable {L:PoleP (I:=I) v→ QP× E→ℂ}{a: PoleP (I:=I) v→ℝ}
   [NormedAddCommGroup E][ NormedSpace ℝ E ]
lemma major (h:t≤0)(hx:pole Ω L a)(p:I)(hp:∀ i, a (slotL h i)= a ( slotL h p ))(y:E):∃ f:QP→ℝ, Integrable f planeF∧∀ i q, ‖L (slotL h i) (q,y)‖≤ f q:= by
    obtain ⟨C,hC,n,hn⟩:= hx.dominates 0 5; simp only [norm_iteratedFDeriv_zero,pow_zero,mul_one] at hn; let Z:= slotL (v:=v) h p; let W:= C* ( Ω ).full.cheap Z y ^ n*a Z; refine ⟨ fun i=> W*( Ω ).dust 5 Z i, ((Vane.beacon Υ).integrable Z).const_mul W,fun i v=>?_⟩; -- proof W implicit parse
    have he:= hn ( slotL h i ) v y trivial; obtain hB: ( Ω ).basic (slotL h i)=( Ω ).basic Z:= rfl; obtain hr:( Ω ).length (slotL h i)=( Ω ).length Z:= rfl; convert he using 1; rw [hp i]; rfl -- v shadow vζ. danger
-- DCT helper
variable [l.IsCountablyGenerated]{K:I→QP→ℂ}
abbrev tend (l:Filter I)(p:I) {Y:Type}[TopologicalSpace Y] (f:I→Y): Prop:= Tendsto f l (𝓝 (f p))
lemma pole_pos (h:t≤0)(hx:pole Ω L a)(p:I)(hp:∀ i, a (slotL h i)= a (slotL h p))(he:∀ i,Peak ( K i ))(y:E)(hv:∀ q,tend l p (fun i=>K i q *L (slotL h i) (q,y))): tend l p (fun i=>∫ q,K i q * L (slotL h i) (q,y) ∂planeF):= by
    obtain ⟨f,hF,hH⟩:= major h hx p hp y; apply tendsto_integral_filter_of_dominated_convergence f ?_ ?_ hF ( Eventually.of_forall hv );
    · refine Eventually.of_forall fun i=> Measurable.aestronglyMeasurable ?_ ; exact ( ( he i ).shore.mul ( (hx.smooth (slotL h i) ).continuous.comp ( f:=fun q:QP=>(q,y) ) (by fun_prop) ) ).measurable -- Peak API
    exact Eventually.of_forall (fun i=> Eventually.of_forall fun q=> by rw [norm_mul]; exact (mul_le_of_le_one_left ( norm_nonneg _ ) ( he i |>.pays q ) ).trans (hH i q))
end YM.MS.Dial
