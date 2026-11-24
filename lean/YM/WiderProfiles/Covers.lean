import YM.FVA2.Full.Covers
import YM.WiderProfiles.Vane.Trigger
/-!
WiderProfiles §F.1. Derivations extended from `YM/FVA2/Full/Covers.lean`.
Upper growth consumes an exponent of the existing market in `WCoverSep.pay`,
used at the four purchase sites touch/lighting/River/placeW. The rest of this
family of `_wide` lemmas propagates that change, following the original proofs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Rake
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Heat Tone Momentum Landau Detect Book High Frame Flux Osc Fiddle Snap City Wire Wind Signal Latch Job Belt
open Garment Outlook Geo Land Pearl Train Dock Emit Menus Book.Convolve LogTime LogTime.IntervalFamily Program
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W] {G:Gauge}{ P: Geo I}{B:Local.Physical.Deck G}{O:Land.Booked B}{M: Land.MS_Data G O}
variable (V:FullBook B) (P:Geo I)(T: Prescription B)(M: Land.MS_Data G O)
variable {P}{x:Position W I} (R: WMesh P x) (labels:W→ Label B)
include R
omit [LinearOrder W] in
lemma touristF_wide (hc:G.Simple) : WTour ( constantP G I (LowP G) ) (constantP G I (PlanetL G)) P x true (initials P T) (rowKF V P T ∘ labels) (Label.h ∘ labels):= ⟨ R,Geo.masterL .., fun _ _=> tagL P T _, fun i n=> tagXF V P T (labels i) n,fun s=> lightLF V P T hc (labels s) ⟩
end YM.MS.Rake
end
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vane
open Set Function Filter Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat High Frame Wire Signal Flux Wind Garment Outlook Latch Job Belt Rake Geo
open Osc Fiddle Snap Book.Convolve
open scoped Topology ContDiff Interval
variable { I W:Type}{G:Gauge}{P:Geo I}{K:Belt I}{F H D: Glade G I}{X:I→ℂ}{d h:ℕ}{ζ:ℝ}
variable { J:Type}[LinearOrder W]{x:Position W I}{c b:Bool}{K L K' L':Planet G I}{B B': Site G I}{A A':W→Site G I}{R:W→ℕ}{p:ℝ}{U V:Dance G I W}{S:Finset W}{v:I→ℝ}
local notation "m0"=> (fun (_:I)=>planeF)
open Land Pearl Train Booked Menus Local.Physical
variable { B: Deck G} (V:FullBook B){O:Booked B}(M:MS_Data G O)(T:Prescription B)(R:W→Label B)(P:Geo I)
include T
lemma CoversF_wide (h:G.Simple)(hx: WMesh P x)(he:TaylorOKF M V T): ∃ U V', LOrdF V P T R x U ∧ DOrd O P M R x V' ∧ ∀ S: Finset W,S.Nonempty→ ∀ n:ℕ,let k:= charge ( Label.h∘ R ) S; Verdict P k 0 ( U S n ) ∧ Verdict P k 0 ( V' S n ) ∧ Verdict P k eps_gain ( U S n - V' S n ):= by
    obtain ht:= touristF_wide V T hx R h; obtain hV:= builder_wide M hx R; obtain ⟨ U,hU⟩:= formal_wide ht; obtain ⟨W,hW⟩:= formal_wide hV; obtain ⟨Z,X,Tz⟩:= offersF V M T R he (gulfG (P:=P)); obtain ⟨Y,Q,RQ⟩:= offersF V M T R he ( westV (P:=P) ); exact ⟨ U,W,hU,hW,fun _ hp n=> ⟨ closure_wide ht Z Y hU hp n, closure_wide hV X Q hW hp n,trade_wide ht hV Z X Y Q Tz RQ hU hW hp n⟩ ⟩
end YM.MS.Vane
end
