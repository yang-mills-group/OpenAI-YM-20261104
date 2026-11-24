import YM.MS.Vista.VCore
/-!
# End gate B cost after finite. Forward growth past endpoints.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Vista
open Set Function Filter Finset Metric MeasureTheory Real High
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit
open Rake.Geo Orbit.LogReal
open scoped Topology ContDiff Interval
variable {G:Gauge}{I E:Type}{L:I→Side}{P:Belt I}{ V:Visa I}{X:Rake.Site G I}{Z:Lin I}
   {F:Glade G I}{ Q:ℕ→I→Law G}{b: Bool}{ K:Planet G I}{c:ℝ}
local notation "Θ"=> After V L
local notation "Ω"=> enterV L b
lemma afterT (ζ:(After V L).time): until0 L ζ.1≤ tstart ζ:= ζ.2.property
lemma afterR (ζ:(After V L).time): (After V L).price.length ζ= tickA L ζ.1 := rfl
lemma afterM (ζ:(After V L).time): (After V L).price.length ζ=( Miles Θ L ζ |>.val:ℝ):= rfl
lemma Next_fee {a:(After V L).time→ℝ}(he:Piece (After V L) K a)(hx:nn a): Vel Θ Ω K (μF Θ L ) a:= ⟨ f_cap (fun i=>( afterM i ).le ), he,hx⟩
lemma unit_span {d:ℝ}: Adjuster ( G:= G ) Θ b true (goodM Θ d):= by intro E _ _ w hz hc p q he hv; apply le_of_eq; unfold Qbud goodM; rw [ afterR p, afterR q, he ]
lemma Large_B {μ:(After V L).time→Measure QP}(P0: Vel (After V L) Z K μ 1)(B1: bulk ( Mid V L ) X)(H:Core Z K X Q): bulk ( After V L ) X:= by
   intro k hk; induction k using Nat.strong_induction_on with| h k hX=>
     let ℓ:= ( rateS Θ 4 ); obtain Hm:= live_g H.h H.entry H.script hk; have hL : Adjuster (G:=G) Θ true true ℓ := by unfold ℓ; rw [ ← good_η ]; exact unit_span
     have hv: Lease true true (Θ).price ( LaunchF Θ (until0 L) (warp0 G I (X k)) ) ℓ:= by unfold ℓ; obtain hc:=B1 k hk; unfold χr WarpHere at hc; rw [ ← good_η ] at hc ⊢; exact Vista.station hc unit_span
     refine kernel (a:= until0 L) soonM.acc Hm hL (rateC _ _) hv ?_; intro r he hF; obtain hp := On_c (b:=false) (A:=fun _=>0) P0 hF ( H.entry k |>.1 ) (rateC _ _) (fun x=> Bool.noConfusion x); rw [ one_mul ] at hp; unfold coinF C_wind; rw [ map_add ]; apply Lens.plus hp; refine pinch (c:=false) ( fancy ?_ _ ) ( fun x=>Bool.noConfusion x ); exact Cuba ( P:=Θ ) _ ( rateC _ _ ) (fun i hi=>by obtain he:=early _ _ _ hi; obtain hs:= step_F ( hX (k-i) (by omega) (by omega)) ( hX i (by omega) (by omega) ) P0.2.1 ( rateC _ _ ) ( fun i=>zero_le_one ); rw [ one_mul ] at hs; exact hs ) -- `fancy` infer unfolding groups.
end YM.MS.Vista
