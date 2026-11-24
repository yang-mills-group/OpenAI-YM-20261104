import YM.MS.Fleet.Visit
/-!
# Products for the actual cover IR limit
Returns both result on limUnder and proof of convergence from prior Ω. No cubical-gauge changes.
Stencils in marks supported on finite configurations offset by c from center A.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I J W:Type}[LinearOrder W]{L:I→Side}
 {X U:Rake.Dance G I W}{Q:Seeds G I W}{P:Faces I}{R:High.Recount G}
local notation "Ψ"=> ( outside L )
local notation "ιW"=> ( Orbit.uniform G I )
open Native.Wilsonian Paint Rake.Geo Vane Land Program Logarithm Wind Menus Orbit.LogReal
open Puff Puff.SplitP Puff.Actors Puff.Engine Puff.Mom Vista High High.Knobs
variable {η:I→ℝ}{p:Team} (B: Fixed ( col ( skyline G p )) R true 4 1)
   {c:Berth ( W:=W ) ( I:=I )}{A:W→ Actor G}
include B
lemma beeT (i:I)(s:Finset W)(h:Badge A)(hx:SpaceOut.Easier G L (goalsK c η A ) P p η X)(n:ℕ) ( H:Dec G ) ( he:PM ( Memo (fun w=>c w i) A s ) (skyline G p ) H 0):
 Tendsto (fun t:ℝ=> H n ( η i ) t []) atTop (𝓝 ( bouquet (fun a j=> toZ X a j i ) s n )):= by
    let u (w:W):= c w i; let t:=η i; let F:=Memo u A s; obtain hF:Circle G F false 0:=memory u h s
    obtain ⟨Y,f,hY,hF',h0,hV⟩:=sold B h t u
    obtain ⟨ Z,g,hH,hG,hQ,hG'⟩:= sold ( A:=fun _:UnitW=> F ) B (fun _=>hF) t 0
    have hf: Y=favorite (fun _:Unit=> i) X := by
       obtain hz:= stalk hx (A:=fun (_:Unit)=>0) (fun _=>1) (fun _=>i); -- param η identity.Q recursion might not defeq (dite) rewrite
       exact soloP hY hz
    let S (i:ℕ)(s:Finset W)(n:ℕ):= bouquet ( f i ) s n
    have hK (i:ℕ):g i Ξtag n=S i s n:= by
       obtain ⟨ B0,V,hB,hT⟩:= ( show CCOrb _ _ _ _ _ _ _ _ from h0 )
       obtain hs := (hB i).1; obtain ⟨ A',hv',hA⟩:= proper ( G:=G ) ( U:=A ) i h0 h ( X:= B0 ) hs s; obtain ⟨C,hp,hc⟩:= AloneOrb (F:=F) i _ hQ hs; -- ctx
       have he:A'=C:= momonly hv' hp; rw [he] at hA; exact tendsto_nhds_unique ( hc n ) ( hA n )
    have hu : toZ Z Ξtag n () = bouquet ( fun a j=> toZ Y a j () ) s n := tendsto_nhds_unique (( hG' _ n ).congr (fun i=> hK i)) ( hV.select s n )
    rw [ hf ] at hu; rw [← show toZ Z Ξtag n ()=Mom.bouquet (fun a j=>toZ X a j i) s n from hu ];
    have hi:= hG Ξtag n (); change Tendsto _ _ ( 𝓝 ( Vane.blade ( Z Ξtag n ) () ) ) at hi; change Tendsto _ _ ( 𝓝 ( Vane.blade _ () ) ); refine hi.congr fun t=>?_ ; rw [ δclock he hH ]; unfold Scope Ext; rw [sleeve_here]; exact one_mul _
end YM.MS.Fleet
