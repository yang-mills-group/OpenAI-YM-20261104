import YM.MS.Fleet.Place
/-!
Param-independent center and evaluation. Work on same order.Mode. Normalize cluster cumulants.
For comparison at fixed offsets use translation with the common anchor A ONLY affecting Q stencils;
for the cover Easy with any anchor in the equations yields same X. Thus passing to infinite
period leaves even the (flexibly tuned) single mark equal the proper moments.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Fleet
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Fiddle Osc.Snap Native
open Lattice City Latch Job Belt Rake Flux Wire Book Convolve Orbit Cog
open scoped Topology ContDiff Interval
variable {G:Gauge}{I J W:Type}[LinearOrder W]{L:I→Side}
 {X:Rake.Dance G I W}{Q:Seeds G I W}{P:Faces I}
local notation "Ψ"=> ( outside L )
local notation "ιW"=> ( Orbit.uniform G I )
open Native.Wilsonian Paint Rake.Geo Vane Land Program Logarithm Wind Menus Orbit.LogReal
open Puff Puff.Actors Puff.Mom
variable {η:I→ℝ}{T:Team}{ V: Vista.Visa I }
local notation "πA"=> Scope G (Wind.skyline G T) η
omit [LinearOrder W] in
lemma zip_δ (P:Faces I)(u:Planet G I)(x y:Glade G I)(L:I→Side)(i:I)(t:ℝ): zip2 (outside L) u P P x y i t= PairV false μzone 0 0 (u i t) (x i t) ( y i t ):= by unfold zip2; rw [ adjust,if_neg (by decide :¬false=true), add_zero ]; unfold feeling; rw [sub_self]; simp only [Dph,taste,Bool.false_eq_true,↓reduceIte,add_neg_cancel]; rfl
-- map params independently

def favorite (θ:J→I)(X:Rake.Dance G I W): Rake.Dance G J W:= fun s n j=> X s n (θ j)
lemma stalk (h:SpaceOut.Easier G L Q P T η X) (A:Faces J)(L': J→ Side)(f:J→I): SpaceOut.Easier G L' (fun s n j=> Q s n (f j)) A T (η ∘ f) (favorite f X):= by
    refine ⟨ by unfold favorite; rw [ h.1 ]; rfl, fun s hs n=>?_⟩; obtain ⟨hk,H⟩:= h.2 s hs n; constructor; · intro i; exact hk ( f i )
    obtain ⟨k,hK⟩:= H.cap; refine ⟨ ⟨k,fun i t=> hK (f i) t⟩,fun i t w=>?_⟩;
    obtain hp:= H.pace ( f i ) t w; convert! hp using 1;
    rw [ flat_zip0 _ rfl A, flat_zip0 Ψ rfl P ]; unfold campus lonely archB; simp_rw [Vista.idle_d rfl,add_zero]; simp_rw [Pi.add_apply,Finset.sum_apply]; -- zip2 simp
    simp_rw [zip_δ]; rfl
end YM.MS.Fleet
