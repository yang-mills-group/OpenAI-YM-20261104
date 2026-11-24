import YM.MS.Fleet.Passage
/-!
Pointwise merging on fixed meshes for the cover IR limit. Valid for every choice of periods / η path
of diagram comparison and fixed s grade; crucially allows support offsets growing with the index
i while proving the pointwise statement. Cumulant assembled through `Puff.Mom.Ord`. GPL.
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
variable {η:I→ℝ}{p:Team}{ V: Vista.Visa I }
  {c:Berth ( W:=W ) ( I:=I )}{A:W→ Actor G}{t:ℝ}{h:ℤ}
omit [LinearOrder W] in
abbrev UnitW := Fin 1
local notation "ζ"=> Scope G (Wind.skyline G p) η
-- collapsed reading
variable {F: Actor G} {Y: Dec G} (k: ℕ)
abbrev Ξtag : Finset UnitW := {(0: UnitW)}
lemma δclock {U:Rake.Dance G I UnitW}(H:PM F (skyline G p) Y h)(hx:SpaceOut.Easier G L (goalsK (fun _ _=>0) η (fun (_:UnitW)=> F)) P p η U): U Ξtag=Scope G Y η:= by
    let Q:Seeds G I UnitW:= (goalsK (fun _ _=>0) η (fun _=> F)); have he : SpaceOut.Easier G L Q P p η U:=hx
    let Z:= ζ; let V:= Scope G Y η; have hp n:Clocked ( zip0 Ψ ιW P ) (Q Ξtag n) ( V n ) ( lonely ιW Z V n ):= by
       have h' := castP η (fun _=>0) H n L P; rw [show Q Ξtag n=_ from funext (fun i=> goals_m (U:=fun _=> F) _ _ _ n i) ];
       dsimp only at h'; simp_rw [pure] at h'; exact h'
    funext n; induction n using Nat.strong_induction_on with| h n ih=>
       obtain ht:= he.2 Ξtag ( Finset.singleton_nonempty _ ) n; rw [ campus,Vista.idle_d rfl,add_zero,archB, show picks Ξtag=∅ from Finset.eq_empty_iff_forall_notMem.mpr (fun _ hx=> Rake.clips ( Finset.card_singleton _ ) hx), Finset.sum_empty,add_zero ] at ht; refine modal_uniq ( β_motor (engineV ..)) ht ?_; obtain HH:=hp n; rw [show lonely _ _ ( U Ξtag ) n= lonely ιW Z V n from Finset.sum_congr rfl fun j hj=> by rw [ih j ( mem_Ico.mp hj |>.2)] ]; exact HH
lemma blade1 {U:Rake.Dance G I UnitW} (H:PM F (skyline G p) Y h)(hx:SpaceOut.Easier G L (goalsK (fun _ _=>0) η (fun (_:UnitW)=> F)) P p η U): Vane.blade ( U Ξtag k )= fun i=> limUnder atTop (fun t:ℝ=> Y k (η i) t []):= by rw [δclock H hx]; funext i; unfold blade; congr! 1; funext t; unfold Scope Ext; rw [ sleeve_here ]; exact one_mul _
-- simpler scalar series bouquet singleton evaluation z.
lemma AloneOrb { X: SlotB G L } (i:I)(f:Terrify UnitW I)(hn: CCOrb G η p P L ( goalsK (fun _ _=>0) η (fun (_:UnitW)=> F) ) false f)( ht:SpaceOut.LedgerB G η p L false i (X i)): ∃ U, Lodged σbranch (normal G (dimT L i) false ) ( X i ) ( Ocell G L false i P ∘ F ( η i )) U ∧ ∀ n,Tendsto (fun r:ℝ=>U n r [] ) atTop (𝓝 ( f Ξtag n i )):= by
    obtain ⟨B,U,hH,h⟩ := hn; obtain ⟨hp,hV⟩:= hH i; obtain hᵥ:= just ht hp; rw [ hᵥ ]; let U':= U i Ξtag; refine ⟨ U',fun n=> ?_,fun n=>h _ n i ⟩; have hz:=hV.2 Ξtag ( Finset.singleton_nonempty _ ) n; obtain ⟨hx,hY⟩:= hz; have he : ( W0 L false ( goalsK (fun _ _=>0) η (fun (_:UnitW)=> F) ) i P Ξtag n )= Ocell G L false i P ( F (η i) n ):= by rw [ W0,goals_m ]; rfl -- W source unfolded
    have hv:labels ( σbranch ( n:=dimT L i ) ( G:=G) ) ( normal G ( dimT L i ) false ) (U i) Ξtag n=0:= by unfold labels; rw [ show picks Ξtag=∅ from Finset.eq_empty_iff_forall_notMem.mpr (fun _ hx=> Rake.clips ( Finset.card_singleton _ ) hx), Finset.sum_empty ]; -- label
    exact ⟨ hx.trans he, by rwa [hv,add_zero] at hY ⟩
end YM.MS.Fleet
