import YM.MS.Echo.Event
/-!
# BV equivalence of cover-correlation limits. Moving geometry, order by order.
Turns off exactly on all eventually disjoint native stencils. Doesn't take limits of
harmonics or assume raw limit data was given on arbitrary sequences.
-/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Echo
open Set Filter Function Finset Metric MeasureTheory Real
open Koszul Plane Landau Detect Tone Momentum Heat Osc Native
open Lattice Book Convolve Cylinder Lab High Program Logarithm Wind Menus Native.Wilsonian Native.Draft Paint
open Flux City Signal Modeled Frame Wire Latch Job Belt Rake Orbit Orbit.LogReal Vista High.Knobs Fleet Rake.Geo
open Puff Puff.SplitP Puff.Engine Puff.Actors Puff.Mom
open scoped Topology ContDiff Interval
variable {I W:Type}[LinearOrder W]{G:Gauge}{n i k:ℕ}{ U Y:W→ Actor G }{ F H V: Actor G}{u:ℤ}
    {p:Team}{R:High.Recount G}{s q:Finset W}
    {z:W→ Cover}{c:Berth ( I:=I ) ( W:= W )}{l:Filter I}{v w:W}
local notation "ξ"=> skyline G p
lemma switchM (h:ReadyP p U)(he:ReadyP p Y)(s:Finset W): ReadyP p ( s.piecewise Y U ) where
    badge w:= by by_cases hz:w∈ s; rw [Finset.piecewise_eq_of_mem _ _ _ hz]; exact he.badge w; rw [Finset.piecewise_eq_of_notMem _ _ _ hz]; exact h.badge w -- check lemma `rwa`
    shine w x:= by by_cases hz:w∈ s; rw [ Finset.piecewise_eq_of_mem _ _ _ hz ]; exact he.shine w x; rw [ Finset.piecewise_eq_of_notMem _ _ _ hz ]; exact h.shine w x
variable (hu:Sparse l c)(hx:ReadyP p U)(he:ReadyP p Y)
include hu hx he
lemma replace (J:Finset W) (n:ℕ) (hM:∀ i∈ q,Menu p ( U i ) ( Y i )) (hq:q⊆J): ∀ᶠ i in l,∀ s:ℝ, Refund p (Memo (starP c i) U J) (Memo (starP c i) (q.piecewise Y U) J) n s := by
   classical
   induction q using Finset.induction_on with
   | empty=> simp only [Finset.piecewise_empty]; exact Eventually.of_forall fun _ _=> Ziff _
   | insert i q hi ih=>
       obtain ht := ih (fun j hj=> hM j (Finset.mem_insert_of_mem hj)) ( Finset.Subset.trans (Finset.subset_insert _ _) hq ); let w:= q.piecewise Y U; let X:= (insert i q).piecewise Y U;
       let Q:= J.erase i; have hK:i∉Q:=Finset.notMem_erase _ _; have hg : insert i Q=J:= Finset.insert_erase (hq (Finset.mem_insert_self ..));
       have hf:∀ j∈ Q,w j=X j:= fun j hj=> ( by unfold w X; by_cases hz:j∈ q; simp [*, Finset.piecewise]; obtain he: j ≠ i:= Finset.mem_erase.mp hj|>.1; simp [*, Finset.piecewise] );
       obtain hr:= future_M hu hK hf ( switchM hx he q ) ( switchM hx he (insert i q)) (show Menu p ( w i ) ( X i ) from (by unfold w X; rw [ Finset.piecewise_eq_of_notMem _ _ _ hi, Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_self ..) ]; exact hM i ( Finset.mem_insert_self .. ))) n; rw [hg] at hr; filter_upwards [hr,ht] with i hi ht y; exact Refund.trans ( ht y ) ( hi y )
lemma render (H:∀ i,Menu p ( U i ) ( Y i ))(J:Finset W) (n:ℕ) : ∀ᶠ i in l,∀ y:ℝ, Refund p ( Memo (starP c i) U J ) ( Memo (starP c i) Y J ) n y:= by
   filter_upwards [ replace hu hx he J n (fun s _=>H s) (Finset.Subset.refl J) ] with i hi y; have hv:= hi y; rw [ mergeNe (switchM hx he J|>.badge) he.badge (fun j hj=> Finset.piecewise_eq_of_mem _ _ _ hj ) ] at hv; exact hv
variable (B: Fixed ( col ( skyline G p )) R true 4 1)(hG:G.Simple){L L':I→Side}{A A':Faces I}{ η:I→ℝ}{X D:Rake.Dance G I W}
include B hG
theorem quote (h:∀ i,Menu p ( U i ) ( Y i ))(hQ:SpaceOut.Easier G L (goalsK c η U) A p η X)(hU:SpaceOut.Easier G L' (goalsK c η Y) A' p η D)(k:ℕ)(s:Finset W): ∀ᶠ i in l, bury i s ( Fleet.toZ X ) k=bury i s ( toZ D ) k:= by
    filter_upwards [render hu hx he h s k] with i hi; obtain ⟨V,hV,hm⟩:= ( hi ( η i ) ).ticket; let A:= Memo (starP c i) U s; let B':=Memo (starP c i) Y s; obtain ⟨X',hx'⟩:= member (skyPC G p) hV; obtain ⟨Z,hZ⟩:= member ( skyPC G p ) ( show Circle G A false 0 from memory _ hx.badge _ ); obtain ⟨Q',ht⟩:= member ( skyPC G p ) ( show Circle G B' false 0 from memory _ he.badge _ ); let z:= η i; let a:= bury i s ( Fleet.toZ X ) k; let b:=bury i s ( Fleet.toZ D ) k; let f(t:ℝ):= Z k z t []- Q' k z t []; have hz': Tendsto f atTop (𝓝 (0:ℂ)):= ( clock0 z B hV hx' k ).congr (fun t=> congr_fun (survive z (skyPC G p) hx' hG hV hZ ht _ hm t ) [] ); exact sub_eq_zero.mp ( tendsto_nhds_unique ( ( beeT B i s hx.badge hQ k Z hZ ).sub (beeT B i s he.badge hU k Q' ht ) ) hz') -- names
end YM.MS.Echo
