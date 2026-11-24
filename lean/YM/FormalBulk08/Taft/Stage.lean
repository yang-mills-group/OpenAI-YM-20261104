import YM.FormalBulk08.Taft.Shadow
set_option autoImplicit false
noncomputable section
namespace YM.FormalBulk08.Taft
open Reef Flat Lattice Laurent Bloch Exterior Wilson Filter Function Orb Wick Series Jets Work.F03 Work.F05 Work.F08 PowerSeries Next.Free RG Precision
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp Pose Glide Chapel Bank Dawn Grail Palm Wine Rial Aster Roof Quire Clover Dove Dove.Lab North Elm Drift Trellis Avenue Castor
open scoped Topology ENNReal Matrix ContDiff BigOperators Classical
open Planned.PrimaryIntegral295 Place Film Carrier Source Source.Drops Labels
variable {G:Gauge}{K:KernelChoices}{I:Type}{W:Lab G K I}{ρ:ChartRatio G}{E e r d D R n:ℕ}{o:Loc G 1}{F:Frame G d}{H:Hol G}{T:SectionData F}
variable (q:Quota F H W o D E R)(u:Use W ρ E)(h:LocalRatio ρ)(a:hue G)(hs:G.Simple)(ht:T.Sound H)(hb:Bid.pop T)(hr:d≤R)
variable (P C:Pin W.scrolls) (hp:∀ i,P.N i≤ C.N i)
omit h in
def prim (hp:d+1≤D)(M:I→ℕ)(x:Deck P):=bridge K W a F ρ T hp x.a (M x.a) x.b
omit h in
def primL (i:Turn P)(x:Letter F):= heightK ((W.V i.a).S.block i.b) d (Pose.weight F x)
-- defs `a`,`q` absent body; may need explicit
include u
lemma tallSoft (x:Letter F): Soft (Dove.tide P) (fun i=> primL P i x):= by
   unfold primL; simp_rw [heightK_of_le _ (weightFits F x)];exact (u.liable.blocks.reach (fun i:Turn P=>i.toLeaf)).pows _
include q h a hs ht hb hr
lemma beginning (i j:Letter F): Soft (sage P) (fun x=> prim (W:=W) (ρ:=ρ) (T:=T) a P q.horizon P.N x i j) := by
    let Q:= prim (W:=W) (ρ:=ρ) (T:=T) a P q.horizon P.N; have hQ x: Mob F (Q x):= laden q h a hs ht hb _ _ _ x.zone x.cap; let M(x:Turn P):=bornM (W:=W) (ρ:=ρ) (T:=T) a q.horizon x.a (P.N x.a) x.b; have hM x : Colfax (slots F) (Pose.weight F) (M x) (primL P x):= (mat_begins a h q hs ht hb _ _ _ x.zone x.head).1
    have hv(i j): Soft (Dove.tide P) (fun x:Turn P=>(noncontract F (M x))⁻¹ i j):=by
        simp_rw [nc_revert (hM _),noncontract]; split
        next he=> exact (runwayBack q u h a hs ht hb hr i j 0 (Nat.zero_le _)).left.reach (fun x:Turn P=>(⟨x.toLeaf,_,_,x.head,le_refl (P.N x.a)⟩: transferPoint W))
        next he=> exact soft_coin (Dove.tide P) _
    -- uniform over all columns separately
    generalize hP:d-Pose.weight F j=n; induction n using Nat.strong_induction_on generalizing j with
    | _ n ih=>
       change Soft (sage P) (fun i'=>Q i' i j); by_cases hp:i=j
       · subst i; simp_rw [(hQ _).unit]; apply soft_coin
       by_cases ht:Pose.weight F j<Pose.weight F i; swap
       · simp_rw [show ∀ x,Q x i j=0 from fun x=> Classical.byContradiction fun h=> ht ((hQ x).raiseS i j h hp).2]; apply soft_coin
       let w(x:Turn P)(k:Letter F):=Q x.ups i k*(noncontract F (M x))⁻¹ k j;let z(x:Turn P):= ∑ k∈Finset.univ.erase j,w x k; have hu x :0≤ primL P x i * (primL P x j)⁻¹ ∧ primL P x i * (primL P x j)⁻¹ ≤Turn.rad 1 x:= by rw [←wide_factor];exact high_up _ i j ht
       refine balance_coin u.liable ?_ ((tallSoft u P i).times (g:=z) ?_) hu ?_
       · simp_rw [show ∀ x,Q (peak P x)=1 from fun x=> bridge_self ..]; exact soft_coin _ _
       · refine soft_bill _ (f:=fun k x=> w x k) ?_; intro k hk; by_cases he:Pose.weight F j<Pose.weight F k
         · exact (town_fold (up_age _ u.liable) (g:=fun i:Turn P=>i.ups) (ih (d-Pose.weight F k) (by have :=weightFits F k;omega) k rfl)).times (hv k j)
         have he' x : w x k=0:= by unfold w; rw [show (noncontract F (M x))⁻¹ k j=0 from Classical.byContradiction fun hz=> he ((nc_mob (hM x) k j hz (Finset.ne_of_mem_erase hk)).2),mul_zero]
         simp_rw [he'];apply soft_coin
       intro x; have he := wheel_visit (B:=Q x.ups) (L:=(W.V x.a).S.block x.b) (hM x) i j; have hx: Q x.bed=wheel F (Q x.ups) ((W.V x.a).S.block x.b) (M x):= contacted q a _ _ _ x.head; rw [hx,he]; change primL P x i*(Q _ _ _*(primL P x j)⁻¹ + z x)= _; ring
end YM.FormalBulk08.Taft
