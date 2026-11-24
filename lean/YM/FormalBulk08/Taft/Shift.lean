import YM.FormalBulk08.Taft.Stage
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
include q u h a hs ht hb hr hp
lemma tracing (i j:Letter F): Pact (sage P) (Degree targetPower) (fun x=> prim (W:=W) (ρ:=ρ) (T:=T) a P q.horizon P.N x i j) (fun x=> prim (W:=W) (ρ:=ρ) (T:=T) a P q.horizon C.N x i j) := by
    let Q:= prim (W:=W) (ρ:=ρ) (T:=T) a P q.horizon P.N; have hQ x: Mob F (Q x):= laden q h a hs ht hb _ _ _ x.zone x.cap; let M(x:Turn P):=bornM (W:=W) (ρ:=ρ) (T:=T) a q.horizon x.a (P.N x.a) x.b; have hM x : Colfax (slots F) (Pose.weight F) (M x) (primL P x):= (mat_begins a h q hs ht hb _ _ _ x.zone x.head).1
    let Z:= prim (W:=W) (ρ:=ρ) (T:=T) a P q.horizon C.N; have hZ x: Mob F (Z x):= laden q h a hs ht hb _ _ _ x.zone (x.cap.trans (hp _)); let N(x:Turn P):=bornM (W:=W) (ρ:=ρ) (T:=T) a q.horizon x.a (C.N x.a) x.b; have hN x : Colfax (slots F) (Pose.weight F) (N x) (primL P x):=(mat_begins a h q hs ht hb _ _ _ x.zone (x.head.trans_le (hp _))).1
    let qL(i j):= beginning q u h a hs ht hb hr P i j; have qR(i j): Soft (sage P) (fun x=> Z x i j):=(beginning q u h a hs ht hb hr C i j).reach (raiseD P C hp)
    have hv:= nonroad (τ:=Dove.tide P) (δ:=Dove.bump targetPower) hM hN (fun i j=>(runwayBack q u h a hs ht hb hr i j 0 (Nat.zero_le _)).link (fun x:Turn P=>(⟨x.toLeaf,P.N x.a,C.N x.a,x.head,hp _⟩:transferPoint W)))
    generalize hP:d-Pose.weight F j=n; induction n using Nat.strong_induction_on generalizing j with
    | _ n ih=>
       change Pact _ _ (fun i'=>Q i' i j) (fun i'=> Z i' i j); by_cases ht:i=j; · subst i; simp_rw [(hQ _).unit,(hZ _).unit]; apply Pact.coin
       by_cases hb':Pose.weight F j<Pose.weight F i; swap
       · simp_rw [show ∀ x,Q x i j=0 from fun x=> Classical.byContradiction fun h=> hb' ((hQ x).raiseS i j h ht).2, show ∀ x,Z x i j=0 from fun x=> Classical.byContradiction fun h=> hb' ((hZ x).raiseS i j h ht).2]; apply Pact.coin
       let w(x:Turn P)(k:Letter F):=Q x.ups i k*(noncontract F (M x))⁻¹ k j;let z(x:Turn P):= ∑ k∈Finset.univ.erase j,w x k; let m(x:Turn P)(k:Letter F):=Z x.ups i k*(noncontract F (N x))⁻¹ k j; let t(x:Turn P):=∑ k∈ Finset.univ.erase j,m x k
       have hu x :0≤ primL P x i * (primL P x j)⁻¹ ∧ primL P x i * (primL P x j)⁻¹ ≤Turn.rad 1 x:= by rw [←wide_factor];exact high_up _ i j hb'
       have hy:Pact (Dove.tide P) (Dove.bump targetPower) z t:= by
           refine pact_sums _ (f:=fun k x=> w x k) (g:=fun k x=>m x k) ?_; intro k hk; by_cases he:Pose.weight F j<Pose.weight F k
           · exact (Pact_lift (g:=fun i:Turn P=>i.ups) (up_age _ u.liable) (ih (d-Pose.weight F k) (by have :=weightFits F k;omega) k rfl) (fun _=>le_rfl)).times (hv k j)
           have he' x : w x k=0:= by unfold w; rw [show (noncontract F (M x))⁻¹ k j=0 from Classical.byContradiction fun hz=> he ((nc_mob (hM x) k j hz (Finset.ne_of_mem_erase hk)).2),mul_zero]
           have ht' x : m x k=0:= by unfold m; rw [show (noncontract F (N x))⁻¹ k j=0 from Classical.byContradiction fun hz=> he ((nc_mob (hN x) k j hz (Finset.ne_of_mem_erase hk)).2),mul_zero]
           simp_rw [he',ht'];apply Pact.coin
       refine ⟨qL i j,qR i j, vanishing_coin u.liable (by norm_num [targetPower]) ((((qL i j).plus (qR i j).minus).below (g:=fun x=>Q x i j-Z x i j) (fun x=> by rw [sub_eq_add_neg])).reach (peak P)) (((Pact.constant (tallSoft u P i)).times hy).blur) hu ?_⟩
       intro x; have he := wheel_visit (B:=Q x.ups) (L:=(W.V x.a).S.block x.b) (hM x) i j; have hp' := wheel_visit (B:=Z x.ups) (L:=(W.V x.a).S.block x.b) (hN x) i j; have hx: Q x.bed=wheel F (Q x.ups) ((W.V x.a).S.block x.b) (M x):= contacted q a _ _ _ x.head; have hk:Z x.bed=wheel F (Z x.ups) ((W.V x.a).S.block x.b) (N x):= contacted q a _ _ _ (x.head.trans_le (hp _)); change Q _ i j - Z _ i j=_; rw [hx,he,hk,hp']; change primL P x i*(Q x.ups _ _*(primL P x j)⁻¹ + z x)-primL P x i*(Z x.ups _ _*(primL P x j)⁻¹+t x)= _*(_-_)+(_-_);ring
end YM.FormalBulk08.Taft
