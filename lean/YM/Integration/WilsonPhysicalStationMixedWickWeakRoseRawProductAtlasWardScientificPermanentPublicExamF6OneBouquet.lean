import YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6ScalarBouquets
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OneBouquet
open Lattice Maxwell Maxwell.Free XSpace XSpace.Structure1 XSpace.Normalize XSpace.Cirrus
open FVA2 FVA2.Register MS MS.Native MS.Plane MS.Book MS.Menus MS.Tide MS.Fleet MS.Swirl MS.Swirl.Near MS.Rake MS.Land
open Koszul Plane Landau Tone Frame Lattice City Latch Job Detect Tone Momentum Heat Orbit Cog Orbit.LogReal Book Convolve Program Native Wilsonian
open Draft Paint Orient Cylinder Lab Menus Fleet Puff Puff.Actors Puff.Engine Puff.Mom Puff.SplitP Puff.Dynamics
open SpaceOut Swirl Swirl.Near FVA2.Arrival FVA2.Scale Filter Set Function
open scoped Classical BigOperators Topology
open Position Position.Axes

open MS.Puff MS.Puff.Stencil Finset Koszul Book Book.Convolve MS.Puff.Actors MS.Puff.Engine MS.Puff.Dynamics MS.Puff.SplitP
variable {W E : Type} [DecidableEq W] [AddCommGroup E] [Module ℂ E] (M:MS.Puff.Actors E) {F:Finset W→E}
local notation "P"=> MS.Puff.SplitP.marked W
local notation "T"=> M.stack (MS.Puff.SplitP.marked W)
local infixl:70 " ⋆ "=> M.core
lemma pay0 {w:W} {f:Finset W→ E} (u: Finset W)(h:w∉u)(hp:∀ u:Finset W,w∈u → u.card≠1→ F u=0) : (∑ i∈ subs u, F (insert w i.1) ⋆ f i.2)= F {w} ⋆ f u:= by
   rw [ sumS (fun a b=>F (insert w a) ⋆ f b) u, Finset.sum_eq_single_of_mem ∅ (Finset.empty_mem_powerset _) ]; · simp
   intro a ha he; rw [ hp (insert w a) (Finset.mem_insert_self ..) ?_,map_zero,LinearMap.zero_apply ]; rw [ Finset.card_insert_of_notMem (fun p=>h ( ( Finset.mem_powerset.mp ha ) p )) ]; obtain hz:= Finset.card_pos.mpr ( Finset.nonempty_iff_ne_empty.mpr he ); omega
variable (hx:∀ p,F p∈M.guard)
include hx
lemma wagt (p:Finset W)(i:W)(he:i∉p)(j:ℕ)(hp:∀ u:Finset W,i∈u → u.card≠1→F u=0): (T).wages F (j+1) (insert i p) = F {i} ⋆ ( (T).wages F j p ):= by
   let t:=F {i}; have ht u (k:ℕ)(l:Finset W): F u ⋆ (t ⋆ ((T).wages F k l))=t ⋆ ( F u ⋆ ((T).wages F k l)):= mmc ( hx u ) (hx {i}) _; induction j generalizing p with
   | zero=>
      rw [ nextW (M:=T) (n:=0),Pi.smul_apply,firstW,(T).identityR,Nat.cast_zero, zero_add, inv_one, one_smul ]; by_cases h:p.Nonempty
      · have hv:=hp (insert i p) (Finset.mem_insert_self ..) (by rw [ Finset.card_insert_of_notMem he ]; obtain hv:=Finset.card_pos.mpr h; omega); rw [hv, show (T).unit p=0 from Eq.trans (congr_fun firstW p).symm (spare M h ( F:=F )),map_zero]
      rw [ Finset.not_nonempty_iff_eq_empty.mp h, show insert i (∅:Finset W)={i} from rfl]; unfold Actors.stack; dsimp only; rw [ SplitP.refineV,if_pos (show (∅:Finset W)=(P).origin from rfl), M.identityR ]
   | succ j ih=>
      rw [ nextW (M:=T) (n:=j+1), Pi.smul_apply ]; change _ • (∑ x∈ subs (insert i p), _)= _; rw [ ins he (fun a b=> F a ⋆ ((T).wages F (j+1) b)), pay0 M p he hp ];
      have hz : (∑ x ∈subs p,F x.1 ⋆ ((T).wages F ( j+1 ) (insert i x.2)))=t ⋆ (( (T).core F ((T).wages F j) ) p) := by change _ = t ⋆ ((P).Lift M.core _ _ _); rw [ (P).loan,map_sum]; exact Finset.sum_congr rfl fun r hr=> (congr_arg ( F r.1 ⋆ · ) ( ih r.2 (fun v=> he ( ( cards.mp (( P).sym.mp hr ) ).1 v ) ) ) ).trans (ht r.1 j r.2)
      rw [ hz,nextNF (M:=T) j, Pi.smul_apply,map_smul, inv_smul_eq_iff₀ ( zeroN' (j+1) ) ]; push_cast; module
theorem original (S: Finset W)(w:W)(he:w∉S)(hp:∀ u:Finset W,w∈u → u.card≠1→F u=0) : M.Cheer P F (insert w S) =F {w} ⋆ M.Cheer P F S:= by
   unfold Cheer Actors.cheers; simp only [ Finset.sum_apply, show ∀ p:Finset W,(P).grade p=p.card from fun _=>rfl,Finset.card_insert_of_notMem he ]; -- unfold M algebra! ptype
   rw [ Finset.sum_range_succ', spare M (Finset.insert_nonempty ..), add_zero, map_sum ]; exact Finset.sum_congr rfl fun i _=> wagt M hx S w he i hp
end YM.Integration.WilsonPhysicalStationMixedWickWeakRoseRawProductAtlasWardScientificPermanentPublicExamF6OneBouquet
