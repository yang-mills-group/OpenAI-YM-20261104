import YM.SignedWilsonExpansion.Chron.Membrane
import YM.Next.RANK.Coordinates
import YM.WilsonCoeffUV.Marked.Bounds.Clearance
/-! Nested block digits, reconciliation at finite period and cover. No replacement by first reflected unit.
For gauges at fixed r applications `confirmed` uses actual cells (not a shift of positions). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.WilsonCoeffUV.Mer.Xa
open Wilson Gauge AnalyticNext.QuarticMatch.Sheets Filter Function Matrix Lattice RG Laurent Bloch Metric
open Blue FreeResolvent Work.F08 Bank Soil Exterior Next.Free Tree Precision Power Embroider
open Source Source.Drops Labels Planned.PrimaryIntegral295 Place Carrier WardBin Cosmos Bulb
open Realm Fountain PathCost Embroider.Canvas Shard PowerSeries XSpace
open Supply Ticket Polestar Next.Foundations Patrol Shard.Plan
open Wheel.Mark Next.Rank.Station
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{A:Levels G}{J I:Type*}{e k h m c f v b N i j r n :ℕ}
namespace Ballots
variable (S:Schedule){p:ℕ}{K:Levels G} (Y:J→ Cover)
lemma packetC (L:Side)(u: Cover) : L.val • parentC L u + lift (wrap L u)=u:=congr_arg Prod.fst ((Eq.trans (congr_arg (panel L Unit) ((patchwork (L:=L) (u,())).symm)) (Equiv.apply_symm_apply ..)))
lemma homing {n m:Side}(A:Ratio n m)(u:Cover): wrap n (parentC A.count u)=A.parent (wrap m u):=by
    apply A.embed_injective; rw [A.embed_wrap]; apply add_right_cancel (b:=wrap m (lift (A.residue (wrap m u)))) -- order?
    rw [A.unpack_at,Ratio.residue_wrap,←map_add,packetC]
lemma flats {n m:Side}(A:Ratio n m) : A.parent 0=0:= by rw [← show A.embed 0=0 from A.root.map_zero, Ratio.embed_parent] -- careful rewrites rhs?
-- contact genealogy in exact original family: S.level.block
abbrev postedT (h:i ≤ k)(p): Ratio (S.side i p) (S.side k p):= S.toDepth h p
lemma reunion (S: Schedule)(k p)(w:Site (S.side k p)): (S.toDepth (le_refl k) p).embed w=w:=by unfold Ratio.embed Schedule.toDepth; simp only [tsub_self,Schedule.steps]; rw [show ((1:Side).val :ℕ)=1 from rfl,one_smul,wrap_lift]
lemma reunion' (S:Schedule)(k p)(w:Site (S.side k p)): (S.toDepth (le_refl k) p).parent w=w:=by nth_rw 1 [← reunion S k p w]; rw [Ratio.embed_parent]
lemma carrier_unwrap (z:Cover)(t:i≤k): wrap (S.side i p) (carrierR S i k z)= (postedT S t p).parent (wrap (S.side k p) z):=by
    induction k,t using Nat.le_induction generalizing z with
    | base=> rw [nearR,reunion'];rfl
    | succ k hk ih=> rw [upR S hk, ih, parent_nested (S.toDepth hk p) (S.oneStep k p) _ (S.toDepth_odd ..) (S.oneStep_odd ..),show wrap _ ( parentC (S.block k) z )= _ from homing (S.oneStep k p) z]
lemma now_period (i)(z:Cover): ∀ᶠ p in atTop, lift (wrap (S.side i p) z)=z:=by
    have hy (i:ℕ): StrictMono fun p=>(S.side i p).val:=fun a b h=> Nat.mul_lt_mul_of_pos_right (S.period_strict h) (S.denominator i).property
    let t:ℕ:= Finset.univ.sup fun a=>2*(z a).natAbs
    filter_upwards [ (hy i).tendsto_atTop.eventually (eventually_gt_atTop t)] with p h; rw [lift_eq_iff]; refine ⟨rfl,?_⟩; intro j; have he:2*(z j).natAbs ≤ t := Finset.le_sup (f:=fun j=>2*(z j).natAbs) (Finset.mem_univ j); have hp:t<(S.side i p).val:=h; omega
lemma routeParent (z:Cover)(t:j+1≤k): parentC (S.block j) (carrierR S (j+1) k z)=carrierR S j k z:=by
   let u:= carrierR S (j+1) k z; let v:=carrierR S j k z
   have he (p:ℕ): wrap (S.side j p) (parentC (S.block j) u)=wrap (S.side j p) v:=by
       unfold u v; rw [carrier_unwrap S z ( Nat.le_of_lt t ), parent_nested (S.oneStep j p) (S.toDepth t p) _ (S.oneStep_odd ..) (S.toDepth_odd ..),← carrier_unwrap S z t]; exact homing (S.oneStep j p) _
   obtain ⟨p,h,k⟩:=((now_period S j (parentC (S.block j) u)).and (now_period S j v)).exists; rw [he p,k] at h; exact h.symm
abbrev rolls (Y:J→Site (S.side k p))(t:i≤k): J→Site (S.side i p):= (S.toDepth t p).parent ∘ Y
-- Indirection works for quotient.Test.Problem.Cropped.
def digits (S:Schedule)(p k:ℕ)(Y:J→ Site (S.side k p)) (i:ℕ)(j:J): Site (S.block i) := if hx:i+1≤k then (S.oneStep i p).residue (rolls S Y hx j) else 0
-- exact address as in nested calendar of WilsonIndependentCollarOrdinaryCruise

def routeX (T:∀ i:ℕ,J→ Site (S.block i)): ℕ → ℕ → (J→ Cover)→ J→ Cover
   | 0,_,y=>y
   | d+1,m,y=> routeX T d (m+1) (fun j=>(S.block m).val • y j+ lift ( T m j ))
abbrev partners (i:ℕ): J→ Cover := carrierR S i k ∘ Y -- missing k binder/undeclared?
lemma passport (u:i≤k)(c:ℕ)(w:i+c≤k):
    routeX S (digits S p k (wrap ( S.side k p ) ∘ Y)) c i (partners (k:=k) S Y i)= partners (k:=k) S Y (i+c):=by
    induction c generalizing i with
    | zero=> rfl
    | succ c ih=>
       have H : i+1≤ k:=by omega
       have h(j): ( S.block i ).val • carrierR S i k (Y j)+ lift ( digits S p k ( wrap (S.side k p ) ∘ Y ) i j)=carrierR S (i+1) k (Y j):=by rw [digits,dif_pos H,show rolls S (wrap _ ∘ Y) H j= _ from ( carrier_unwrap (p:=p) S (Y j) H ).symm,← routeParent S (Y j) H]; convert packetC (S.block i) (carrierR S (i+1) k (Y j)) using 1; rw [ Ratio.residue_wrap ]; rfl -- -- check
       rw [show i+(c+1)=i+1+c by omega]; refine Eq.trans (congr_arg ( routeX _ _ c (i+1) ) (funext h)) (ih H (by omega))
lemma confirmed [Finite J](w:r≤c)(t:c≤k): ∀ᶠ p in atTop, let T:= digits S p k (wrap (S.side k p)∘Y);
   rolls S (wrap (S.side k p)∘Y) t=0 → routeX S T (k-c) c (routeX S T (c-r) r 0)=Y:=by
   have a:= w.trans t
   filter_upwards [Filter.eventually_all.mpr (fun j=> now_period S r ( carrierR S r k (Y j)))] with p hp
   intro T x
   have hx: (0:J→ Cover)=partners (k:=k) S Y r:=by
       funext j; change 0= _; unfold partners; rw [Function.comp_apply,←hp j]; apply Eq.symm; rw [carrier_unwrap S _ a,parent_nested (postedT S w p) (postedT S t p) _ (S.toDepth_odd ..) (S.toDepth_odd ..), show (postedT S t p).parent ((wrap _) (Y j))=0 from congr_fun x j] -- missed explicit nested costs
       rw [flats,coat0]
   have ht:c+(k-c)=k:=by omega
   have hw:r+(c-r)=c:=by omega
   rw [hx, passport (p:=p) S Y a (c-r) (hw.le.trans t),hw,passport (p:=p) S Y t (k-c) ht.le,ht]; unfold partners; simp_rw [nearR]; rfl
end Ballots
end YM.WilsonCoeffUV.Mer.Xa
