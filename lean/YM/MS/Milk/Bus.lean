import YM.MS.Milk.Magic
import YM.MS.Milk.Mural
import YM.MS.Milk.Outfit
import YM.Next.RANK.GaussTags
/-!
# Multi-standard.Even connected equation only.Expose operations.Near past estimate when all distinct, theorem.Probewise identity. -/
set_option autoImplicit false
noncomputable section
namespace YM.MS.Milk
open Set Function Filter Finset Metric MeasureTheory Real
open Plane Koszul Landau Detect Heat Tone Latch Latch.Job Rake Orbit Breeze Book Convolve Flux
open Analysis Submodule InnerProductSpace City Next.Rank Next.Rank.Normal Theater Drops Maxwell Local.Physical
open Labels
open Complex (I)
open scoped Topology ContDiff BigOperators RealInnerProductSpace
variable {A X W:Type}{G:Gauge} [LinearOrder W]{n d r:ℕ}{s:ℝ}{U:W→ℝ}{P:W→Pol G}
local infix:70 " ⋆ "=> product (field Landau.parity)
local notation "Φκ"=> field (P:=QP) ( Landau.parity ( C:=G.ColorIndex ) ( A:=Axis ) )
open Puff SplitP Puff.Log Engine Dynamics Actors Swirl
variable (x:W→E4)(hp: Injective x)(u:W→Pol G)
set_option quotPrecheck false
local notation "M"=> ASeq G
local notation "sU"=> marked W
lemma nearT (b:Finset W) : Clean (LogU x hp u b - Sent x u b):= by
    let t:= MeterU x hp u; let y:=Meter0 x u; rw [ ← restG x u ]; change Clean (Meter M sU t b- Meter M sU y b ); let S:=Meter M sU t; let Y:= Meter M sU y
    have he i: Giant ( y i ):= aim_G (Forum G x) _ ( economics x hp|>.2.1 ); have hx i: Giant ( t i ):= aim_G (Forum G x) _ ( economics x hp|>.1 ); have hu i: Clean ( t i-y i ):= near_home x hp _
    have hk i: S i∈ LeaseL G:= MeterIN M sU t ( LeaseL G ) (fun i hi j hj=> trunk_G (U:=i) ( V:=j ) hi hj ) hx i;
    induction h:(sU).grade b using Nat.strong_induction_on generalizing b with
    | h k ih=>
       rw [ spawn, spawn M sU y b ]; -- second maybe first rewrites both sides if syntact
       rw [ ← smul_sub, issue,issue, cloak,cloak ]; rw [show ((sU).grade b:ℂ) • t b-_-( _ • y b- _ ) = _ from (sub_sub_sub_comm ..) ]; rw [ ← smul_sub, ← Finset.sum_sub_distrib ]; refine Clean.smul (by refine ( road G ).sub_mem ( Clean.smul ( hu b ) _ ) ?_; apply cPack; intro i hi; exact subtract_c ( U:= α sU i.1 • S i.1 ) ( P:= α sU i.1 • Y i.1 ) ( V:=t i.2 ) ( Q:=y i.2) (by rw [← smul_sub]; exact Clean.smul ( ih _ (h ▸ keep sU hi ) i.1 rfl ) _) ( hu i.2 ) ( Giant.smul (hk _) _ ) ( he _ )) _
lemma birthQ (p:Finset W)(h:2≤p.card): Clean ( LogU x hp u p ):= by obtain hv:=nearT x hp u p; rwa [ sent_e x u _ (by omega),sub_zero ] at hv
lemma horizonT (s:Finset W)(p:Legs ( Lane4 G )): Tendsto (fun y=> MeterU x hp u s y p ) atTop (𝓝 ( Tint ( Forum G x ) (entry G x hp) (pot s u) p )):= last atTop ( fun i j=> by
    simp only [ Taxi, entry ]; apply ( show Tendsto _ _ _ from ?_ ); simpa only [sub_zero] using tendsto_const_nhds.sub (eitherI ( ( ClockCert i.2 j.2 ).wind ( x i.1-x j.1 ) ) ( by unfold Drops.sizeL; omega ) ) ) _ p
end YM.MS.Milk
