import YM.OPE.Compatible.Niche.Nook
import YM.OPE.Compatible.Niche.Tech
import YM.OPE.Rough.Supply
import YM.OPE.Compatible.Calendars.Repeat
/-!
# Augmented supplies on one construction

Acquire or consume extra quantitative certificates. Here hypotheses/function
inputs still specify which purchases are needed; `FinalBeam` / `Clients.Jacob`
for actually obtaining all the properties needed for the extension on the same
construction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
variable {G:Gauge}
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent

variable (hG:G.Simple)
open OPE OPE.Owl
set_option quotPrecheck false
include hG
-- Chronology gift chooses instance; late delays STILL may be boosted for EOM proof
lemma epigram {b:ℝ} (h:0<b) (a:Axis): ∃ (s:Sheet G)(p:MapPrices)(H:Votive.Sponsor G)(K:Votive.Seasons H)(X:Stroke.PriceBook (chart_ok G) K)(Y:ℕ→ℕ)(U:Rolls (ThroughLaunch.raise s Y))(Px:Spells.Pad G)(D:Desk (ThroughLaunch.raise s Y) X a hG) (T:Protection U),s.kernel.penalty=b ∧ ∃ V:Delays T,∀ Z: Delays T, DelayLe V Z→∀ (B : Bar Z) (W:Wait B), ∃ F: Wait B,(W.readyHere≤ F.readyHere ∧ W.minLength ≤ F.minLength ∧ W.window ≤ F.window)∧∀ W':Wait B, F.readyHere≤W'.readyHere→F.window≤ W'.window→F.minLength≤ W'.minLength→ ∀ (q: Levels G),Paid W' q→AsDivisors q.S→∃ (P :PostCost U)(hP:Stock.Priced Z)(D0:Directed G W' (chart G) (ThroughLaunch.bearing s p) P),D0.a=q ∧ ∃ _C:Fuel hG s p H K a X Y U Px D (Alloy.mk P T Z B W' hP D0), True:=by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun _=>100⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= le_rfl
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    exact le_rfl
  obtain ⟨s,T,P,A,F₀,Y,K,hX,hR,hh_stage,l,hL,hK⟩:= producerB hG hp he (fun i=> i+1) (fun i j hij=> Nat.succ_le_succ hij) (fun i=> by omega) hE
  let τ(i:ℕ):= l i+16; let M:=ThroughLaunch.currency s T τ
  obtain ⟨⟨D⟩,H⟩:= hK τ (fun i=> Nat.le_add_right _ _) a; obtain ⟨P',hZ⟩:= D.enrich; let B:=Classical.choice (Spells.curtainL G)
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H D P' B hZ
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩
  obtain ⟨V,h₁,b,hK⟩:= hH Q J₀ U
  refine ⟨s,T,P,A,F₀,τ,P',B,D,θ,hX ▸ hb,V,fun Z hZ B W=>?_⟩; obtain ⟨F',hp,H⟩:= hK Z hZ B W; refine ⟨F',hp,fun W' ha hm hv q h hx=>?_⟩; obtain ⟨hz,S,Hm,R,-,T0,C,Q,K,d,hF⟩:= H W' ha hm hv q h hx; refine ⟨_,_,_,Hm, ⟨_,_,R,T0,C,Q,K,d,hF,fun j=>(hh_stage.prices j), fun i=>le_trans (Nat.le_add_left 16 (l i)) (?_),hR⟩,trivial⟩; exact (P'.large i).need
end YM.PhysicalNext.Repeat.Legato
