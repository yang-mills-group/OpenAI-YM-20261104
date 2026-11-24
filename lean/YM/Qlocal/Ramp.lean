import YM.FullVolume.Cross
import YM.Qlocal.Passenger
/-! same witness campaign with prices. accounts Full all usual path/Family.Spec.Targets. -/
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
-- Unconditional existence through the actual Wcmain, ranks and Seed.
variable (hG:G.Simple)
open YM.Qlocal.Schedule
variable {Mψ:YM.Qlocal.Schedule.Goal G} (hmψ: Obtainable Mψ)
include hG hmψ
theorem daggerK {β:ℝ} (h:0<β) : ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(X:Factor A)(Y:ℕ→ℝ)(K:Bid.Worth)(b:Bandage X Y K),
    A.B.a.clock.kernel.penalty=β ∧ Mψ M P A X ∧ Unlatched b (fun _=>1) (fun T t S _ => let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∀ f:Extraction.Order, MergeProof.East.CompleteWeak Z f) := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G β h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= tridentK hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hmψ hE
  let M:=ThroughLaunch.currency s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,hψ,c,hU⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  exact ⟨_,_,_,_,_,_,c,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hψ,hU⟩


open FullVolume
namespace Run
theorem rampK (b : ℝ) (hp : 0<b) : ∃ R : Run G, R.family.path.levels.clock.kernel.penalty = b ∧ Mψ _ _ _ R.kit:=by
   obtain ⟨M,P,A,X,Y,K,bC,hK,hW,h⟩:= daggerK hG hmψ hp
   obtain ⟨T,⟨Z⟩⟩:= rod (by assumption) X
   choose t ht using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   obtain ⟨D,S,hm,hc,hH,hF⟩:= squad (by assumption) bC T Z.receipts t ht
   exact ⟨⟨_,_,_,_,_,_,bC,_,h,T,Z,t,ht,D,S,hm,hH,hF⟩,hK,hW⟩

end Run
end YM.PhysicalNext.Repeat.Legato
