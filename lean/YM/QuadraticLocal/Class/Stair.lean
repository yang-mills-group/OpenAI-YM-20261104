import YM.QuadraticLocal.Found.Mission

/-! # Dashboard order and exponent gauges when starting this campaign

Expose them all prior to any t.N or height reader call.
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
variable {φ:ℕ→ℕ}(Θ:VowsR.LawScroll G φ) (hG:G.Simple){K:KernelChoices}(hK :∀ p : Patch,p.Branches K G){v:Orders}(hp:ThroughLaunch.Draft v)(Q:ℕ→ℕ) (hQ:Monotone Q)(hQ':∀ i,1 ≤ Q i)

include hp hG in
theorem dagger_aligned {β:ℝ} (h:0<β) (hE:∀ i,100 ≤ v.supportExp i): ∃ (M:Metals G)(P:Rolls M.p)(A:Alloy M P)(X:Factor A)(Y:ℕ→ℝ)(K:Bid.Worth)(b:Bandage X Y K),
    A.B.a.clock.kernel.penalty=β ∧ VowsR.Sanctuary Θ X ∧ WithStage M.p v ∧ Unlatched b (fun _=>1) (fun T t S _ => let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S; ∀ f:Extraction.Order, MergeProof.East.CompleteWeak Z f) := by
  obtain ⟨k,hb,hk⟩:= YM.Axial.viable G β h
  obtain ⟨s,T,Y,K,hX,Hstage,l,hL,hK⟩:= trident_B Θ hG hk hp (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
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
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,hU⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  exact ⟨_,_,_,_,_,_,c,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,W.2.2.2.2.2, show WithStage (ThroughLaunch.currency s T l).p v from ⟨Hstage.first,Hstage.jets,Hstage.powers,Hstage.prices⟩,hU⟩


open FullVolume


theorem Run.attain_aligned (h : G.Simple) (v : Orders) (hd : ThroughLaunch.Draft v) (b : ℝ) (hp : 0<b)(hE:∀ i,100 ≤ v.supportExp i) : ∃ R : Run G, R.family.path.levels.clock.kernel.penalty=b ∧ VowsR.Sanctuary Θ R.kit ∧ WithStage R.metals.p v:=by
   obtain ⟨M,P,A,X,Y,K,bC,hK,hξ,hS,h'⟩:= dagger_aligned Θ h hd hp hE
   obtain ⟨T,⟨Z⟩⟩:= rod (by assumption) X
   choose t ht using fun d:ℕ=> (A.B.a.fits.deep.eventually_ge_atTop (d+3)).exists
   obtain ⟨D,S,hm,hc,hH,hF⟩:= squad (by assumption) bC T Z.receipts t ht
   exact ⟨⟨_,_,_,_,_,_,bC,_,h',T,Z,t,ht,D,S,hm,hH,hF⟩,hK,hξ,hS⟩


end YM.PhysicalNext.Repeat.Legato
