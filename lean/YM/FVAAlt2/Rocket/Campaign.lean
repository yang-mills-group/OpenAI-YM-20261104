import YM.FullVolume.Cross
/-!
# Choose plateau lengths on the **same** Run. No second Issue, no Betas matched across different planners

Endpoint generalizes `dagger` with specific extra tickets. Same UV theorem inputs of
 `FullVolume.Cross.realized`; not implying completion of e.g. coadmissions with the
 later Jewel package. Keeps apparatus/policy choices on this Run.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.FVAAlt2
open Function Filter Set Lattice RG RG.Shoot Wilson Precision RG.Supply Input Org Extra.Histories Source
open JointLoad JointLoad.Heir JointLoad.Heir.Suite JointLoad.Psalm Clockwork
open AnalyticBridge VerifiedReset Collection Quotes Next.Scheduling Extra.Iteration Song Geo
open ThroughLaunch Roof Push.PriceCompiler Further.StrongStartup SectorNext
open WilsonStartup Progress.DirectedRecipe Time Next.Foundations UVNext.CouplingReset
open Cub Circlet Graces Roost Planned.GuardedAtom Bandage
open InteractingRank Next.Rank Next.Rank.Tapes RankCovariance PhysicalNext.InteractingRank.Soft FullVolume
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff Interval InnerProductSpace
open Next.Extract Dash
open YM.MergeProof MergeProof.Accent
variable {G:Gauge}
-- general onto. add Min floor L at each smoothing index, windows REG. HasY payable independently.
def Windows (a:Levels G)(μ:ℕ→ℕ)(q: ℕ→ Side→ℕ) := (∀ i,μ i≤ (a.clock.factor i).val) ∧ ∃ d, ∀ i≥d, ∃ k, q i (a.clock.factor i) ≤ k ∧ ∀ j, k-q i (a.clock.factor i) ≤ j → j≤ k+q i (a.clock.factor i) → a.clock.J j=i
lemma buys (hG:G.Simple){Kᵣ:KernelChoices}(hK₀:∀ P:Patch,P.Branches Kᵣ G) (N₀:ℕ→ℕ)(q:ℕ→ Side→ℕ): ∃ R : Run G, R.family.path.levels.clock.kernel= Kᵣ ∧ Windows R.family.path.levels N₀ q:=by
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,τ,hL,hK⟩:= trident hG hK₀ he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) hE
  let l i:= max (N₀ i) (τ i)
  let M:=ThroughLaunch.currency s T l
  obtain ⟨⟨P⟩,H⟩:= hK l (fun i=>le_max_right ..)
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun j _=>q j (P.L j),fun _=> tendsto_const_nhds.div_atTop tendsto_id,0⟩
  obtain ⟨T',⟨-, -,hw⟩,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine T' hG; obtain ⟨X,B,hB,R,W,c,hU⟩:= H T' le_rfl le_rfl le_rfl a ha hp
  obtain ⟨T₀,⟨Z⟩⟩:= rod (G:=G) hG R
  choose t ht using fun d:ℕ=> (B.a.fits.deep.eventually_ge_atTop (d+3)).exists
  obtain ⟨D',S',hm,hc,hH,hF⟩:= squad hG c T₀ Z.receipts t ht
  refine ⟨⟨_,_,_,_,_,_,c,_,hU,T₀,Z,t,ht,D',S',hm,hH,hF⟩,B.valid.kernel.trans hX, ?_⟩
  change Windows B.a N₀ q; unfold Windows; rw [hB, ha.lengths]; refine ⟨ fun i=> ?_,(raise s l).first,?_⟩
  · exact le_trans (le_max_left (N₀ i) (τ i)) (P.large i).need
  intro i hi; obtain ⟨k,-,h,h'⟩:= ha.run i hi
  refine ⟨ k,(hw i _).trans h,fun j hj hl=> h' j ?_ ?_ ⟩
  change k-T'.window i _≤j
  · exact (Nat.sub_le_sub_left (hw i _) k).trans hj
  exact hl.trans (Nat.add_le_add_left (hw i _) _)
end YM.PhysicalNext.Repeat.Legato.FVAAlt2
