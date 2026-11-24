import YM.OPE.Rough.Supply
import YM.OPE.Loom.ExtraDelays
/-!
# Construct Wilson & continuum supplies along one family

Adapted from YM/OPE/Rough/Supply.lean, retaining its architecture. Stronger ports & receipts, same
chosen RG construction. Now includes `Sharper` and its extra post-L delay. No logarithmic endpoint inputs assumed.
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
-- Unconditional existence through the actual Wcmain, ranks and Seed.
variable (hG:G.Simple)
include hG
/-- Receipts hold on THIS compiler / path. Independent of all matching estimates. -/
structure Sharper (C:Family G) (W:Bid.Worth)(r:ℕ→ℕ)(D:∀ N p m:ℕ,m<N→GaugeDoor (C.path.rep N p (m+1)) (C.path.rep N p m)) : Prop extends OPE.Package C W r D where
    improves m N j d (he:C.ref d ≤ m) (hp:m<N) : Throws C.path N j m (D N j m hp) (hol G) (localSection G d) (C.path.levels.clock.hatBeta (m+1))
    price i : (C.path.levels.budget i).supportExponent=100
    limit_r : Tendsto r atTop atTop

-- build with same Bourse producer
 theorem loom_columns {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    (∃ W r D, Sharper C W r D) ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun _=>100⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= le_rfl
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    rfl
  obtain ⟨s,T,Y,K,hX,WStage,l,hL,hK⟩:= himalayas_columns hG hp he (fun j=>j+1) (fun _ _ h=>Nat.succ_le_succ h) (fun _=>Nat.le_add_left ..) hE
  let M:=ThroughLaunch.currency s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨U', -, hu'⟩ := OPE.halo_delay U
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ U'
  obtain ⟨V',hp₂,hp₄⟩:= subsidize_feasible V
  obtain ⟨D,-⟩:= Bar.exists_above V' 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V' hp₂ D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,D',hT,hq,h_col,h_fr,hu⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
  change Velour Z (renal B.a) _ D' ∧ VelourArity Z _ _ D' ∧ (∀ f:Extraction.Order,MergeProof.East.CompleteWeak Z f) at hu
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu.1 hq hv hF,hq, Ribbons.fugacious Z hG hu.1⟩ -- fix argument order
  refine ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW, ?_, hπ,fun f hf=>⟨grilled Z hF hU hq hf,hu.2.2 f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
  · refine ⟨_, _, _, ⟨⟨hU, hu.1, fun d N p hn m hm h => h_col d N p hn m hm h, h_fr, ?_, ?_, hv, hq⟩, hu.2.1⟩, ?_,?_,?_⟩
    · apply hu' V' (h₁.trans hp₂) Y B.a B.valid
    · assumption
    · exact fun m N j d=> further hG c _ T _ _ D' hT (hp₄ V' (DelayLe.refl _) Y _ B.valid) m N j d
    · intro i; change (B.a.params i).supportExponent=100; rw [params_eq B.valid]; exact WStage.prices _
    exact ((tendsto_add_atTop_nat 1).comp (B.a.fits.deep.comp (tendsto_add_atTop_nat 1)))
end YM.PhysicalNext.Repeat.Legato
