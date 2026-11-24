import YM.OPE.Log.Plans
import YM.GapsContact.Dusk.Bardo
import YM.GapsContact.Dusk.Treasury
/-! Common pump. See Trace/Noel, OPE/Log/Entrance, Frontier6/Multi/Bonds/Deep. -/
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

private lemma eachTuneD {C:Family G}{W}(H:ColumnSteps C W)(d N p:ℕ)(h:C.ref d ≤ N) (m:ℕ)(hm:C.ref d ≤ m)(he:m<N) : Triangle C.path W m (fun v=> ((C.factory d N p).entries (m+1) v).x) (fun v=> ((C.factory d N p).entries m v).x):=by
  obtain ⟨Z,hZ,hp,hq⟩:= H d N p h
  rw [hZ]
  obtain ⟨T,hT,h⟩:=hq m hm he
  have eq (i) (hv : C.ref d ≤ i) (hu : i ≤ N) : (fun v=> ((Z.draft C.path).inits i v).x) = (Z.tone i).index:= funext ((hp.earned i hv hu).currents)
  rw [eq m hm he.le, eq (m+1) (by omega) he]
  refine ⟨T,hT,h.costs,fun v=>?_⟩; rw [←(hp.earned m hm he.le).currents v]; exact h.error v
include hG
theorem noelD {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    Realm C ∧ GapsContact.Dusk.Feasible C.path.levels ∧
    (∃ W r D, OPE.Log.LogPackage C W r D ∧ GapsContact.Dusk.Shipper C.path r D) ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧MergeProof.East.CompleteWeak C F ∧ Trace.Over.Gallery C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by exact le_rfl
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    exact le_rfl
  obtain ⟨s,T,Y,K,hX,hstage,l,hL,hK⟩:= meranoD hG hp he (fun i=>i+2) (by intro i j h; exact Nat.add_le_add_right h _) (fun i=>by omega) (fun i=>by omega) hE
  let M:=ThroughLaunch.currency s T l
  obtain ⟨⟨P⟩,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨U', -, hu'⟩ := OPE.halo_delay U
  obtain ⟨W₀,hw,hw'⟩:= OPE.Log.aux_delay U'
  obtain ⟨D₀,h₀,hD⟩:= GapsContact.Dusk.reserve W₀
  obtain ⟨V,h₁,hK⟩:= hH Q J₀ D₀
  obtain ⟨D,-⟩:= Bar.exists_above V 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK V (DelayLe.refl _) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,W,c,T,t,S,D',hT,hq,h_col,h_fr,hu⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let Z:= Family.mk (Issue.trail T) (hol G) (Labels.frames G) (localSection G) t S
  change Velour Z (renal B.a) _ D' ∧ VelourArity Z _ _ D' ∧ Pillows Z _ _ D' ∧ LightArity Z _ _ D' ∧ GapsContact.Dusk.Shipper Z.path (mutt B.a fun i=>i+2) D' ∧ (∀ f:Extraction.Order, MergeProof.East.CompleteWeak Z f ∧ Trace.Over.Gallery Z f) at hu
  obtain ⟨hx,hvA,hPll,hLit,hXD,hAll⟩:=hu

  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S,rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hx hq hv hF,hq, Ribbons.fugacious Z hG hx⟩
  have hf:Tendsto (mutt B.a (fun i=>i+2)) atTop atTop:= by
     refine tendsto_atTop_mono (f:=B.a.clock.J) (fun i=>?_) B.a.fits.deep
     change _ ≤ B.a.clock.J (i+1)+2; have ht:= B.a.fits.mono i.le_succ; exact le_trans ht (Nat.le_add_right ..)
  have hRealm: Realm Z:=⟨hv,hq,h_fr,_,_,_,hU,h_col,⟨hx,hPll⟩,hf⟩
  refine ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hc,hF,hW,hRealm,hD V h₁ D Y B.a B.valid, ?_, hπ,fun f hf=>⟨grilled Z hF hU hq hf,hAll f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩
  refine ⟨_, _, _,⟨⟨⟨hU,hx,?_, h_fr, ?_, ?_, hv, hq⟩,hvA⟩, hLit, hw' V (h₀.trans h₁) Y B.a B.valid, hf,?_⟩,hXD⟩
  · intro d N p h m hm hm'; exact (eachTuneD (C:=Z) h_col d N p h m hm hm') -- inspect signature
  · apply hu' V (hw.trans (h₀.trans h₁)) Y B.a B.valid
  · assumption
  intro i; change (B.a.params i).supportExponent=100; rw [params_eq B.valid]; exact hstage.prices _
end YM.PhysicalNext.Repeat.Legato
