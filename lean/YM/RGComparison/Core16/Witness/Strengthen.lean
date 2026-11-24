import YM.RGComparison.Core16.Unmarked.Hangar
import YM.RGComparison.Core16.Witness.Granted
import YM.RGComparison.Core16.Witness.Demand
import YM.OPE.Replicas.Budget
import YM.UVExtension.Oasis.Wish
import YM.UVExtension.Oasis.Flora
import YM.UVExtension.Upland.Plinth
import YM.MergeProof.South.FinalG
import YM.MergeProof.West.Ozone


/-! Adapter based on Oasis/Hall.lean and OPE/Levy/Path.lean. Strengthen, retain budget. Can pay more beforeL, delays and Wait. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Legato.Core16
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
open UVExtension UVExtension.Harvest
/-! price from same schedule, Barn pins together all projections and histories,
    Transfers peak & radiances, see e.g. Poppy.Fountain. Real offset laws
    on `.yard` are the marked families actually tested. At the center exact
    CLOSED acquisitions via UV-stress.Weak L output. -/
include hG
theorem floweredWith {P_extra:Levels G→Prop} (h_extra:RGComparison.Core16.Witness.Demandable P_extra) (J₁ : RGComparison.Core16.Witness.Rewards G)(hJ: RGComparison.Core16.Witness.Encounters J₁) {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ P_extra C.path.levels ∧ (∃ V₁:RGComparison.Core16.Hangar C hG, RGComparison.Core16.Witness.permits J₁ V₁.R) ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    UVExtension.Oasis.Floral (hG:=hG) C ∧ (∃ W r D,OPE.Package C W r D) ∧ RGComparison.Core16.Witness.CalendarGate C.path.levels ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧_root_.YM.OPE.Levy.Stocked C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
  obtain ⟨k,hb,hp⟩:= YM.Axial.viable G b h
  let v: Orders:= ⟨4,fun i=>6+i,fun i=>2+i,fun i=>100+i⟩
  have hE (i:ℕ): 100 ≤ v.supportExp i:= by change (100:ℝ) ≤ 100+i; simp
  have he : Draft v:= by
    refine ⟨le_rfl,fun i j hij=> Nat.add_le_add_left hij 6,fun i j hij=> Nat.add_le_add_left hij 2,fun i j hij=>?_,fun i=> lt_of_lt_of_le (by norm_num) (hE i),fun i=>by change _ ≤6+i; omega,fun i=>by change _≤2+i; omega⟩
    change (100:ℝ)+i≤100+j; gcongr
  obtain ⟨s,T,Y,K,hX,H,l,hL,hK⟩:= bulwark hG hp he (fun _=>1) (fun _ _ _=>le_rfl) (fun _=>le_rfl) J₁ hJ hE
  let M:=UVExtension.Case.provider s T l
  obtain ⟨P,h3,hHead⟩ := RGComparison.Core16.Witness.lintel M.p hG
  obtain ⟨-,H⟩:= hK l le_rfl
  let Q (i j:ℕ): JointLoad.Clockwork.Menu:= ⟨Push.SectorMeasure.Chi.canonical,1,0,0,0,0,0,0,one_pos,le_rfl⟩
  let J₀ (i j:ℕ):JointLoad.Folio.Aux:=⟨40,1,1,le_rfl⟩
  let E : Next.Scheduling.Exchange:=⟨0,0,1,1,1,0,0,by norm_num⟩
  obtain ⟨w,h⟩:= H P
  obtain ⟨F,hF⟩:= h w le_rfl (fun _ _=> ⟨1,1,1,1,le_rfl,zero_lt_one,zero_lt_one⟩) (fun _ _=> E)
  obtain ⟨θ,-,hH⟩:= hF _ (fun _=>one_pos)
  let U: Delays θ:=⟨fun _=>0,fun _ _=>0,fun _=>1,fun _=>1⟩; obtain ⟨V,h₁,hK⟩:= hH Q J₀ U
  obtain ⟨V',hV,hG₀⟩:= RGComparison.Core16.Witness.buy_calendar V h3
  obtain ⟨Vplus,hV',hV₀⟩:= OPE.halo_delay V'; obtain ⟨Vextra,hV_plus,hV_extra⟩:= h_extra _ _ _ Vplus
  obtain ⟨D,-⟩:= Bar.exists_above Vextra 2; let I:Wait D:= ⟨fun _=>0,fun _ _=>0,fun _=>by simp,0⟩
  obtain ⟨Y,-,H⟩:= hK Vextra (hV.trans (hV'.trans hV_plus)) D I
  obtain ⟨a,ha,hp⟩:= Wait.engine Y hG; obtain ⟨X,B,hB,R,⟨hW1,hW2,hW3,hW4,hW5,hWW⟩,c,T,t,S,Hx,Hk,hT,hq,hu,hD,h_lease,h_rate,⟨hh',hH,h_Φ,h_sh⟩,hfr,hVa,hE⟩:= H Y le_rfl le_rfl le_rfl a ha hp
  let V:= Mast.centerB S Hx; let W:=Mast.cellar S c Hx t Hk; let S':= Mast.Cellar.gate (Mast.roseA S) W
  let Z:= Family.mk (Issue.trail V) (hol G) (Labels.frames G) (localSection G) t S'
  obtain ⟨hc,hF,hQ,hU,hW,B₀,-,-,K₀,F₀,L,-,H⟩:=hT.reception
  have hv:Ribbons.Created Z:= ⟨_,t,S',rfl⟩
  have hπ:Acme.Aroma Z:= ⟨Ribbons.laurelE Z hG hU hu hq hv hF,hq, Ribbons.fugacious Z hG hu⟩
  have head:= hHead B.a B.valid.stage B.valid.lengths; have gate : OPE.Package Z _ (mutt B.a (fun _=>1)) _:=⟨⟨hU,hu,RGComparison.Core16.Witness.framed S c (Mast.roseA S) Hx Hk head,hfr,hV₀ Vextra hV_plus Y B.a B.valid,hQ,hv,hq⟩, hVa⟩
  let Hx₁:RGComparison.Core16.Hangar Z hG:=⟨M,P,_,R,S,T,Hx,t,_,_,c,W,Oasis.spring Hx,rfl⟩
  have hE₁ :RGComparison.Core16.Witness.permits J₁ Hx₁.R:= hWW
  exact ⟨_,(congr_arg KernelChoices.penalty (B.valid.kernel.trans hX)).trans hb,hV_extra Vextra (.refl _) _ Y B.a B.valid,⟨Hx₁,hE₁⟩,hc,hF,hW,Oasis.survives W Hx hD hQ hh' hH (hB.symm ▸ h_Φ) h_sh h_lease h_rate hT hu, ⟨_,_,_,gate⟩,hG₀ _ (hV'.trans hV_plus) Y B.a B.valid, hπ,fun f hf=>⟨grilled Z hF hU hq hf,hE f⟩,fun f=>by obtain ⟨g,A,L,R,z,T,E,h,hp⟩:= H f; exact ⟨g,A,L,R,T,E,hp⟩⟩

theorem flowered {b:ℝ} (h:0<b) : ∃ C:Family G, C.path.levels.clock.kernel.penalty=b ∧ Spec.Calibrated C ∧ C.Makes ∧ Extraction.Wcmain C ∧
    UVExtension.Oasis.Floral (hG:=hG) C ∧ (∃ W r D,OPE.Package C W r D) ∧ RGComparison.Core16.Witness.CalendarGate C.path.levels ∧ Acme.Aroma C ∧ (∀ F:Extraction.Order, Cells.CellHyp C F → Grill C F∧_root_.YM.OPE.Levy.Stocked C F)∧∀ f:Extraction.Order, ∃ (g:Extraction.Order) (A:Table C.book) (L:ℕ→Table C.book) (R:Bin A) (T:Table C.book) (E:DiffPlan T), Next.Extract.Base C (f.refine g) A L R T E ∧ ∃ s:Spec.Seed C (f.refine g) T,Maxwell.Ranks T s.kernel.spin := by
    obtain ⟨C,hB,-,-,hc⟩:= floweredWith hG RGComparison.Core16.Witness.free_node (RGComparison.Core16.Witness.nullR G) RGComparison.Core16.Witness.minimum h
    exact ⟨C,hB,hc⟩
end YM.PhysicalNext.Repeat.Legato.Core16
