import YM.Integration.WilsonIndependentCapturedPages
import YM.Integration.WilsonReceivedChronologicalRosterOuterHomeMesh
import YM.SignedWilsonExpansion.Vault.Amber
/-! At all scales, pay Reporter.f & visit common capture date.
  Corresponding ONLY to Stop/Diary previously appointed. The stopping time does
 not peep at forecasts. Authority includes all period tapes & both poses. -/
set_option autoImplicit false
set_option maxHeartbeats 310000
set_option maxRecDepth 4000
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.Election.VaultM.Till
open Function Finset Set Filter MeasureTheory Lattice RG Wilson Source Labels Extra.Histories -- Motion
open Extraction Table Spec Trace.Pilot PhysicalNext.Repeat.Legato Trace.Physical.GermGraph
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonMeasuredPublicEntrancePanel (Panel)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonOriginalGeneralRosterFare (rotation debit)
open WilsonMeasuredPublicEntranceCellWords (physical submitted)
open WilsonMeasuredPublicEntranceTransferSubmitted (vector)
open WilsonMeasuredPublicEntranceTransferWord (field price)
open RG05Readout RG05Readout.Address RG05Readout.Records Marker Cells HeartT HeartT.Spritz
open WilsonReflectedPublicOrientedFaces (displayed)
open PRAY
open SignedWilsonExpansion Homes Purchases UVClock Schedules StageG Camera SignedWilsonExpansion.Vault Asymptotics
open XSpace FVA2 FVA2.Register Dancer Dancer.Fort Dancer.Stitch
open WilsonOriginalGeneralRosterUnion (Row need request)
open WilsonOriginalGeneralRosterFile (Issued)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonOriginalGeneralRosterUnionReturn (Returned)
open WilsonReceivedChronologicalFixedRoseVariation (cells)
open WilsonReflectedPublicStationFare (station)
open WilsonReflectedOpticalRate (depth)
open WilsonAddressedMixedStationRange (width)
open WilsonOriginalMicroscopicGuardedReporters (Arrived)
open Cordial Pane PRAY.Wings
open scoped Classical BigOperators Topology ContDiff
variable {G:Gauge}{R:PhysicalNext.Repeat.Legato.Run G}{h:G.Simple}{e:Axis}{T₀:Campaign R}{W₀:Campaign.Pillars R T₀}
variable {P:PRAY R h}{D:ℕ}(W:P.Wings D)
universe u₀
variable {σ:OrderS G}{ε:ℝ}(p:PaidP.{u₀} e h ε σ R T₀ W₀) (Z:WilsonPrescription G)
variable {a:Axis}{ι:Type}{L:Filter ι}{r t:ι→ℝ} {P':Plans a} (U: Author.CameraT P')
local notation "C₀" => R.family
open Trace.Pilot Diary Barrel WilsonCoeffUV.Bank
open HalfRoof Cope Exporter.Loans PurchVoice Logwood
open WilsonOriginalPublicTrialPhaseUncutField (Fee)
open SignedWilsonExpansion.Fire
open WilsonCoeffUV WilsonCoeffUV.Embroider WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Xa Precision
open Pert.Asymptotics Liner MarqueQ StageG Crops Ballots
variable {v c:ι→ℕ}{μ:ι→ℝ}{K f₀ K₀ D₀ ν j F N per u n S o w q:ℕ}(M:Diary W L r t)(win:Draft G D P')
open WilsonMovingForkOwnRadiusSites (Recorded)
open WilsonPositionProgramReporterBand (Band)
open WilsonMovingForkPrintedFile (parent)
open WilsonMovingForkSeededPoint (seats)
namespace Tincture
variable {X:XSpace.Run}{stage κ:ℕ}{B:Band R X stage}
variable (S₁:WilsonIndependentCapturedPages.Stop R X B o F)(old:0 < stage)
variable (hr:Tendsto r L trail)(d:0<D)
local notation "𝔠" => capCenter (r:=r) (R:=R) (U:=U)
local notation "Λ" => (C₀).path.levels
local notation "aZ" => (C₀).S.a
local notation "σZ" => (C₀).S.scale
structure Cursor (b₀:ℕ)(w:ι):Prop where
  late : b₀ ≤ capCenter (r:=r) (R:=R) (U:=U) w
  gap :  capCenter (r:=r) (R:=R) (U:=U) w+2≤ reporter W M w
  mesh : ( R.family ).S.a ( capCenter (r:=r) (R:=R) (U:=U) w ) / ( R.family ).S.a (reporter W M w) ≤( boilerM R.family (reporter W M w) )^(2*W.T+13+2*1)
  space : ∀ (win:Draft G D P') (x:Shake (n:=Draft.bill win)),plotF W M win x w→ Recorded R ( reporter W M w ) ( capCenter (r:=r) (R:=R) (U:=U) w ) x
abbrev seqV (U:Author.CameraT P')(B:Band R X stage) (r:ι→ℝ)(w:ι) := capCenter (r:=r) (R:=R) (U:=U) w-B.reporter
abbrev viewS (w:ι) := S₁.date ( seqV (R:=R) U B r w )
abbrev heatS (w:ι):= regulatorRun R.family ( capCenter (r:=r) (R:=R) (U:=U) w ) 0 ( capCenter (r:=r) (R:=R) (U:=U) w )
include hr W d p
lemma rollsT (b₀:ℕ) : ∀ᶠ i in L,Cursor W U M b₀ i:=by
   have e:= WilsonReceivedChronologicalRosterOuterHomeMesh.original P.last h P.bliss p.receiptsP.2 D W.T 1 ( SlotX (G:=G) ) W.book ( Draft.headR d false ) U.U U.broad b₀
   filter_upwards [hr.eventually e,hr.eventually ( annex (I:= Scarf G D ) W ), allHomes W M d, hr.eventually self_mem_nhdsWithin, M.lo ] with i hi ht hv hr hs; let ρ:= houseP W M i; have hQ:= hi ρ (ht _ hv) hv.2; dsimp only at hQ; rcases hQ with ⟨ hz,he,hg,hm,hs'⟩; have hm': (ρ ( Draft.headR d false ) ).val=r i:= hs; rw [ hz,hm' ] at he hg hm hs'; exact ⟨he,hg,hm,fun win x h=>hs' _ (fun t=> spaceF W U M win x i hr h 1 t |>.2 )⟩
include M in
lemma funerals : Tendsto ( capCenter (r:=r) (R:=R) (U:=U) ) L atTop:= tendsto_atTop.mpr fun b=> (rollsT W p U M hr d b).mono fun i hi=>hi.late
include M in
lemma parade : ∀ᶠ i in L,B.reporter+seqV (R:=R) U B r i=capCenter (r:=r) (R:=R) (U:=U) i :=
    (rollsT W p U M hr d B.reporter).mono fun i hi=> Nat.add_sub_of_le hi.late
namespace Cursor
omit hr d p
lemma coordinates {b₀:ℕ}{i:ι}(Q:Cursor W U M b₀ i)(x:Shake (n:=Draft.bill win))(hi:plotF W M win x i) (per:ℕ)(u:ℕ) : wreathW W U M i per u x:=by
    intro z
    let f:= reporter W M i; let k:= filing W M u i; let c:= capCenter (r:=r) (R:=R) (U:=U) i; have fk:f≤k:= ( WilsonInvariantActionPosition.arrival R .. ).1.le
    have e:= ( ( Q.space win x hi ) k fk c le_rfl z ).1 per; have η:location (C₀).S f k per ∘ x=WilsonMovingForkSeededPoint.seats (R:=R) fk per x:=by funext; unfold location Function.comp WilsonMovingForkSeededPoint.seats; simp only [dif_pos fk]
    change Ballots.rolls ( C₀ ).S (location (( C₀ ).S) f k per ∘ x) z=0; rw [ η ]; exact funext e
end Cursor
include hr d p W U -- maybe duplicate include
local notation "vT" => ( viewS (r:=r) U S₁ )
local notation "ST" => heatS (r:=r) (R:=R) (U:=U)
lemma visiting (b₀:ℕ)(old:0<stage) : ∀ᶠ i in L,Cursor W U M b₀ i ∧ ( B.reporter+seqV (R:=R) U B r i=capCenter (r:=r) (R:=R) (U:=U) i ) ∧ o≤ vT i ∧ 0 < vT i ∧ vT i ≤ 𝔠 i ∧ aZ (𝔠 i)/aZ (vT i)≤ ( (ST i)^F)^2 ∧ σZ (𝔠 i)-σZ (vT i)≤4*(2*(F:ℝ)+1)*Real.log ( ST i )⁻¹ :=by
     obtain ⟨b,e⟩:=eventually_atTop.mp S₁.heard; let t':= seqV (R:=R) U B r; let f:= capCenter (r:=r) (R:=R) (U:=U); filter_upwards [ (rollsT W p U M hr d b₀), ( parade (B:=B) W p U M hr d ), (funerals W p U M hr d).eventually_ge_atTop (B.reporter+b) ] with i hi hz hx; have ht:b≤t' i:=by change _ ≤ f i at hx; change B.reporter+t' i=f i at hz; omega
     let g:=e ( t' i ) ht; change Cursor W U M b₀ i ∧ _ ∧ o≤ S₁.date ( t' i ) ∧ 0<S₁.date ( t' i )∧ S₁.date ( t' i )≤ f i∧ _; refine ⟨hi,hz,g.1, old.trans_le (( B.ready ( t' i ) ).trans ( S₁.lower ( t' i ) )), ( S₁.upper ( t' i ) ).trans hz.le,?_⟩; have hQ:=( g.2 (B.reporter+t' i) 0 le_rfl ).2.2; rw [ (show B.reporter+t' i=f i from hz) ] at hQ; exact hQ
lemma wires (κ:ℕ)(old:0<stage) : AgeRead (window W) κ F L ( R.family.path.levels ) r (cck G∘r) (reporter W M) (filing W M κ) (capCenter (r:=r) (R:=R) (U:=U)) (viewS (r:=r) U S₁) (heatS (r:=r) (R:=R) (U:=U)):=by
    let c:= capCenter (r:=r) (R:=R) (U:=U); let Sν:= visiting W p U M S₁ hr d 0 old; unfold window; rw [show 2*W.T+13= (2*W.T+11+2*1) from by omega]; refine requestAge W p.receiptsP.2 hr ( allHomes W M d ) (SlotX (G:=G)) (U:=U.U) ⟨hr.eventually ( brackets (R:=R) U.U U.broad ), U.broad, Sν.mono ( fun i hi=> hi.1.gap ), Sν.mono ( fun i hi=> hi.2.2.2.2.1 ), Sν.mono ( fun i hi=> hi.2.2.2.2.2 ), (?_)⟩ (Eventually.of_forall fun i=>rfl); exact fun x=> lensClock (C₀) h R.makes hr c c ( fun _=>0 ) x ( Eventually.of_forall fun _=>le_rfl )
-- Cool on every regulator-retained face at v. Needed for booking all words, when sold eccentric weight higher.
lemma tot (v:ι→ℕ) (height : Glow ( R.family ).path.levels r (cck G ∘ r) L v) : ∀ᶠ i in L,∀ N p:ℕ,v i ≤N → 0 < regulatorRun R.family N p (v i) ∧ regulatorRun R.family N p (v i) ≤1 :=by
   let e':= radius_clock h hr; let Θ:= (C₀).path.levels.clock.hatBeta ∘ v; have hz:Rise Θ L:= tends e' ( epoch_wave e' EventuallyEq.rfl height )
   filter_upwards [hz.eventually_ge_atTop 4] with i hi N p o; let y:=(C₀).path.β N p (v i); have hX: Θ i/2 ≤ y :=( R.makes.wilson.represents N p (v i) o ).band.1; have he:0<y:=by linarith only [hX,hi]
   exact ⟨inv_pos.mpr (Real.sqrt_pos.mpr he), inv_le_one_of_one_le₀ ((Real.le_sqrt zero_le_one he.le).mpr ( by linarith only [hi,hX] ))⟩
-- choose band using appointed World, always allowing positive stage. The datum S₁ remains chronological on posterior k geometry.
omit p hr W d U
include p
lemma blink (old:ℕ)(X:XSpace.Run)(stage:ℕ)(eB:ℕ)(H:0<eB)(rS:X.ratio=(3:ℕ)^eB) : ∃ B:Band R X stage,∀ F:ℕ,Nonempty (WilsonIndependentCapturedPages.Stop R X B old F):=by
     obtain ⟨B⟩:= WilsonPositionProgramReporterBand.original R X h p.paid.nested H rS p.receiptsP.2.2 stage; exact ⟨ B, WilsonIndependentCapturedPages.original R X h p.receiptsP.2 B old ⟩
end Tincture
end YM.Integration.Election.VaultM.Till
end
