import YM.Integration.WilsonMeasuredPublicEntranceTransferLocatedPanel
import YM.Integration.WilsonMeasuredPublicEntranceTransferProfileMass
/-! Joint signed testing of the actual K observables supplied by the original campus, with coordinate ties and the full centered phase on the original N vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCampusSurvey
open Function Set Filter Finset MeasureTheory Lattice Wilson RG Source Labels Cells
open Extra.Histories PhysicalNext.Repeat.Legato RG16 RG16.Literal WilsonThermometerUnitFilingCoarse
open WilsonReflectedPublicOrientedFaces (displayed)
open OPE Next.Rank Overlay Bid Push.GridApprox MergeProof Ribbons Accent ManyCopies
open WilsonMeasuredPublicEntrancePanel (Panel Reading)
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMeasuredPublicEntranceCellWords (submitted physical)
open WilsonMeasuredPublicEntranceOrderedPins (Release publicValue)
open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare
open Table Climb Next.UVStress
open Extraction Spec PertExtension PertExtension.LatticePT Trace.Pilot Trace.Terrace
open PhysicalNext.Repeat.Legato Push.GridApprox OPE.Strobe OPE.Therm
open scoped Classical BigOperators Topology
open Trace.Physical.GermGraph (Opened)
open WilsonMeasuredPublicEntranceBookedSurvey (Press model)
open WilsonMeasuredPublicEntranceTransferProfileMass (tested phase size)
open WilsonMeasuredPublicEntranceTransferLocatedPanel (cost)
open WilsonMeasuredPublicEntranceBookedRegulators (moving)
open WilsonMeasuredPublicEntranceMarkedNode (turned field)
variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}(F:Final R.family order S)
variable {l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}{arch:Arch R.family}
local notation "C₀" => R.family
local notation "β" => R.family.path.levels.clock.hatBeta
open WilsonMovingForkOpticalBook (reporter)
open WilsonMeasuredPublicEntranceMasterUpper (ReadAt)
open WilsonMeasuredPublicEntrancePanelOrder (capital)
open WilsonMeasuredPublicEntrancePanel (accuracy)
open WilsonMeasuredPublicEntranceScreen (Ground)
open WilsonMeasuredPublicEntranceFullCampus (School)
open WilsonMeasuredPublicEntranceTransferKnotBoard (At)
open RG16 RG16.Literal PhysicalNext.Repeat.Mallow Bandage
local notation "full" => Stock.final (Fin n)



def reflection (b:Bool):Motion:=if b then (Signed.mirror timeAxis,true) else (1,false)

theorem turn (d:ℕ)(Y:(R.family).label d)(b:Bool):
    displayed R d Y (reflection b)=turned R b Y:=by
  cases b
  · simp [reflection,displayed,turned,show (1:Signed).ortho=1 from map_one Signed.inclusionO,Labels.Frame.act_one]
  · rfl

def submittedWord {D n f K N p:ℕ}(d:Fin n→Fin (D+1))
    (file:Filed R (fun i=>(d i).val) K)(up:f≤K)(Y:∀i,(C₀).label (d i).val)
    (marked:Fin n→Bool)(o:Fin n→ Cover):Config G ((C₀).side K p)→ℂ:=
  submitted R (fun i=>(d i).val) (N:=N) file up Y (fun i=>reflection (marked i))
    (fun i=>wrap ((C₀).side f p) (o i)) (Stock.final (Fin n))

theorem original {D T n t q u:ℕ}{d:Fin n→Fin (D+1)}{e:Fin n→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val}
    {names:(i:Fin n)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:Fin n→ℝ}{E:Fin n→ℕ}{tuition:ℝ}{power target:ℕ}
    {ρ:Fin n→{s:ℝ //0<s ∧ s<δ}}{f K:ℕ}
    (one:∀i,1≤M i)(campus:WilsonMeasuredPublicEntranceFullCampus.School F D T t d e books names M E tuition power target ρ f K):
    ∃up:f<K,∃electrode:(p:ℕ)→(i:Fin n)→Bool→(C₀).label (d i).val ≃ₗ[ℂ] (C₀).label (d i).val,
      ∀N p,∀_live:K≤N,∀mode:Fin n→Bool,
      let grade:=fun i=>(d i).val
      let name:=fun i h=>names i (ρ i) (mode i) h
      let Y:=fun (b:Fin n→Bool) i=>(((books (ρ i)).rows (d i)).arm (b i) (name i (b i))).source (N,p)
      ∀old:(Fin n→Bool)→Filed R grade K,
      let file:=fun b=>WilsonMeasuredPublicEntranceCutoffFile.complete R grade (old b) (fun p i=>electrode p i (b i))
      (∀b,(file b).station=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) (b i))) →
      ∀desired requested,(∀i,accuracy grade requested i≤e i) → desired+∑i,E i≤requested →
      ∀base j apron reserve first,ReadAt R grade base N p apron requested t reserve power (capital R D tuition) first →
      first≤j → base≤j → ∀height:j+2≤f,K=WilsonInvariantActionPosition.berth R reserve f →
      (∀b i,first≤(file b).station i) → base≤u → ∀past:u≤j,Opened (C₀) 0 u p → Opened (C₀) 0 j p →
      ∀{m:ℕ}{A:Type}[Fintype A]{ref:A→E4}{φ:Test n}{r:ℝ}{rp:0<r}
        (P:Press R φ r rp f m ref)(marked:Fin n→Bool)(ε:ℝ),
      (∀i a,Ground R N p j f apron (fun k=>wrap ((C₀).side f p) ((P.port i a) k))) →
      (∀i a,At F d books ρ name q u f (P.port i a) ε N p) →
      let Q:=fun b i a=>submittedWord (N:=N) (p:=p) (R:=R) d (file b) up.le (Y b) marked (P.port i a)
      let Gibbs:=fun b i a=>∫U,Q b i a U ∂scene (C₀).path N p K
      let Ear:=fun b i a=>actualTransport (C₀) (N:=N) (Q b i a) ((past.trans (by omega : j≤f)).trans up.le) 1
      ∀α:(Fin n→Bool)→ℂ,
      ‖tested P α Gibbs-phase P α Gibbs Ear-moving F (fun i=>books (ρ i)) d name P α marked (N,p)‖≤
        ∑b,‖α b‖*(WilsonMeasuredPublicEntranceTransferProfileMass.size P*(cost F d books ρ f q desired M name b+ε)):=by
  classical
  obtain ⟨up,electrode,covered⟩:=WilsonMeasuredPublicEntranceTransferLocatedPanel.original (q:=q) (u:=u) F one campus
  refine ⟨up,electrode,?_⟩
  intro N p live mode grade name Y old file station desired requested acc exposure base j apron reserve first read
    before baseJ height berth allSlots baseU past earU earJ m A fin ref φ r rp P marked ε geo nodes Q Gibbs Ear α
  let current:=fun b (i:P.Entry) (a:(model P i).sample)=>publicValue (C:=C₀) (S:=S)
    grade f (P.port i a) (field R F (fun i=>books (ρ i)) d name b marked (N,p))
  have matchSource (b:Fin n→Bool):(fun i=>displayed R (grade i) (Y b i) (reflection (marked i)))=
      field R F (fun i=>books (ρ i)) d name b marked (N,p):=funext fun i=>turn _ _ _
  apply WilsonMeasuredPublicEntranceTransferProfileMass.compensated P α Gibbs Ear current
    (fun b=>cost F d books ρ f q desired M name b+ε)
  intro b i a
  have paid:=(covered N p live mode b (old b) (station b) desired requested acc exposure base j apron reserve first read
    before baseJ height berth (allSlots b) baseU past earU earJ (P.port i a) (fun i=>reflection (marked i))
    ε (geo i a) (nodes i a)).1
  dsimp only at paid
  rw [matchSource b] at paid
  exact paid

end YM.Integration.WilsonMeasuredPublicEntranceTransferCampusSurvey
end
