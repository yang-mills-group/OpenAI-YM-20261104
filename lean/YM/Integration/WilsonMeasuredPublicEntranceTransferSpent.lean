import YM.Integration.WilsonMeasuredPublicEntranceTransferCofinalSurvey
/-! Exact two-ear debit on genuine stationed source files, with its separately earned total receipt expressed in numerical currency. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferSpent
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




open WilsonMeasuredPublicEntranceTransferCampusSurvey (submittedWord)
variable {D T n:ℕ}{d:Fin n→Fin (D+1)}{e:Fin n→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val}
    {names:(i:Fin n)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:Fin n→ℝ}{E:Fin n→ℕ}{tuition:ℝ}{power target t:ℕ}
    {ρ:Fin n→{s:ℝ //0<s ∧ s<δ}}{f K j u apron q:ℕ}
    {m:ℕ}{B:Type}[Fintype B]{ref:B→E4}{φ:Test n}{r:ℝ}{rp:0<r}
local notation "grade" => fun i=>(d i).val

def Spent (books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val)
    (ρ:Fin n→{s:ℝ //0<s ∧ s<δ})(name:∀i,Bool→S.Field (d i).val)
    (E:Fin n→ℕ)(qmin apron t power:ℕ)(tuition:ℝ)(P:Press R φ r rp f m ref)
    (up:f<K)(past:u≤j)(height:j+2≤f)
    (electrode:(p:ℕ)→(i:Fin n)→Bool→(C₀).label (d i).val ≃ₗ[ℂ] (C₀).label (d i).val)
    (marked:Fin n→Bool)(α:(Fin n→Bool)→ℂ)(gross ε fee:ℝ)(z:ℕ×ℕ)(out:ℂ):Prop:=
  let N:=z.1
  let p:=z.2
  let Y:=fun (b:Fin n→Bool) i=>(((books (ρ i)).rows (d i)).arm (b i) (name i (b i))).source z
  ∀_cut:K≤N,∀old:(Fin n→Bool)→Filed R grade K,
  let file:=fun b=>WilsonMeasuredPublicEntranceCutoffFile.complete R grade (old b) (fun p i=>electrode p i (b i))
  (∀b,(file b).station=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) (b i))) →
  ∀desired requested,qmin≤desired → (∀i,accuracy grade requested i≤e i) → desired+∑i,E i≤requested →
  ∀base reserve first,ReadAt R grade base N p apron requested t reserve power (capital R D tuition) first →
  first≤j → base≤j → K=WilsonInvariantActionPosition.berth R reserve f →
  (∀b i,first≤(file b).station i) → base≤u → Opened (C₀) 0 u p → Opened (C₀) 0 j p →
  let Q:=fun b i a=>submittedWord (N:=N) (p:=p) (R:=R) d (file b) up.le (Y b) marked (P.port i a)
  let Gibbs:=fun b i a=>∫U,Q b i a U ∂scene (C₀).path N p K
  let Ear:=fun b i a=>actualTransport (C₀) (N:=N) (Q b i a) ((past.trans (by omega : j≤f)).trans up.le) 1
  ‖tested P α Gibbs-phase P α Gibbs Ear-out‖≤
      (∑b,‖α b‖)*(WilsonMeasuredPublicEntranceTransferProfileMass.size P*(gross+ε))+fee


open WilsonMeasuredPublicEntranceTransferCofinalSurvey (Invoice)
open WilsonMeasuredPublicEntranceTransferProfileMass (size)

theorem mass_nonneg (P:Press R φ r rp f m ref):0 ≤ WilsonMeasuredPublicEntranceTransferProfileMass.size P:=by
  unfold WilsonMeasuredPublicEntranceTransferProfileMass.size
  refine sum_nonneg fun i _=>mul_nonneg (norm_nonneg _) ?_
  unfold WilsonSeparatedBranchStencil.bill
  exact sum_nonneg fun a _=>norm_nonneg _

theorem counted (P:Press R φ r rp f m ref)(name:∀i,Bool→S.Field (d i).val)
    (up:f<K)(past:u≤j)(height:j+2≤f)(electrode:(p:ℕ)→(i:Fin n)→Bool→(C₀).label (d i).val ≃ₗ[ℂ] (C₀).label (d i).val)
    (marked:Fin n→Bool)(α:(Fin n→Bool)→ℂ)(gross ε fee:ℝ)(w:ℕ×ℕ)(out:ℂ)(qmin:ℕ)
    (charged:∀desired, qmin≤desired → ∀b,cost F d books ρ f q desired M name b≤gross)
    (invoice:Invoice (e:=e) F books ρ name M E q apron t power tuition P up past height electrode marked α ε fee w out):
    Spent (e:=e) F books ρ name E qmin apron t power tuition P up past height electrode marked α gross ε fee w out:=by
  intro cut old file stations desired requested limit accuracy stamp base reserve first law oldJ baseJ effect slots baseU opened older Q Gibbs Ear
  have native:=invoice cut old stations desired requested accuracy stamp base reserve first law oldJ baseJ effect slots baseU opened older
  apply native.trans
  apply add_le_add _ le_rfl
  rw [Finset.sum_mul]
  exact sum_le_sum fun b _=>mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (add_le_add (charged desired limit b) (le_refl ε)) (mass_nonneg P)) (norm_nonneg _)

end YM.Integration.WilsonMeasuredPublicEntranceTransferSpent
end
