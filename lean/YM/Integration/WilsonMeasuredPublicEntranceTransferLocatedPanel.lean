import YM.Integration.WilsonMeasuredPublicEntranceTransferKnotBoard
import YM.Integration.WilsonMeasuredPublicEntranceFullCampus
import YM.Integration.WilsonSeparatedPrefixSchoolHearing
/-! The previously appointed master campus supplies the actual matrix and each named fitted source on every received f-grid location, including K=N. Both original regulator limits keep the uncut K observable on the original N film. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferLocatedPanel
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


def cost {D T n:ℕ}{δ:ℝ}(d:Fin n→Fin (D+1))
    (books:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val)
    (ρ:Fin n→{s:ℝ // 0<s ∧ s<δ})(f q desired:ℕ)(M:Fin n→ℝ)
    (name:∀i,Bool→S.Field (d i).val)(b:Fin n→Bool):ℝ:=
  (∏i:↥(Stock.final (Fin n)).val,Motion.orbitCost ((C₀).labels.level (d i.val).val)*
    charge F ((books (ρ i.val)).rows (d i.val)) f (b i.val) (name i.val (b i.val)))*((β f)^q)⁻¹+
  (∏i,WilsonAddressedHomeDose.ceiling (R:=R) (d i).val (M i))*((β f)^desired)⁻¹

theorem original {D T n t q u:ℕ}{d:Fin n→Fin (D+1)}{e:Fin n→ℕ}{δ:ℝ}
    {books:(s:{s:ℝ //0<s ∧ s<δ})→Book F (l:=l) H arch D T s.val}
    {names:(i:Fin n)→{s:ℝ //0<s ∧ s<δ}→Bool→Bool→S.Field (d i).val}
    {M:Fin n→ℝ}{E:Fin n→ℕ}{tuition:ℝ}{power target:ℕ}
    {ρ:Fin n→{s:ℝ //0<s ∧ s<δ}}{f K:ℕ}
    (one:∀i,1≤M i)(campus:WilsonMeasuredPublicEntranceFullCampus.School F D T t d e books names M E tuition power target ρ f K):
    ∃up:f<K,∃electrode:(p:ℕ)→(i:Fin n)→Bool→(C₀).label (d i).val ≃ₗ[ℂ] (C₀).label (d i).val,
      ∀N p,∀_live:K≤N,∀mode b:Fin n→Bool,
      let grade:=fun i=>(d i).val
      let name:=fun i h=>names i (ρ i) (mode i) h
      let Y:=fun i=>(((books (ρ i)).rows (d i)).arm (b i) (name i (b i))).source (N,p)
      ∀old:Filed R grade K,let file:=WilsonMeasuredPublicEntranceCutoffFile.complete R grade old (fun p i=>electrode p i (b i))
      file.station=(fun i=>WilsonReflectedPublicStationFare.station F ((books (ρ i)).rows (d i)) (b i)) →
      ∀desired requested,(∀i,accuracy grade requested i≤e i) → desired+∑i,E i≤requested →
      ∀base j apron reserve first,ReadAt R grade base N p apron requested t reserve power (capital R D tuition) first →
      first≤j → base≤j → ∀height:j+2≤f,K=WilsonInvariantActionPosition.berth R reserve f →
      (∀i,first≤file.station i) → base≤u → ∀past:u≤j,Opened (C₀) 0 u p → Opened (C₀) 0 j p →
      ∀(o:Fin n→ Cover)(turn:Fin n→Motion)(ε:ℝ),
      let loc:=fun i=>wrap ((C₀).side f p) (o i)
      Ground R N p j f apron loc → At F d books ρ name q u f o ε N p →
      let Q:=submitted R grade (N:=N) file up.le Y turn loc (Stock.final (Fin n))
      let older:=actualTransport (C₀) (N:=N) Q ((past.trans (by omega : j≤f)).trans up.le) 1
      let gibbs:=∫U,Q U ∂scene (C₀).path N p K
      let ren:=publicValue (C:=C₀) (S:=S) grade f o (fun i=>displayed R (grade i) (Y i) (turn i))
      let paid:=cost F d books ρ f q desired M name b+ε
      ‖older-ren‖≤paid ∧ ‖gibbs-ren‖≤‖gibbs-older‖+paid:=by
  classical
  obtain ⟨up,electrode,_,installed⟩:=campus
  refine ⟨up,electrode,?_⟩
  intro N p live mode b grade name Y old file station desired requested acc exposure base j apron reserve first read
    before baseJ height berth allSlots baseU past earU earJ o turn ε loc ground knot Q older gibbs ren paid
  obtain ⟨_,_,_,_,supply⟩:=installed N p live
  have steps (i k:Fin n)(ne:i≠k):((C₀).path.levels.budget f).B^2<separation (loc i) (loc k):=by
    have same:((C₀).path.rep N p f).p=(C₀).path.levels.budget f:=(R.makes.wilson.represents N p f (up.le.trans live)).vac
    have cleared:=ground.2.1 i k ne
    rw [same] at cleared
    exact cleared
  obtain ⟨A,atSlot,axes,rows,purses,_,_,motions,roots,_,_,_,refs,wage⟩:=
    supply n id mode b old station requested acc turn loc steps
  have dates:∀i,first≤A.slot i:=fun i=>by rw [atSlot];exact allSlots i
  have gA:Ground R N p j f apron A.loc:=by rw [roots];exact ground
  have sale:=read j f K before baseJ height berth up.le live A dates (Or.inr gA) u baseU past earU earJ
  let uf:u≤f:=past.trans (by omega)
  have ok:∀i,1≤A.M i:=fun i=>by rw [purses];exact one i
  have debt:=knot (up.trans_le live) K up.le live requested power t (capital R D tuition) A file atSlot axes roots
    b rows uf sale ok E refs wage desired exposure
  dsimp only at debt
  rw [←WilsonMeasuredPublicEntranceTransferSubmitted.original R grade A file atSlot axes (Stock.final (Fin n))] at debt
  rw [rows,motions,roots,purses] at debt
  exact debt

end YM.Integration.WilsonMeasuredPublicEntranceTransferLocatedPanel
end
