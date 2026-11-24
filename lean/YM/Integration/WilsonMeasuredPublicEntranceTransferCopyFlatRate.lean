import YM.Integration.WilsonMeasuredPublicEntranceTransferLocatedPanel
import YM.Integration.WilsonMeasuredPublicEntranceTransferKineticRate
import YM.Integration.WilsonMeasuredPublicEntranceCutoffHearing
/-! The previously appointed master campus supplies the actual matrix and each named fitted source on every received f-grid location, including K=N. Both original regulator limits keep the uncut K observable on the original N film. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option quotPrecheck false
set_option maxHeartbeats 1700000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceTransferCopyFlatRate
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


theorem original {D T n t u:ℕ}{d:Fin n→Fin (D+1)}{e:Fin n→ℕ}{δ:ℝ}
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
      ∀loc:Fin n→Site ((C₀).side f p),∀turn:Fin n→Motion,Ground R N p j f apron loc →
      let road: u≤K:=(past.trans (by omega :j≤f)).trans up.le
      let Q:=submitted R grade (N:=N) file up.le Y turn loc (Stock.final (Fin n))
      let raw:=physical R grade (N:=N) Y turn loc (Stock.final (Fin n))
      let parent:=actualTransport (C₀) (N:=N) raw (road.trans _live) 1
      let lower:=actualTransport (C₀) (N:=N) Q road 1
      let price:=(∏i,WilsonAddressedHomeDose.ceiling (R:=R) (grade i) (M i))*((β f)^desired)⁻¹
      ‖parent-lower‖≤price ∧
        ‖lower-(C₀).omega N p raw‖≤‖(C₀).omega N p raw-parent‖+price ∧
        ‖lower-(C₀).omega N p raw‖≤‖(C₀).omega N p raw-parent‖+
          (∏i,WilsonAddressedHomeDose.ceiling (R:=R) (grade i) (M i))*
            (2*(Pert.Asymptotics.regulatorRun (C₀) N p f)^2)^desired:=by
  classical
  obtain ⟨up,electrode,_,installed⟩:=campus
  refine ⟨up,electrode,?_⟩
  intro N p live mode b grade name Y old file station desired requested acc exposure base j apron reserve first read
    before baseJ height berth allSlots baseU past earU earJ loc turn ground road Q raw parent lower price
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
  have precise:=WilsonMeasuredPublicEntranceCellWords.paid R grade A file atSlot axes uf sale ok E refs wage (Stock.final (Fin n)) desired
    (by simpa only [Stock.final] using exposure)
  rw [WilsonMeasuredPublicEntranceCutoffHearing.original] at precise
  unfold WilsonMeasuredPublicEntranceCutoffHearing.difference at precise
  rw [rows,motions,roots,purses] at precise
  have step:‖parent-lower‖≤price:=by simpa only [parent,lower,price,raw,Q,Y,name,Function.comp_apply,id_eq,Stock.final] using precise
  have earned:‖lower-(C₀).omega N p raw‖≤‖(C₀).omega N p raw-parent‖+price:=by
    calc
      _=‖(C₀).omega N p raw-lower‖:=norm_sub_rev ..
      _≤‖(C₀).omega N p raw-parent‖+‖parent-lower‖:=norm_sub_le_norm_sub_add_norm_sub ..
      _≤_:=add_le_add le_rfl step
  have nb:0≤∏i,WilsonAddressedHomeDose.ceiling (R:=R) (grade i) (M i):=
    prod_nonneg (fun i _=>(by linarith [one i] : (0:ℝ)≤2*M i).trans (le_max_left ..))
  exact ⟨step,earned,earned.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (WilsonMeasuredPublicEntranceTransferKineticRate.kinetic (R:=R) f desired N p (up.le.trans live)) nb))⟩

end YM.Integration.WilsonMeasuredPublicEntranceTransferCopyFlatRate
end
