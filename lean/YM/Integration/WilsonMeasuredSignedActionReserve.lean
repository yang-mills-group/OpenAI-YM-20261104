import YM.Integration.WilsonOriginalTwoFlatPublicBooks
import YM.Integration.OPETreePhysical
/-! The weak grade roof can increase on the same Wilson family and the
same issued finite pooled portfolio. Only its stated grades are billed. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredSignedActionReserve
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open WilsonAddressedPublicPool WilsonAddressedPublicCrown WilsonThermometerReflectedTrajectory
open scoped Classical Topology BigOperators
open WilsonReflectedPublicOrientedFaces
open Climb Maxwell Maxwell.Free MS.Land Next.Rank.Station MergeProof.East Next.UVStress Trace.Terrace Trace.Pilot GapsContact GapsContact.Seams
open GapsContact.Stamps Trace GapsContact.Ascent
open WilsonMeasuredPublicBank WilsonPositionProgramPublicStations WilsonReflectedPublicStationFare

open RG16 RG16.Literal OPE Overlay Bid Push.GridApprox PhysicalNext.Repeat.Mallow Bandage
open WilsonReflectedPublicStationFare

open WilsonOriginalTwoFlatPublicFare (charge)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonOriginalTwoFlatGridScaling (gap)

variable {G:Gauge}{R:Run G}{order:Extraction.Order}{S:Table R.family.book}
  (F:Final R.family order S){l:Ultrafilter (ℕ×ℕ)}{H:(Bel R.family.book).Hierarchy}
  {z:Trace.Terrace.Arch R.family}{lo wid teach}(L:Package R.family wid lo teach)
  {I:Type}[Fintype I][DecidableEq I][Nonempty I]
local notation "C" => R.family
local notation "P" => R.family.path.levels
local notation "a" => R.family.S.a
local notation "β" => (P).clock.hatBeta

open WilsonOriginalTwoFlatPublicBooks (Book)
open WilsonThermometerUnitFilingFourWeakWall (Purchased)
open WilsonPositionProgramPublicStations (Pair)
open WilsonThermometerUnitFilingFourSquare (Arm)

theorem mounted {D T height:ℕ}{r:ℝ}
    (stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
      (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T))
    (weak:Purchased F H l r (max D height)):
    ∃B:Book F (l:=l) H z D T r,height≤B.k ∧ height≤B.W.k:=by
  obtain ⟨k,cap,W,good,atR,live,_width,available⟩:=weak.station
  have fits:D≤k:=(le_max_left D height).trans cap
  have rows(e:Fin (D+1)):∃V:Spin.change S e.val,Nonempty (Pair F stock (Nat.le_of_lt_succ e.isLt) W fits V r):=by
    let i:Fin (max D height+1):=⟨e.val,Nat.lt_succ_of_le ((Nat.le_of_lt_succ e.isLt).trans (le_max_left ..))⟩
    obtain ⟨V,filed⟩:=available i
    choose arm holds cards using filed
    let v(y:S.Field e.val):Arm R.family S (l:Filter _) e.val y:=
      let leg:=arm (V.symm y)
      ⟨leg.source,leg.label,leg.approaches,leg.represents.trans (V.apply_symm_apply y)⟩
    let arms(b:Bool)(y:S.Field e.val):Arm R.family S (l:Filter _) e.val y:=
      if b then v y else ((stock.department e.val (Nat.le_of_lt_succ e.isLt)).print y).arm
    refine ⟨V,⟨⟨arms,fun _=>rfl,fun y b=>holds (V.symm y) b,fun y=>?_⟩⟩⟩
    exact cards (V.symm y)
  choose V row using rows
  exact ⟨⟨stock,k,W,fits,good,atR,V,fun e=>Classical.choice (row e)⟩,
    (le_max_right D height).trans cap,(le_max_right D height).trans live⟩

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(D:ℕ):
    ∃T:ℕ,∀height:ℕ,∀ᶠ r in trail,
      ∃B:Book F (l:=l) H z D T r,height≤B.k ∧ height≤B.W.k:=by
  obtain ⟨T,stocks⟩:=WilsonPositionProgramPublicStations.original F simple bliss D
  refine ⟨T,fun height=>?_⟩
  filter_upwards [stocks,WilsonThermometerUnitFilingFourWeakWall.original F simple bliss (max D height)]
    with r bought weak
  obtain ⟨stock,_⟩:=bought.1
  exact mounted F stock weak

theorem books (simple:G.Simple)(bliss:Bliss F l z H)(D:ℕ):
    ∃T:ℕ,∃δ:ℝ,0<δ ∧ ∃B:(s:{s:ℝ // 0<s ∧ s<δ})→Book F (l:=l) H z D T s.val,
      ∀cap:ℕ,∀ᶠ r in trail,∀pos:0<r,∀small:r<δ,
        cap≤(B ⟨r,pos,small⟩).k ∧ cap≤(B ⟨r,pos,small⟩).W.k:=by
  obtain ⟨T,offered⟩:=original F simple bliss D
  let Fits:=fun k:ℕ=>fun r:ℝ=>∃B:Book F (l:=l) H z D T r,k≤B.k ∧ k≤B.W.k
  obtain ⟨cap,late,buy⟩:=OPETreePhysical.slow_demand Fits (Eventually.of_forall offered)
  obtain ⟨δ,dp,all⟩:=Metric.mem_nhdsWithin_iff.mp buy
  have paid(r:{r:ℝ // 0<r ∧ r<δ}):Fits (cap r) r:=all (show r.val∈Metric.ball (0:ℝ) δ ∩ Set.Ioi 0 from
    ⟨by simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos r.property.1] using r.property.2,r.property.1⟩)
  choose B sizes using paid
  refine ⟨T,δ,dp,B,?_⟩
  intro k
  filter_upwards [late.eventually_ge_atTop k] with r larger
  intro pos small
  exact ⟨larger.trans (sizes ⟨r,pos,small⟩).1,larger.trans (sizes ⟨r,pos,small⟩).2⟩

end YM.Integration.WilsonMeasuredSignedActionReserve
end
