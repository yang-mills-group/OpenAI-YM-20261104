import YM.Integration.WilsonOriginalTwoFlatPublicPanel

/-! Purchase the original reflection stop and the common public field book
on the elected run before fixing any field, viewer or original cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicBooks
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

structure Book (H:(Bel R.family.book).Hierarchy)(z:Trace.Terrace.Arch R.family)(D T:ℕ)(r:ℝ) where
  stock : Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
    (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)
  k : ℕ
  W : Vane R.family k
  fits : D ≤ k
  checked : W.checked order H k
  active : W.wheel.r=r
  V : ∀e:Fin (D+1),Spin.change S e.val
  rows : ∀e:Fin (D+1),Pair F stock (Nat.le_of_lt_succ e.isLt) W fits (V e) r

theorem original (simple:G.Simple)(bliss:Bliss F l z H)(D:ℕ):
    ∃T:ℕ,∃δ:ℝ,0<δ ∧
      Nonempty ((r:{r:ℝ // 0<r ∧ r<δ})→Book F (l:=l) H z D T r.val):=by
  obtain ⟨T,stocks⟩:=WilsonPositionProgramPublicStations.original F simple bliss D
  obtain ⟨δ,dp,box⟩:=Metric.mem_nhdsWithin_iff.mp stocks
  refine ⟨T,δ,dp,?_⟩
  have issue(r:{r:ℝ // 0<r ∧ r<δ}):Nonempty (Book F (l:=l) H z D T r.val):=by
    have bought:=box (show r.val∈Metric.ball (0:ℝ) δ ∩ Set.Ioi 0 from ⟨by
      simpa only [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos r.property.1] using r.property.2,r.property.1⟩)
    obtain ⟨stock,k,fits,W,checked,active,_,_,book⟩:=bought.1
    have take(e:Fin (D+1)):=book e.val (Nat.le_of_lt_succ e.isLt)
    choose V paid using take
    exact ⟨⟨stock,k,W,fits,checked,active,V,fun e=>Classical.choice (paid e)⟩⟩
  exact ⟨fun r=>Classical.choice (issue r)⟩

end YM.Integration.WilsonOriginalTwoFlatPublicBooks
end
