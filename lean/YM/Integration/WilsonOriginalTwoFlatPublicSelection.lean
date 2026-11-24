import YM.Integration.WilsonOriginalTwoFlatPublicPanel

/-! Purchase the original reflection stop and the common public field book
on the elected run before fixing any field, viewer or original cutoff. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicSelection
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

include L in
theorem original (simple:G.Simple)(bliss:Bliss F l z H)(slow:WilsonWindowReportingPace.Slow R.kit)
    (D q:ℕ)(d:I→Fin (D+1)){M η:ℝ}(one:1≤M)(ep:0<η):
    ∃J u T:ℕ,Stop C 0 J u ∧ ∀ᶠ r in trail,∃k:ℕ,
    ∃stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T),
    ∃ (W:Vane R.family k) (fits:D≤k) (V:∀e:Fin (D+1),Spin.change S e.val)
      (A:∀e:Fin (D+1),Pair F stock (Nat.le_of_lt_succ e.isLt) W fits (V e) r),
      W.checked order H k ∧ W.wheel.r=r ∧
      let m:=max stock.j W.k
      let j:=WilsonInvariantActionPosition.berth R 5 m
      ∃uj:u≤j,∀N p:ℕ,∀hN:j<N,∀o:I → Cover,(∀i,‖(C).S.gridPoint j (o i)‖≤M*r) →
      (Pairwise fun i i'=>η*r≤‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      ∀weak:I→Bool,∀v:∀i,S.Field (d i).val,
      let Y:=word R (fun i=>(d i).val) j N p hN.le o (fun i=>((A (d i)).arm (weak i) (v i)).source (N,p))
      ‖gap R N p u (uj.trans hN.le) Y‖ ≤ (∏i,charge F (A (d i)) j (weak i) (v i))*((β j)^q)⁻¹:=by
  obtain ⟨J,u,stop⟩:=(RG16.Literal.forStop C simple L 0).exists
  obtain ⟨T,stocks⟩:=WilsonPositionProgramPublicStations.original F simple bliss D
  have zero:=stop 0 le_rfl
  refine ⟨J,u,T,zero,?_⟩
  filter_upwards [stocks,WilsonOriginalTwoFlatPublicPanel.original F L simple bliss slow zero
    (fun i=>(d i).val) D T q (fun i=>Nat.le_of_lt_succ (d i).isLt) one ep] with r funds heard
  obtain ⟨stock,k,fits,W,checked,active,_,_,book⟩:=funds.1
  have take(e:Fin (D+1)):=book e.val (Nat.le_of_lt_succ e.isLt)
  choose V paid using take
  let A(e:Fin (D+1)):=Classical.choice (paid e)
  exact ⟨k,stock,W,fits,V,A,checked,active,heard (fun i=>A (d i)) checked active⟩

end YM.Integration.WilsonOriginalTwoFlatPublicSelection
end
