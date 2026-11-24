import YM.Integration.WilsonOriginalTwoFlatPublicFare
import YM.Integration.WilsonOriginalTwoFlatPublicGeometry

/-! Unrestricted Wilson moments on an entire separated shape of the actual
common reporting grid.  Every name has its own elected public lift and fare.
The fixed stop, chamber and numerical floor precede the original regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalTwoFlatPublicPanel
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
    {J u:ℕ}(stop:Stop C 0 J u)(d:I→ℕ)(D T q:ℕ)(cap:∀i,d i≤D)
    {M η:ℝ}(one:1≤M)(ep:0<η):
    ∀ᶠ r in trail,∀{k:ℕ}
      {stock:Bank F l D (WilsonThermometerUnitFilingFourPoolShell.radius z T r)
        (dock (WilsonThermometerUnitFilingFourPoolShell.radius z T r)^T)}
      {W:Vane R.family k}{fits:D≤k}{V:∀i,Spin.change S (d i)}
      (A:∀i,Pair F stock (cap i) W fits (V i) r),W.checked order H k → W.wheel.r=r →
      let m:=max stock.j W.k
      let j:=WilsonInvariantActionPosition.berth R 5 m
      ∃uj:u≤j,∀N p:ℕ,∀hN:j<N,∀o:I → Cover,(∀i,‖(C).S.gridPoint j (o i)‖≤M*r) →
      (Pairwise fun i i'=>η*r≤‖(C).S.gridPoint j (o i)-(C).S.gridPoint j (o i')‖) →
      ∀weak:I→Bool,∀v:∀i,S.Field (d i),
      let Y:=word R d j N p hN.le o (fun i=>((A i).arm (weak i) (v i)).source (N,p))
      ‖gap R N p u (uj.trans hN.le) Y‖ ≤ (∏i,charge F (A i) j (weak i) (v i))*((β j)^q)⁻¹:=by
  obtain ⟨floor,paid⟩:=eventually_atTop.mp (WilsonOriginalTwoFlatGridScaling.original R d L simple slow stop (2*T+11) q)
  filter_upwards [WilsonOriginalTwoFlatPublicGeometry.original F simple bliss slow T (max u floor) u one ep] with r geo
  intro k stock W fits V A checked active m j
  have shape (i:I):=geo (A i) checked active
  obtain ⟨late,positive,small,fine,span,separation,_⟩:=shape (Classical.choice ‹Nonempty I›)
  have uj:u≤j:=(le_max_left ..).trans late
  refine ⟨uj,?_⟩
  intro N p hN o inside apart weak v
  have stipend(i:I):=WilsonOriginalTwoFlatPublicFare.issued F (A i) checked (weak i) (v i)
    ((shape i).2.2.2.2.2.2 (weak i)) (p:=p) hN
  apply paid j ((le_max_right ..).trans late) positive small fine span N p hN o _ _ _ _
    (fun i=>lt_of_lt_of_le zero_lt_one (le_max_left ..)) stipend uj
  · intro i
    calc
      _ ≤ 8*(M*r):=mul_le_mul_of_nonneg_left (inside i) (by norm_num)
      _ = _:=by ring
  · intro i i' diff
    exact separation.trans (apart diff)

end YM.Integration.WilsonOriginalTwoFlatPublicPanel
end
