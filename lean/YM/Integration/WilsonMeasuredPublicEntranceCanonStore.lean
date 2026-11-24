import YM.Integration.WilsonSeparatedPrefixCanonicalPublicSale
/-! The full filed public source itself supplies the true incoming P wallet at its home date. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonMeasuredPublicEntranceCanonStore
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open Extraction Table Spec Trace.Pilot Trace.Physical Trace.Physical.Germ
open WilsonThermometerOwnOffsetRadii WilsonThermometerOwnOffsetTale WilsonThermometerReflectedTrajectory
open WilsonThermometerOwnOffsetNectar WilsonReflectedPublicOrientedFaces
open Function Filter Finset Set MeasureTheory Lattice RG Wilson Source Labels Extra.Histories Motion
open Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open PhysicalNext PhysicalNext.Repeat.Legato Work.G08 Next.Rank Marker MergeProof Accent Extra.Multi
open RG05Readout RG05Readout.Address RG05Readout.Records Menu Extra.Trajectories Push.GridApprox.Nil
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonAddressedAlignedColumn
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open WilsonAddressedAlignedColumn
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){I:Type}[Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "J₀" => Marks I

theorem original (d:I → ℕ){N p f:ℕ}(live:f<N)
    (turn:I → Motion)(o:I → Site ((C).side f p))(y:∀a,Palette (C) (d a))
    (V:∀a,Sight (C) (d a) p)(r:∀a,Emblems (C) (d a))(names:Census I)(t:ℕ)
    (filed:WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o y V r names live.le t):
    let P:=(C).path.rep N p f
    let w:=fun _:I=>((H f)^t)⁻¹
    (∃φ:I → Config G ((C).side f p) → ℂ,∃ω,∃F:Config G ((C).side f p) → Poly names,
      Served P φ ω F o w P.p.supportExponent 1) ∧
    (∀a,0<w a ∧ (w a)⁻¹=(H f)^t):=by
  intro P w
  let origins:=WilsonThermometerOwnOffsetJoint.origins R (fun a=>WilsonThermometerReflectedRoster.endpoint R
    (N:=N) 0 (turn a) (o a)) f
  have sites:origins=o:=by
    funext a
    exact (WilsonThermometerReflectedRoster.parent R (N:=N) 0 (turn a) (o a) le_rfl live.le).trans
      (WilsonReflectedPublicOpticalJoint.location R live.le (turn a) (o a))
  have budget:P.p=(C).path.levels.budget f:=(R.makes.wilson.represents N p f live.le).vac
  have tariff:topPitch (C).path N f=P.p.supportExponent:=by rw [topPitch,if_neg live.ne,budget]
  have sold:Served P _ _ _ origins (fun _=>radius R t f f) (topPitch (C).path N f) 1:=(filed f le_rfl live.le).2.2
  rw [sites,tariff,radius_start] at sold
  refine ⟨⟨_,_,_,sold⟩,fun a=>⟨inv_pos.mpr (pow_pos (WardBin.hot (C).path.levels f) _),inv_inv _⟩⟩

end YM.Integration.WilsonMeasuredPublicEntranceCanonStore
end
