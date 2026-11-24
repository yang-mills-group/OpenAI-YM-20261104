import YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerLedger

/-! The finite reflected experiment pays its complete canonical inlet on the
original period and cutoff, before reading any separated physical subface. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerSale
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

theorem original (d:I → ℕ)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b):
    ∀ᶠ f:ℕ in atTop,∀ N p (live:f<N)(V:∀i,Sight (C) (d i) p)(r:∀i,Emblems (C) (d i))
      (home:∀i,Opened (C) (d i) f p)(_enrolled:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R)
        f N p (d i) (digits R N p 0) (V i) (r i))
      (x:∀i,(C).label (d i))(turn:I → Motion)(o:I → Site ((C).side f p))(t:ℕ),
    let P:=(C).path.rep N p f
    let y:=fun i=>offer R (x i) (home i) live.le
    let data:=fun i=>reduce (y i)
    let quiet:=fun i=>marked R (N:=N) 0 (turn i) (o i) (V i) (r i) (data i) f
    let F:=WilsonThermometerReflectedRoster.density R d (fun _=>0) turn o data r J₀ live.le live.le
    ((A).params f).supportExponent=100 →
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o data V r J₀ live.le t →
    ∃q:∀i,Coefficient ((C).labels.level (d i)) ((C).side f p),
      (∀i,(q i).Format (o i) (C).params P) ∧
      (∀i,((C).labels.level (d i)).coeffSize (q i).x≤(H f)^4) ∧
      (∀i,(q i).remBound (o i) P (LocalComparison.forcedDivisor (C) f) (WilsonReflectedPublicMountedInvoice.wage R f)) ∧
      WilsonReflectedPublicMountedInvoice.wage R f≤(H f)^4 ∧
      (∀i,(quiet i).2.1=(q i).exponentialEntry (o i) ((C).localSection (d i)) P) ∧
      (∀i,profile P.activities (quiet i).2.2=profile P.activities (q i).forced) ∧
      (∀i,(q i).density (o i) ((C).localSection (d i)) P=(quiet i).1) ∧
      WilsonOriginalPhysicalFirstEntryOwnerLedger.Priced (P:=P) (o:=o) q
        (fun i=>(q i).exponentialEntry (o i) ((C).localSection (d i)) P)
        F (fun _=>(H f^t)⁻¹) (LocalComparison.forcedDivisor (C) f)
        (fun _=>WilsonReflectedPublicMountedInvoice.wage R f) :=by
  filter_upwards [WilsonSeparatedPrefixCanonicalPublicSale.original R d simple shop] with
    f sold N p live V r home enrolled x turn o t P y data quiet F fixed active
  obtain ⟨q,form,head,old,pole,green,keys,whole,stock⟩:=sold N p live V r home enrolled x turn o t active
  have point:P.p=(A).budget f:=(R.makes.wilson.represents N p f live.le).vac
  have exponent:0≤P.p.supportExponent:=by rw [point];change 0≤((A).params f).supportExponent;rw [fixed];norm_num
  have positive:0 < H f:=lt_of_lt_of_le zero_lt_one ((A).fits.delayed f).le
  refine ⟨q,form,head,old,pole,green,keys,whole,?_⟩
  exact WilsonOriginalPhysicalFirstEntryOwnerLedger.filed q _ F _ _ _
    (fun _=>inv_pos.mpr (pow_pos positive t)) exponent form old stock
end YM.Integration.WilsonOriginalPhysicalFirstEntryOwnerSale
