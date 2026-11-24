import YM.Integration.WilsonReflectedPublicMountedInvoice
import YM.Integration.WilsonReflectedPublicOrientedFaces
import YM.Integration.WilsonSeparatedPrefixCanonicalTwoFlat

/-! The actual oriented, displaced cutoff fields on their original cofiled
roster supply the single-site salaries for the physical two-flat hearing. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalPublicSale
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
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o data V r J₀ live.le t →
    ∃q:∀i,Coefficient ((C).labels.level (d i)) ((C).side f p),
      (∀i,(q i).Format (o i) (C).params P) ∧
      (∀i,((C).labels.level (d i)).coeffSize (q i).x≤(H f)^4) ∧
      (∀i,(q i).remBound (o i) P (LocalComparison.forcedDivisor (C) f) (WilsonReflectedPublicMountedInvoice.wage R f)) ∧
      WilsonReflectedPublicMountedInvoice.wage R f≤(H f)^4 ∧
      (∀i,(quiet i).2.1=(q i).exponentialEntry (o i) ((C).localSection (d i)) P) ∧
      (∀i,profile P.activities (quiet i).2.2=profile P.activities (q i).forced) ∧
      (∀i,(q i).density (o i) ((C).localSection (d i)) P=(quiet i).1) ∧
      Served P (fun i=>(q i).exponentialEntry (o i) ((C).localSection (d i)) P)
        (fun i=>profile P.activities (q i).forced) F o (fun _=>(H f^t)⁻¹) P.p.supportExponent 1:=by
  have prints:=Filter.eventually_all.mpr (fun i:I=>WilsonReflectedPublicMountedInvoice.original R simple shop (d i))
  have cover:=Filter.eventually_all.mpr (fun i:I=>(RG01.Physical.hats simple (A)).eventually_ge_atTop
    (orbitCost ((C).labels.level (d i))))
  filter_upwards [prints,cover,(RG01.Physical.hats simple (A)).eventually_ge_atTop 4] with f invoices prices hot N p live V r home enrolled x turn o t P y data quiet F filed
  choose q fit head pay bright forced exactFiled using fun i=> invoices i live.le (home i) (enrolled i) (x i) (turn i) (o i)
  have hp:1≤H f:=by linarith
  let X:=H f
  let B:=WilsonReflectedPublicMountedInvoice.wage R f
  have maxB:1+B≤X^2:=by
    have h1:=Real.log_le_self (x:=X) (by exact zero_le_one.trans hp)
    have xp:0<2+Real.log X:=by linarith [Real.log_nonneg hp]
    change 4≤X at hot
    have h2:=Real.log_le_self (x:=2+Real.log X) xp.le
    change 1+(1+Real.log (2+Real.log X))≤X^2
    nlinarith only [hot,h1,h2,sq_nonneg (X-2)]
  have small:B≤X^4:=by
    have h:X^2≤X^4:=pow_le_pow_right₀ hp (by decide:2≤4)
    linarith only [h,maxB]
  have within(i):((C).labels.level (d i)).coeffSize (q i).x≤ X^4:=by
    have o0:=zero_le_one.trans (orbitCost_one_le ((C).labels.level (d i)))
    have payB:=mul_le_mul_of_nonneg_left maxB o0
    have payO:=mul_le_mul_of_nonneg_right (prices i) (sq_nonneg X)
    have lead:X*X^2≤X^4:=by
      calc _=X^3:=by ring
           _≤_:=pow_le_pow_right₀ hp (by decide)
    exact (head i).trans (payB.trans (payO.trans lead))
  refine ⟨q,fit,within,pay,small,bright,forced,exactFiled,?_⟩
  let origins:=WilsonThermometerOwnOffsetJoint.origins R (fun i=>WilsonThermometerReflectedRoster.endpoint R (N:=N) 0 (turn i) (o i)) f
  have sites:origins=o:=by
    funext i
    exact (WilsonThermometerReflectedRoster.parent R (N:=N) 0 (turn i) (o i) le_rfl live.le).trans
      (WilsonReflectedPublicOpticalJoint.location R live.le (turn i) (o i))
  have sold:Served P (fun i=>(quiet i).2.1) (fun i=>profile P.activities (quiet i).2.2) F origins
      (fun _=>radius R t f f) (topPitch (C).path N f) 1:=(filed f le_rfl live.le).2.2
  have budget:P.p=(A).budget f:=(R.makes.wilson.represents N p f live.le).vac
  have tariff:topPitch (C).path N f=P.p.supportExponent:=by rw [topPitch,if_neg live.ne,budget]
  rw [sites,tariff,radius_start] at sold
  exact (congrArg₂ (fun a h=>Served P a h F o (fun _=>(H f^t)⁻¹) P.p.supportExponent 1)
    (funext bright) (funext forced)).mp sold

end YM.Integration.WilsonSeparatedPrefixCanonicalPublicSale
