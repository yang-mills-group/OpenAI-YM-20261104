import YM.Integration.WilsonSeparatedPrefixCanonicalClearPublic
import YM.Integration.WilsonOriginalMicroscopicEntranceHeldCharge
import YM.Integration.WilsonOriginalMicroscopicEntranceHeadIncome
import YM.Integration.WilsonAddressedPublicGridRooms

/-! The original uncharged microscopic product and the funded masked product at any clear earlier configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntrancePublicHeld
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
open WilsonThermometerUnitFilingCoarse WilsonReflectedPublicOrientedFaces WilsonSeparatedPrefixCanonicalClearConvolution
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "I" => Fin 3
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "H" => (A).clock.hatBeta
local notation "J₀" => Marks I
local notation "X" => Unit×(I×Bool)

theorem original (d:I → ℕ)(simple:G.Simple)(shop:RG05Preconstruction.ReadoutPurchase R.b)
    (pace:WilsonWindowReportingPace.Slow R.kit)(cater:Cater (C) R.doors)
    (wage:WilsonReportLampForecast.Ready (A))
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(window target t:ℕ):
    ∀ᶠ j:ℕ in atTop,∀ N p f (height:j≤f) (live:f<N)
      (V:∀i,Sight (C) (d i) p)(r:∀i,Emblems (C) (d i))(home:∀i,Opened (C) (d i) f p)
      (_enrolled:∀i,Enrolled R.makes R.doors (WilsonThermometerOffsetLedger.cash R) f N p (d i)
        (digits R N p 0) (V i) (r i))
      (x:∀i,(C).label (d i))(turn:I → Motion)(o:I → Site ((C).side f p))
      (route:∀u,X → Site ((C).side u p)),
    let P:=(C).path.rep N p f
    let y:=fun i=>offer R (x i) (home i) live.le
    let data:=fun i=>reduce (y i)
    let arm:=fun i=>marked R (N:=N) 0 (turn i) (o i) (V i) (r i) (data i) f
    WilsonThermometerReflectedRoster.filed R d (fun _=>0) turn o data V r J₀ live.le t →
    (C).S.a j/(C).S.a f≤(H f)^window → ((A).params f).supportExponent=100 →
    5≤P.p.B → (∀a b:I,a≠b → P.p.B^2+1≤ separation (o a) (o b)) →
    route f=(o∘Prod.fst) ∘ Prod.snd →
    (∀v,j≤v → v<f → route v=((A).clock.op v p).ratio.parent ∘ route (v+1)) →
    2≤((A).budget j).supportExponent → ∀endpoint:Config G ((C).side j p),
    flags ((C).path.rep N p j).p.threshold endpoint=∅ → ∀s:(J₀).Mode,
    ∀V₀:Fin 3→ℝ,(∀i,charge (y i)≤ max 1 (2*V₀ i)) →
    let source:=WilsonOriginalMicroscopicEntranceGridRow.old R d live.le (fun i=>displayed R (d i) (x i) (turn i)) o
    let seen:=actualTransport (C) (N:=N) (WilsonOriginalMicroscopicEntranceEarlier.face source s) live.le
    let refund:=fun U=>∏i∈s.val,(charge (y i):ℂ)*(arm i).2.1 U
    Integrable (fun U=>P.eval U • refund U) (prior G _) ∧
      ‖actualTransport (C) (N:=N) (fun U=>seen U-refund U) height endpoint‖≤
        (∏i∈s.val,max 1 (2*V₀ i))*((H f)^target)⁻¹:=by
  obtain ⟨f₀,sale⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalPublicSale.original R d simple shop)
  obtain ⟨f₁,mounted⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalMounted.original R d simple pace wage)
  have goals:=Filter.eventually_all.mpr (fun i:I=>eventually_ge_atTop ((C).ref (d i)))
  obtain ⟨f₂,age⟩:=eventually_atTop.mp goals
  filter_upwards [WilsonSeparatedPrefixCanonicalClearPublic.original R d simple shop pace cater wage nested window target t,
    eventually_ge_atTop (max f₀ (max f₁ f₂)),(RG01.Physical.hats simple (A)).eventually_ge_atTop 1] with j price late heat
  intro N p f height live V r home enrolled x turn o route P y data arm filed span fixed size apart course parent alpha endpoint clearW s V₀ costs source seen refund
  have heads:=price N p f height live V r home enrolled x turn o route filed span fixed size apart course parent alpha endpoint clearW s
  have hp:1≤H f:=heat.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le height)
  obtain ⟨q,fit,_,paid,_,bright,_,_,_⟩:=sale f (by omega) N p live V r home enrolled x turn o t filed
  let B:=WilsonReflectedPublicMountedInvoice.wage R f
  have warm:=zero_lt_one.trans_le hp
  obtain ⟨_,_,_,_,_,_,c,M,_,_,burn,towed,row,_,_⟩:=
    mounted f (by omega) N p live.le fixed o q (fun _=>(H f^t)⁻¹) (fun _=>B)
      (fun _=>inv_pos.mpr (pow_pos warm _)) (age f (by omega)) fit paid
  have same(i:Fin 3)(U):(arm i).2.1 U=(q i).exponentialEntry (o i) ((C).localSection (d i)) P U:=congrFun (bright i) U
  have int:Integrable (fun U=>(P.eval U:ℂ)*∏i∈s.val,(arm i).2.1 U) (prior G _):=by
    simpa only [same] using WilsonOriginalMicroscopicEntranceHeadIncome.original R live.le o _ c M burn towed row s
  let F:=fun U=>P.eval U • actualTransport (C) (N:=N) (fun W=>∏i∈s.val,(charge (y i):ℂ)⁻¹*source i W) live.le U
  let A₀:=WilsonOriginalMicroscopicEntranceHeadCharge.amount (fun i=>charge (y i)) s
  constructor
  · convert int.smul A₀ using 1
    funext U
    simp only [refund,A₀,WilsonOriginalMicroscopicEntranceHeadCharge.amount,Finset.prod_mul_distrib,Complex.real_smul,Pi.smul_apply,smul_eq_mul]
    ring
  · have held:=WilsonOriginalMicroscopicEntranceHeldCharge.original (n:=0) R d (by omega : f+0≤N)
      (fun i=>displayed R (d i) (x i) (turn i)) o (fun i=>charge (y i))
      (fun i=>WilsonThermometerMarchSource.charged (y i)) s F (fun _=>rfl) (fun i=>(arm i).2.1) int height endpoint
    change actualTransport (C) (N:=N) (fun U=>seen U-refund U) height endpoint=A₀*(readingAt R (N:=N) F height endpoint-_) at held
    rw [held,norm_mul]
    have chargeBound:‖A₀‖≤∏i∈s.val,max 1 (2*V₀ i):=by
      simp only [A₀,WilsonOriginalMicroscopicEntranceHeadCharge.amount,norm_prod,Complex.norm_real]
      exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun i _=>by simpa only [Real.norm_of_nonneg (WilsonThermometerMarchSource.charged (y i)).le] using costs i)
    apply mul_le_mul chargeBound _ (norm_nonneg _) (le_trans (norm_nonneg _) chargeBound)
    simpa only [F,source,WilsonOriginalMicroscopicEntranceGridRow.old,WilsonOriginalMicroscopicEntranceGridRow.pin,
      WilsonAddressedPublicGridRooms.top R live.le] using heads

end YM.Integration.WilsonOriginalMicroscopicEntrancePublicHeld
end
