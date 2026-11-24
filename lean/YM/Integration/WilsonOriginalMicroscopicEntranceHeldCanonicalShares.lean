import YM.Integration.WilsonMeasuredPublicEntranceCanonicalShares
import YM.Integration.WilsonMeasuredPublicEntranceCanonicalClearOwner

/-! Both actual canonical hard owners share the registered mixed ordinary peers at a clear original held endpoint. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeldCanonicalShares
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open QuadraticLocal WilsonThermometerMixedCollarSubpower
open WilsonMeasuredCoefficientTransport WilsonMeasuredPublicEntranceOwnerGas
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "S₂" => Marks (V×Bool)
local notation "V₂" => V×Bool
local notation "X" => Unit×(V×Bool)

open WilsonSeparatedPrefixCanonicalClearConvolution (readingAt)
open WilsonMeasuredPublicEntranceOrderedPeers WilsonMeasuredPublicEntrancePeerShares
theorem original (d:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (nested:WilsonPositionProgramNestedLengths.Nested R.rolls)(cater:Cater (C) R.doors)
    (wage:WilsonReportLampForecast.Ready (A))
    (aperture power gross:ℕ)(C₀:ℝ)(posC:0≤C₀):
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j≤k+1) (_kn:k<N)
      (o:V → Site ((C).side (k+1) p))(q:Bool → ∀i,Coefficient ((C).labels.level (d i)) ((C).side (k+1) p))
      (B:Bool → V → ℝ)(w₀ wY:V → ℝ)(route:∀t,X → Site ((C).side t p)),
    let f:=k+1
    let P:=(C).path.rep N p f
    let H:=(A).clock.hatBeta f
    let a:=fun b=>WilsonSeparatedPrefixCanonicalMounted.salary R d f p (q b) (B b)
    ∀(W:Rep G ((C).side f p)),W.p=P.p → ∀ {arg I:Type},∀ [Countable I],∀(Y:Lamps arg I G W.p o S₀)(x:arg),
    (∃ (raw:V → Config G ((C).side f p) → ℂ), ∃ h, ∃ F:Config G ((C).side f p) → Poly S₀,
      Served P raw h F o w₀ P.p.supportExponent 1) →
    ((A).params f).supportExponent=100 → (∀v,0<w₀ v) → (∀v,0<wY v) → (∀b i,0≤B b i) →
    (∀i,(C).ref (d i)≤f) → (∀b i,(q b i).Format (o i) (C).params P) →
    (∀b i,(q b i).remBound (o i) P (LocalComparison.forcedDivisor (C) f) (B b i)) →
    Y.Paid wY W.p.B (W.p.supportExponent+2) 1 →
    (∀v,(w₀ v)⁻¹≤H^gross) → (∀v h b,a h v+B b v≤H^gross) →
    (∀v,(wY v)⁻¹≤Real.exp (C₀*(1+Real.log H)*(scale H)^3)) →
    5≤P.p.B → (∀a b:V,a≠b → P.p.B^2+1 ≤ separation (o a) (o b)) →
    (C).S.a j/(C).S.a f≤H^aperture →
    route f=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j≤t → t<f → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    2≤((A).budget j).supportExponent →
    ∀endpoint:Config G ((C).side j p),flags ((C).path.rep N p j).p.threshold endpoint=∅ →
    ∀s:(S₀).Mode,∀m∈shares s.val.toList,∀tag:Bool,
    let soft:=fun b=>incidence (N:=N) R d o (q b)
    let trial:=fun i U=>(Y.log x U).part ((S₀).fire i)
    let hard:=fun i=>account (q tag i) P
    ‖readingAt R (N:=N) (WilsonMeasuredPublicEntranceFlatShares.owned R s.val (soft false) trial (soft true) hard m)
      height endpoint‖≤(H^power)⁻¹:=by
  filter_upwards [WilsonMeasuredPublicEntranceCanonicalClearOwner.original R d simple pace nested cater wage
    aperture power gross C₀ posC] with j original
  intro N p k height kn o q B w₀ wY route f P H a W same T I inst Y x invoice support wp yp bp ref fit remn
    lamps gross₀ grossY time thick far window top lineage deep endpoint clear s m inserted tag
  let choice:=WilsonMeasuredPublicEntranceShareRoster.pick m
  let chosen:=fun i=>q (choice i) i
  let wage:=fun i=>B (choice i) i
  let lamp:=hosted same Y
  have issued:lamp.Paid wY P.p.B (P.p.supportExponent+2) 1:=
    (WilsonMeasuredPublicEntranceOrderedPeers.paid same Y wY P.p.B (P.p.supportExponent+2) 1).mpr (same ▸ lamps)
  have roots:=WilsonMeasuredPublicEntranceShareRoster.original (K:=ℂ) s.val m inserted 0 0 0
  have charge:=original N p k height kn o chosen wage (B tag) w₀ wY route lamp x
    invoice support wp yp (bp tag) ref (fun i=>fit (choice i) i) (fun i=>remn (choice i) i) issued
    gross₀ (fun i=>grossY i (choice i) tag) time thick far window top lineage deep
    m.after.toFinset m.atName (d m.atName) (q tag m.atName) (fit tag m.atName) (remn tag m.atName)
    endpoint clear s roots.1
  let soft:=fun b=>incidence (N:=N) R d o (q b)
  let tr:=fun i U=>(Y.log x U).part ((S₀).fire i)
  let seen:=fun i U=>if i∈m.after.toFinset then (lamp.log x U).part ((S₀).fire i) else
    (chosen i).exponentialEntry (o i) ((C).localSection (d i)) P U
  have peers (i:V)(U:Config G ((C).side f p)):
      WilsonMeasuredPublicEntranceFlatShares.rest R (soft false) tr (soft true) m i U=seen i U:=by
    dsimp only [WilsonMeasuredPublicEntranceFlatShares.rest,WilsonMeasuredPublicEntranceShareRoster.field,
      WilsonMeasuredPublicEntranceShareRoster.head,seen,soft,tr,incidence,chosen,choice,lamp]
    rw [WilsonMeasuredPublicEntranceOrderedPeers.log]
    simp only [List.mem_toFinset]
    cases sel:WilsonMeasuredPublicEntranceShareRoster.pick m i <;> simp [P,f]
  change ‖readingAt R (N:=N) (fun U=>account (q tag m.atName) P U*
    ∏i∈s.val.erase m.atName,WilsonMeasuredPublicEntranceFlatShares.rest R (soft false) tr (soft true) m i U) height endpoint‖≤_
  simp_rw [peers]
  exact charge

end YM.Integration.WilsonOriginalMicroscopicEntranceHeldCanonicalShares
end
