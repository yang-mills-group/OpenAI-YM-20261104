import YM.Integration.WilsonSeparatedPrefixCanonicalClearQuote
import YM.Integration.WilsonSeparatedPrefixCanonicalClearCash
import YM.Integration.WilsonSeparatedPrefixCanonicalQuote
import YM.Integration.WilsonSeparatedPrefixCanonicalCash
import YM.Integration.WilsonSeparatedPrefixCanonicalSourceDebit

/-! The complete physical separated source at each of its actual earlier flat
readings. All powers and the original election precede N and period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 750000
noncomputable section
namespace YM.Integration.WilsonSeparatedPrefixCanonicalClearRate
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){V:Type}[Fintype V][DecidableEq V]
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "S₂" => Marks (V×Bool)
local notation "V₂" => V×Bool
local notation "X" => Unit×(V×Bool)

theorem original (d:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (cater:Cater (C) R.doors)
    (wage:WilsonReportLampForecast.Ready (A))(nested:WilsonPositionProgramNestedLengths.Nested R.rolls)
    (window price target:ℕ):
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j≤k+1) (_kn:k<N)
      (o:V → Site ((C).side (k+1) p))(w₀ B:V → ℝ)(route:∀t,X → Site ((C).side t p))
      (q:∀v,Coefficient ((C).labels.level (d v)) ((C).side (k+1) p))(F:Config G ((C).side (k+1) p) → Poly S₀),
    let P:=(C).path.rep N p (k+1)
    let φ:=fun v=> (q v).exponentialEntry (o v) ((C).localSection (d v)) P
    let h:=fun v=>profile P.activities (q v).forced
    (C).S.a j/(C).S.a (k+1)≤((A).clock.hatBeta (k+1))^window →
    (∀v,(w₀ v)⁻¹≤((A).clock.hatBeta (k+1))^price) →
    (∀v,((C).labels.level (d v)).coeffSize (q v).x≤((A).clock.hatBeta (k+1))^price) →
    (∀v,B v≤((A).clock.hatBeta (k+1))^price) →
    ((A).params (k+1)).supportExponent=100 → (∀v,0<w₀ v) → (∀v,(C).ref (d v)≤k+1) →
    (∀v,(q v).Format (o v) (C).params P) →
    (∀v,(q v).remBound (o v) P (LocalComparison.forcedDivisor (C) (k+1)) (B v)) →
    Served P φ h F o w₀ P.p.supportExponent 1 → 5≤P.p.B →
    (∀u v:V,u≠v → P.p.B^2+1≤ separation (o u) (o v)) →
    route (k+1)=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    2≤((A).budget j).supportExponent → ∀endpoint:Config G ((C).side j p),
    flags ((C).path.rep N p j).p.threshold endpoint=∅ → ∀s:(S₀).Mode,
    ‖WilsonSeparatedPrefixCanonicalClearConvolution.readingAt R (N:=N) (fun U=>(F U).part s) height endpoint-
       WilsonSeparatedPrefixCanonicalClearConvolution.readingAt R (N:=N) (fun U=>(P.eval U:ℂ)*(∏v∈s.val,φ v U)) height endpoint‖≤
      (((A).clock.hatBeta (k+1))^target)⁻¹:=by
  let wageCount:=(price+7)*Fintype.card V
  filter_upwards [WilsonSeparatedPrefixCanonicalClearQuote.original R d simple pace cater wage,
    WilsonSeparatedPrefixCanonicalClearCash.original (I:=V₂) R simple nested window wageCount target (Fintype.card V:ℝ),
    (RG01.Physical.hats simple (A)).eventually_ge_atTop (2+32*((Fintype.card V:ℝ)+1))] with j
    issue buyer hot N p k height kn o w₀ B route q F P φ h span wallet projected rem fixed positive ref fit salary stock size apart course parent alpha endpoint clearW s
  let x:=(A).clock.hatBeta (k+1)
  let b:=fun v=>((C).labels.level (d v)).coeffSize (q v).x
  let a:=WilsonSeparatedPrefixCanonicalMounted.salary R d (k+1) p q B
  let w:=WilsonSeparatedPrefixCanonicalWallet.seat w₀ a B
  let W:=w ∘ Prod.fst (β:=Bool)
  let τ:=Poly.toll (fun i=>w i^2) s
  let E:=WilsonSeparatedPrefixCanonicalTapRate.value R (k+1)
  let gross:=Real.exp (Fintype.card V:ℝ)*(E⁻¹*WilsonOriginalOccupiedStencil.price (Fintype.card V₂))*
      (∑t:(S₂).Mode,Poly.toll W t*WilsonSeparatedPrefixCanonicalClearHeard.roof R W t (k+1) j)
  let diff:=‖WilsonSeparatedPrefixCanonicalClearConvolution.readingAt R (N:=N) (fun U=>(F U).part s) height endpoint-
       WilsonSeparatedPrefixCanonicalClearConvolution.readingAt R (N:=N) (fun U=>(P.eval U:ℂ)*(∏v∈s.val,φ v U)) height endpoint‖
  have heat:2+32*((Fintype.card V:ℝ)+1)≤x:=
    hot.trans (WilsonStartup.Timing.hat_mono (A) (Gauge.slopeConstant_pos simple).le (by omega))
  have bp(v):0≤b v:=by unfold b Frame.coeffSize;positivity
  obtain ⟨wp,clear⟩:=WilsonSeparatedPrefixCanonicalSourceDebit.original heat price w₀ b B positive bp
    (fun v=>rem_nonneg (salary v)) wallet projected rem
  have heard:τ*diff≤gross:=issue N p k height kn o w₀ B route q F fixed positive ref fit salary stock size apart course parent alpha endpoint clearW s
  have tp:0<τ:=Poly.worth (fun i=>pow_pos (wp i) 2) s
  have gp:0≤gross:=(mul_nonneg tp.le (norm_nonneg _)).trans heard
  calc
    _ = τ⁻¹*(τ*diff):=by change diff=_;field_simp [tp.ne']
    _ ≤ τ⁻¹*gross:=mul_le_mul_of_nonneg_left heard (inv_nonneg.mpr tp.le)
    _ ≤ x^wageCount*gross:=mul_le_mul_of_nonneg_right (clear s) gp
    _ ≤ _:=buyer (k+1) height span W (fun i=>wp i.1)

end YM.Integration.WilsonSeparatedPrefixCanonicalClearRate
