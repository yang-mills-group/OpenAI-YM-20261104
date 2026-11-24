import YM.Integration.WilsonMacroscopicRichQSiteInput
import YM.Integration.WilsonMacroscopicRichSharedGrid

/-! The measured field and the deposited independent prescription are read
at identical fine sites against a single Wilson exterior. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichEnrolledGrid
open Function Filter Set MeasureTheory Lattice RG Wilson Source Labels Analysis Next.Foundations Push.Local
open PhysicalNext PhysicalNext.Repeat.Legato RG05Readout Address Native Pulse Flatten RGComparison.Core16
open OPE PhysMS Spec RG17 Extraction MergeProof.Accent Marker Precision Next.UVStress
open LocalComparison LocalComparison.Global IterationFour IterationFour.Vacuum FullQLocal
open FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric WilsonLimitConstruction QLocalOriginalQHistory
open WilsonSeparatedOriginalSlabWatchScalarMesh
open scoped Classical BigOperators Topology
variable {G:Gauge}{V:Type}[DecidableEq V][Fintype V]{B:MS.Local.Physical.Deck G}
    (R:Run G)(hG:G.Simple)(v:V → MS.Rake.Label B)(J:Request V)(A:NumericSchedule R.family J)
    (d:LocalFormal.Datum R.family (Stock.census V))(Q:MS.Land.Prescription B)(μ:ℝ)(ord:V → ℕ)
local notation "N₀" => d.level+1
local notation "UV" => Config G (R.family.side (N₀) d.period)
local notation "Sites" => V → Site (R.family.side (N₀) d.period)
variable (tests:(V → Site (R.family.side (d.level+1) d.period)) → TestSpace (ActualOriginalQPointSetup.request R v J).tests)
    (s:(Stock.census V).Mode)
local notation "submitted" => fun x:Sites => WilsonMacroscopicRichQSiteInput.observation R hG v J A d Q x μ ord (tests x) s
variable {f:Extraction.Order}{S:Table R.family.book}{F:Final R.family f S}(L:Layout F)
    (h:V → ℕ)(w:(i:V) → R.family.label (h i))(Y:(t:ℕ×ℕ) → (i:V) → Emblems R.family (h i))
    {r cap:ℝ}(rp:0<r)(Ψ:Wave V)(g:Body){k m:ℕ}(top:k≤d.level+1)(paid:m≤d.level+1)
    (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*R.family.S.a k<R.family.S.radius d.period)
local notation "positions" => weighted R h k m (N₀) r Ψ g
local notation "marked" => micros R h (fun i=>atRef L (h i) r (d.level+1,d.period) (w i))
local notation "physical" => WilsonSeparatedOriginalSlabWatchContrast.full L h r w Y k m Ψ g (d.level+1,d.period)
local notation "trial" => WilsonMacroscopicRichSharedGrid.registered R (N₀) d.period (submitted) h (r:=r) Ψ g (k:=k) (m:=m)

include rp top paid enclosed room in
theorem together (U:UV):physical U-trial U=∑x:Sites,positions x*(marked x U-(submitted) x U):=
  WilsonMacroscopicRichSharedGrid.together R (N₀) d.period (submitted) L h w Y rp Ψ g top paid enclosed room U

include rp top paid enclosed room in
theorem tested (ν:Measure UV)[IsFiniteMeasure ν](E:UV → ℂ)(continuousE:Continuous E):
    ∫U,(physical U-trial U)*E U ∂ν=
      ∑x:Sites,positions x*∫U,(marked x U-(submitted) x U)*E U ∂ν:=
  WilsonMacroscopicRichSharedGrid.tested R (N₀) d.period (submitted) L h w Y rp Ψ g top paid enclosed room ν E
    continuousE (fun x=>WilsonMacroscopicRichQSiteInput.continuousField R hG v J A d Q x μ ord (tests x) s)

include rp top paid enclosed room in
theorem watched (W:Watch R.family):
    Wilson.moment (R.family.beta (N₀) d.period) (fun U=>(physical U-trial U)*W.plot (N₀) d.period U)=
      ∑x:Sites,positions x*Wilson.moment (R.family.beta (N₀) d.period)
        (fun U=>(marked x U-(submitted) x U)*W.plot (N₀) d.period U):=by
  apply tested R hG v J A d Q μ ord tests s L h w Y rp Ψ g top paid enclosed room
  exact continuous_finsetProd _ fun i _=>R.family.continuousO (N₀) d.period (W.q i).1 (W.q i).2 (W.among (N₀) d.period i)

end YM.Integration.WilsonMacroscopicRichEnrolledGrid
