import YM.Integration.WilsonMacroscopicRichEnrolledGrid
import YM.Integration.WilsonMacroscopicRichOrderedPartners

/-! The signed original macroscopic discrepancy as a finite sum of
one substituted original operator with all of its measured or nominated
partners and the far field on a single physical configuration. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonMacroscopicRichGridDefects
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
def prescription (x:Sites)(i:V)(U:UV):ℂ:=
  if i∈s.val then
    ((VariableScaling.tests (ActualOriginalQInitialInput.scales R hG v J A d Q x μ ord) (tests x)) i).val 0 *
      WilsonMacroscopicRichOriginalPortfolio.observation R Q (d.level+1) d.period (v i) (μ-R.family.S.scale d.cutoff) (ord i) (x i) U
  else 1

local notation "nominated" => prescription R hG v J A d Q μ ord tests s

theorem fields (x:Sites)(U:UV):(submitted) x U=∏i:V,nominated x i U:=by
  dsimp only
  rw [WilsonMacroscopicRichQSiteInput.sites]
  exact (Fintype.prod_ite_mem s.val _).symm

theorem continuousPrescription (x:Sites)(i:V):Continuous (nominated x i):=by
  unfold prescription
  by_cases hi:i∈s.val
  · simp only [if_pos hi];apply continuous_const.mul
    apply continuous_finsetSum;intro a _
    exact continuous_const.mul (R.family.continuousO ..)
  · simp only [if_neg hi];apply continuous_const

variable {f:Extraction.Order}{S:Table R.family.book}{F:Final R.family f S}(L:Layout F)
    (h:V → ℕ)(w:(i:V) → R.family.label (h i))(Y:(t:ℕ×ℕ) → (i:V) → Emblems R.family (h i))
    {r cap:ℝ}(rp:0<r)(Ψ:Wave V)(g:Body){k m:ℕ}(top:k≤d.level+1)(paid:m≤d.level+1)
    (enclosed:∀x∈tsupport Ψ.val,∀i,‖x i‖≤cap)(room:r*cap+2*R.family.S.a k<R.family.S.radius d.period)
local notation "positions" => weighted R h k m (N₀) r Ψ g
local notation "marked" => micros R h (fun i=>atRef L (h i) r (d.level+1,d.period) (w i))
local notation "physical" => WilsonSeparatedOriginalSlabWatchContrast.full L h r w Y k m Ψ g (d.level+1,d.period)
local notation "trial" => WilsonMacroscopicRichSharedGrid.registered R (N₀) d.period (submitted) h (r:=r) Ψ g (k:=k) (m:=m)

local notation "physicalPart" => fun (x:Sites)(i:V)=>R.family.O (d.level+1) d.period (atRef L (h i) r (d.level+1,d.period) (w i)) (x i)

theorem changed (x:Sites)(U:UV):
    marked x U-(submitted) x U=
      ∑i:V,((physicalPart) x i U-nominated x i U)*
        WilsonMacroscopicRichOrderedPartners.partners (fun t=>(physicalPart) x t U) (fun t=>nominated x t U) i:=by
  rw [fields]
  exact WilsonMacroscopicRichOrderedPartners.original _ _

include rp top paid enclosed room in
theorem measured (ν:Measure UV)[IsFiniteMeasure ν](E:UV → ℂ)(continuousE:Continuous E):
    ∫U,(physical U-trial U)*E U ∂ν=
      ∑x:Sites,positions x*(∑i:V,∫U,
        ((physicalPart) x i U-nominated x i U)*
          WilsonMacroscopicRichOrderedPartners.partners (fun t=>(physicalPart) x t U) (fun t=>nominated x t U) i*E U ∂ν):=by
  rw [WilsonMacroscopicRichEnrolledGrid.tested R hG v J A d Q μ ord tests s L h w Y rp Ψ g top paid enclosed room ν E continuousE]
  apply Finset.sum_congr rfl;intro x _
  congr 1
  simp_rw [changed R hG v J A d Q μ ord tests s L h w x,Finset.sum_mul]
  rw [integral_finsetSum];intro i _
  have cp (j:V):Continuous ((physicalPart) x j):=R.family.continuousO ..
  have cq (j:V):Continuous (nominated x j):=continuousPrescription R hG v J A d Q μ ord tests s x j
  exact ((((cp i).sub (cq i)).mul (WilsonMacroscopicRichOrderedPartners.continuousPartners _ _ cp cq i)).mul continuousE).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

include rp top paid enclosed room in
theorem watched (W:Watch R.family):
    Wilson.moment (R.family.beta (N₀) d.period) (fun U=>(physical U-trial U)*W.plot (N₀) d.period U)=
      ∑x:Sites,positions x*(∑i:V,Wilson.moment (R.family.beta (N₀) d.period) (fun U=>
        ((physicalPart) x i U-nominated x i U)*
          WilsonMacroscopicRichOrderedPartners.partners (fun t=>(physicalPart) x t U) (fun t=>nominated x t U) i*W.plot (N₀) d.period U)):=by
  apply measured R hG v J A d Q μ ord tests s L h w Y rp Ψ g top paid enclosed room
  exact continuous_finsetProd _ fun i _=>R.family.continuousO (N₀) d.period (W.q i).1 (W.q i).2 (W.among (N₀) d.period i)

end YM.Integration.WilsonMacroscopicRichGridDefects
