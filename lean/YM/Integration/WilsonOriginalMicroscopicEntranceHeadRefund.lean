import YM.Integration.WilsonOriginalMicroscopicEntranceHeadIncome
import YM.Integration.WilsonSeparatedPrefixCanonicalTwoFlat
import YM.Integration.WilsonSeparatedPrefixCanonicalQuote
import YM.Integration.WilsonSeparatedPrefixCanonicalCash
import YM.Integration.WilsonSeparatedPrefixCanonicalSourceDebit

/-! The complete physical separated source at each of its actual earlier flat
readings. All powers and the original election precede N and period. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonOriginalMicroscopicEntranceHeadRefund
open Function Filter Set Finset MeasureTheory Lattice Wilson Labels RG Source Marker Push AbsoluteSums
open Push.Local RG12 Extra.Histories Extra.Histories.Relay Ac GridApprox.Nil MergeProof MergeProof.Accent MergeProof.Menu
open RG05Readout RG05Readout.Native RG05Readout.Address RG05Readout.Many RG05Readout.Pantry Records
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Mallow Motion Bandage
open Extra.Multi Extra.Trajectories ConnectedActivityE6 Pressure Extra.Iteration Next.Foundations Lotus
open Trace.Physical.GermGraph Lodestar WilsonThermometerUnitFilingCoarse WilsonOriginalCompanionLinearFiling
open WilsonOriginalOccupiedStencil WilsonOriginalOccupiedSource
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)
local notation "V" => Fin 3
local notation "C" => R.family
local notation "A" => R.family.path.levels
local notation "S₀" => Marks V
local notation "S₂" => Marks (V×Bool)
local notation "V₂" => V×Bool
local notation "X" => Unit×(V×Bool)

theorem original (d:V → ℕ)(simple:G.Simple)(pace:WilsonWindowReportingPace.Slow R.kit)
    (cater:Cater (C) R.doors)(bank:WilsonThermometerClusterProjectionBudget.Ready (A))
    (wage:WilsonReportLampForecast.Ready (A))(nested:WilsonPositionProgramNestedLengths.Nested R.rolls)
    (window price room target:ℕ):
    ∀ᶠ j:ℕ in atTop,∀N p k (height:j+2≤k+1) (kn:k<N) (l:ℕ)
      (o:V → Site ((C).side (k+1) p))(w₀ B:V → ℝ)(route:∀t,X → Site ((C).side t p))(anchor:X)
      (q:∀v,Coefficient ((C).labels.level (d v)) ((C).side (k+1) p))(F:Config G ((C).side (k+1) p) → Poly S₀),
    let P:=(C).path.rep N p (k+1)
    let φ:=fun v=> (q v).exponentialEntry (o v) ((C).localSection (d v)) P
    let h:=fun v=>profile P.activities (q v).forced
    l≤room → (C).S.a j/(C).S.a (k+1)≤((A).clock.hatBeta (k+1))^window →
    (∀v,(w₀ v)⁻¹≤((A).clock.hatBeta (k+1))^price) →
    (∀v,((C).labels.level (d v)).coeffSize (q v).x≤((A).clock.hatBeta (k+1))^price) →
    (∀v,B v≤((A).clock.hatBeta (k+1))^price) →
    ((A).params (k+1)).supportExponent=100 → (∀v,0<w₀ v) → (∀v,(C).ref (d v)≤k+1) →
    (∀v,(q v).Format (o v) (C).params P) →
    (∀v,(q v).remBound (o v) P (LocalComparison.forcedDivisor (C) (k+1)) (B v)) →
    Served P φ h F o w₀ P.p.supportExponent 1 → 5≤P.p.B →
    (∀u v:V,u≠v → P.p.B^2+1≤ separation (o u) (o v)) →
    route (k+1)=(o∘Prod.fst) ∘ Prod.snd →
    (∀t,j+1≤t → t<k+1 → route t=((A).clock.op t p).ratio.parent ∘ route (t+1)) →
    (∀i,coverNumber ((C).path.rep N p (j+1)).p.B ({route (j+1) anchor,route (j+1) i}:Support _)≤l) →
    ((A).clock.op j p).ratio.parent (route (j+1) anchor)=0 →
    ∀u:ℕ,(C).ref 0≤u → ∀uj:u≤j,Opened (C) 0 u p → Opened (C) 0 j p → ∀s:(S₀).Mode,
    ∀(slots:ℕ)(live:(k+1)+slots≤N)(Y:∀a:Fin 3,R.family.label (d a))(χ V₀:Fin 3→ℝ),
    (∀a,0<χ a)→(∀a,χ a≤ max 1 (2*V₀ a))→
    let input:=WilsonOriginalMicroscopicEntranceGridRow.old R d ((Nat.le_add_right (k+1) slots).trans live) Y o
    (∀U,(F U).part s=P.eval U • actualTransport (C) (N:=N)
      (fun T=>∏a∈s.val,(χ a:ℂ)⁻¹*input a T) kn U)→
    let field:=actualTransport (C) (N:=N) (WilsonOriginalMicroscopicEntranceEarlier.face input s) kn
    ‖actualTransport (C) (N:=N) (fun U=>field U-∏a∈s.val,(χ a:ℂ)*φ a U) (uj.trans (by omega)) 1‖≤
      (∏a∈s.val,max 1 (2*V₀ a))*(((A).clock.hatBeta (k+1))^target)⁻¹:=by
  obtain ⟨j₀,mounted⟩:=eventually_atTop.mp (WilsonSeparatedPrefixCanonicalMounted.original R d simple pace wage)
  filter_upwards [WilsonSeparatedPrefixCanonicalTwoFlat.original R d simple pace cater bank wage nested window price room target,eventually_ge_atTop j₀] with j report ready
  intro N p k height kn l o w₀ B route anchor q F P φ h housed span wallet projected rem fixed positive ref fit sal served size apart course parent housing zero u hu uj ou oj s slots live Y χ V₀ pos costs input law field
  have fee:=report N p k height kn l o w₀ B route anchor q F housed span wallet projected rem fixed positive ref fit sal served size apart course parent housing zero u hu uj ou oj s
  obtain ⟨_,_,_,_,_,_,c,M,_,_,burn,towed,row,_,_⟩:=mounted (k+1) (by omega) N p kn fixed o q w₀ B positive ref fit sal
  have int:=WilsonOriginalMicroscopicEntranceHeadIncome.original R kn o φ c M burn towed row s
  have held:=WilsonOriginalMicroscopicEntranceHeadCharge.original R d live Y o χ pos s (fun U=>(F U).part s) law φ int (uj.trans (show j≤k+1 by omega))
  change actualTransport (C) (N:=N) (fun U=>field U-∏a∈s.val,(χ a:ℂ)*φ a U) _ 1=_ at held
  rw [held,norm_mul]
  have charge:‖WilsonOriginalMicroscopicEntranceHeadCharge.amount χ s‖≤ ∏a∈s.val,max 1 (2*V₀ a):=by
    simp only [WilsonOriginalMicroscopicEntranceHeadCharge.amount,norm_prod,Complex.norm_real]
    exact Finset.prod_le_prod (fun _ _=>norm_nonneg _) (fun a _=>by simpa only [Real.norm_of_nonneg (pos a).le] using costs a)
  exact mul_le_mul charge fee (norm_nonneg _) (le_trans (norm_nonneg _) charge)

end YM.Integration.WilsonOriginalMicroscopicEntranceHeadRefund
end
