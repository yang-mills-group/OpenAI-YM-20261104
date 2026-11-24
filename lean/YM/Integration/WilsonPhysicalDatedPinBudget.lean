import YM.Integration.WilsonPhysicalNodalCapturedWord
import YM.Integration.WilsonPhysicalNodalTerminal

/-! Numerical cost of an actual finite-cutoff Schwinger pin. The two
remaining independent comparisons use the funded terminal sheet, its
prescribed inversion board, and the specific public target at this pin. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonPhysicalDatedPinBudget
open Function Filter Finset MeasureTheory Lattice Wilson RG Source Labels Marker Multi Tree
open QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak QuadraticLocal.Mentor QuadraticLocal.Affinity QuadraticLocal.Sunrise
open Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV AllOrder.Transit
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular WilsonOriginalSeparatedMask
open Comparison.Density.Transport Pert.Asymptotics Planned.GuardedAtom Extra.Histories Next.Foundations
open RG16 RG16.Literal Trace.Physical.GermGraph XSpace XSpace.Normalize XSpace.Rose XSpace.Cirrus
open RegulatorIR.FVAAlt2 Trace.Pilot OPE
open WilsonMovingForkHeterogeneousCut (Filed)
open WilsonMovingForkMixedSeed (doses product)
open WilsonMovingForkSeededPoint (seats)
open WilsonMovingForkPrintedFile (row parent allSlots)
open WilsonMovingForkTerminalFile (programme)
open WilsonMovingForkDepositedPrint (polynomial)
open WilsonMovingForkChronologicalTable (density)
open WilsonMovingForkChronologicalSale (Mounted)
open WilsonReceivedChronologicalDualInterval (Owned)
open WilsonOriginalPublicPivotReflected (board evaluated)
open WilsonOriginalPublicNodalSeed (vector)
open WilsonOriginalTwoFlatGridCapture (word)
open WilsonThermometerUnitFilingCoarse (reading)
open WilsonThermometerUnitFilingFlatTelescope (numerator)
open WilsonMacroscopicRichCaptureFilingBudget (capital)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G)(simple:G.Simple){m k:ℕ}(hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → AllOrder.Floe.Layout G)(Γ:ℕ → Pace.Coin){φ:ℕ → ℕ}
  (books:Mentor.Offices.Books D R.rolls Q φ)(ahead:Mentor.Forecast D R.rolls Q φ books)
local notation "C" => R.family

theorem original (cost n:ℕ):∃start:ℕ,∀{N per v L u c site:ℕ},0 < v → start ≤ v →
  ∀ (uv:u ≤ v)(vc:v ≤ c)(ck:c < v+L)(kn:v+L ≤ N)(sk:site ≤ v+L),
  (C).S.a v/(C).S.a (v+L) ≤ ((C).path.levels.clock.hatBeta v)^cost →
  WilsonCenteredCaptureClock.first R simple ≤ c → Opened C 0 u per → Opened C 0 v per →
  ∀(W:Initialize G)(d:Fin n → ℕ)(file:Filed R d (v+L))(Y:(ℕ×ℕ) → (C).book.Vector d)
    (issued:WilsonMovingForkTerminalFile.Source R d v (v+L))(addr:Fin n → Cover)(node:Sample n)
    (q p size:ℕ)(η:ℝ)(Ψ:∀i,Rep G ((C).side i per))(Z:Support ((C).side c per))(rad:ℕ),
  let uk:=uv.trans (vc.trans ck.le)
  let w:=doses R d file.station (N:=N) (per:=per) (file.A N per) (Y (N,per))
  let pin:=seats (R:=R) sk per addr
  let prog:=programme issued
  let b:=prog N per w pin c ck
  let g (i:ℕ):=regulatorRun (C) N per i
  let rep:=(C).path.rep N per c
  let S:=allSlots n
  let native:=word R d site N per (sk.trans kn) addr (Y (N,per))
  let plant:=product R d (N:=N) pin w
  let deposited:=polynomial (issued N per kn w pin v le_rfl (vc.trans_lt ck)) (g v)
  let filed:=evaluated q (g (v+L)) (board R W d (vector R d (N:=N) (per:=per) file (Y (N,per))) node univ)
  0 ≤ η → (∀i,wrap ((C).side (v+L) per) (node.layout i)=pin i) →
  (∀i,v ≤ i → i ≤ v+L → Mounted prog N per w pin i) →
  (∀j,v ≤ j+1 → j+1 < v+L → Owned (N:=N) R simple hk D Q π Γ Ψ books ahead
    (density prog N per w pin) j u v S (p+1) size η) →
  0∈Z → (∀a,parent R ck.le per pin a∈Z) → (∀a,separation (parent R ck.le per pin a) 0 ≤ rad) →
  ∀{ord seats shelf ext:ℕ}{stripU slack gross:ℝ},
    0 ≤ b.strip → b.order ≤ ord → 1 ≤ seats → n ≤ seats → (∑a,b.load a) ≤ shelf →
    Invoice.Supports rep.p stripU (rep.p.supportExponent+2) (g c) b.strip slack →
    Invoice.price rep.p stripU (ord+shelf+1) seats (rep.p.supportExponent+2) slack G ≤
      (2:ℝ)^(ord+shelf+1)*(3*(g c)⁻¹)^2 →
    (∑a:b.index,Real.exp (b.strip*(b.binder a).length)*WilsonIndependentCollarSlateIntensity.amount
      (b.copies a) (b.binder a).center) ≤ gross*(3*(g c)⁻¹)^ext →
    let cap:=((2:ℝ)^(ord+shelf+1))^2*max 1 gross*(3*(g c)⁻¹)^((∑a,b.load a)+1+2+ext)
    ∃C₀ C₁:ℝ,0 ≤ C₀ ∧ 0 ≤ C₁ ∧ C₀ ≤ cap ∧ C₁ ≤ cap ∧
    let height:=WilsonPlantedOrdinary.fare rep.p Z (fun _:Fin n=>1) C₀ C₁ rad ((C).localSection 0)
      (C).params (price G (max rep.p.order rep.p.power)) (R.alloy.B.a.clock.forcedAllowance c)
      (LocalComparison.forcedDivisor C c) S
    let expense:=(4*(cost:ℝ)/Real.log 3)*(WilsonOriginalOrdinaryFaceOrder.constant S S.val.card+
      η*(2:ℝ)^(p+1)*WilsonOriginalCensusFiledHousing.fare S size)*(g v)^p
    ∀target:ℂ,WilsonPhysicalOrdinaryPinExpense.price R W d Y (per:=per) file sk kn uk addr node q target ≤
      ‖WilsonOriginalTwoFlatGridScaling.gap R N per u (uk.trans kn) native‖+
      ‖reading R (N:=N) (credit C N per 0 native (v+L) kn) u uk-
        reading R (N:=N) (numerator R N per (v+L) plant) u uk‖+
      (expense+2*capital C c height 1*Real.exp (-((C).S.scale c-(C).S.scale v)/8)+
        ‖deposited.part S-filed‖)+‖filed-target‖:=by
  obtain ⟨start,paid⟩:=WilsonPhysicalNodalCollar.original R simple hk D Q π Γ books ahead cost n
  refine ⟨start,?_⟩
  intro N per v L u c site vp live uv vc ck kn sk optical first ou ov W d file Y issued addr
    node q p size η Ψ Z rad uk w pin prog b g rep S native plant deposited filed ep located minted
    each center house near ord seats shelf ext stripU slack gross hs dep oc names fit fund fare salary cap
  have income:=paid vp live uv vc ck.le kn sk optical W d file (Y (N,per)) prog addr node q p size η Ψ
    ep located minted each
  have last:=WilsonPhysicalNodalTerminal.original R issued (vc.trans_lt ck) kn w pin
  obtain ⟨C₀,C₁,np,ng,bp,bg,between⟩:=WilsonPhysicalNodalCapturedWord.original R simple prog w pin ck kn
    ou.post uv vc first ou ov Z center house rad near hs dep oc names fit fund fare salary
  refine ⟨C₀,C₁,np,ng,bp,bg,?_⟩
  intro height expense target
  unfold WilsonPhysicalOrdinaryPinExpense.price
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  change _ ≤ expense+‖reading R (N:=N) (numerator R N per c (row prog N per w pin c)) u (uv.trans vc)-
    reading R (N:=N) (numerator R N per c (row prog N per w pin c)) v vc‖+
    ‖reading R (N:=N) (numerator R N per v (row prog N per w pin v)) v le_rfl-filed‖ at income
  rw [last] at income
  exact income.trans (add_le_add (add_le_add le_rfl between) le_rfl)

end YM.Integration.WilsonPhysicalDatedPinBudget
end
