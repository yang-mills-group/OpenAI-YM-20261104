import YM.Integration.WilsonMovingForkChronologicalIncome
import YM.Integration.WilsonReceivedChronologicalDualInterval

/-! The original signed two-stop purchase pays the finite decoder's genuine
one-edge discrepancy on the preselected funded compact programme. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkChronologicalSale
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity QuadraticLocal.Sunrise Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato AllOrder.Transit.WheelP
open AnalyticBridge VerifiedReset RemainderComparison Push Push.PriceCompiler Push.AbsoluteSums
open Stationary Comparison.RG02 QuadraticLocal.Rebirth VowsR LocalComparison ConnectedActivityE6
open OPE.Therm Multi WilsonRootedKioskOccupiedSlip WilsonOriginalSeparatedRegular
open WilsonOriginalSeparatedMask Comparison.Density.Transport Pert.Asymptotics
open WilsonMovingForkChronologicalTable (ordinary density)
open WilsonMovingForkPrintedFile (Board Program)
open WilsonOriginalJointTrialHearing
open scoped BigOperators Classical
variable {G:Gauge}{R:Run G}{n K:ℕ}{d:Fin n→ℕ}(prog:Program R d K)
  (N per:ℕ)(w:∀a,R.family.label (d a))(pins:Fin n→Site (R.family.side K per))

def Mounted (i:ℕ):Prop:=
  ∀ik:i<K, let b:=prog N per w pins i ik
    let rep:=R.family.path.rep N per i
    let g:=regulatorRun R.family N per i
    ∃(ord seats shelf ext:ℕ)(stripU slack gross:ℝ),
      0 ≤ b.strip ∧ b.order ≤ ord ∧ 1 ≤ seats ∧ n ≤ seats ∧ (∑a,b.load a) ≤ shelf ∧
      0 ≤ rep.p.supportExponent+2 ∧
      Invoice.Supports rep.p stripU (rep.p.supportExponent+2) g b.strip slack ∧
      Invoice.price rep.p stripU (ord+shelf+1) seats (rep.p.supportExponent+2) slack G ≤
        (2:ℝ)^(ord+shelf+1)*(3*g⁻¹)^2 ∧
      (∑a:b.index,Real.exp (b.strip*(b.binder a).length)*WilsonIndependentCollarSlateIntensity.amount
        (b.copies a) (b.binder a).center) ≤ gross*(3*g⁻¹)^ext

theorem integrable {i:ℕ}(ik:i ≤ K)(kn:K ≤ N)(issued:Mounted prog N per w pins i):
    MeasureTheory.Integrable (density prog N per w pins i) (prior G _):=by
  rcases ik.lt_or_eq with younger|equal
  · obtain ⟨o,s,h,e,u,l,H,strip,dep,oc,names,fit,positive,support,fare,wage⟩:=issued younger
    exact WilsonMovingForkChronologicalIncome.lower prog N per w pins younger (ik.trans kn)
      strip dep oc names fit positive support fare wage
  · exact equal ▸ WilsonMovingForkChronologicalIncome.upper prog N per w pins kn

variable (simple:G.Simple){m j k:ℕ}(hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀i,Rep G (R.family.side i per))
  {φ:ℕ→ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(ahead:Mentor.Forecast D R.rolls Q φ books)

theorem original {u v b p size:ℕ}{η:ℝ}(uv:u ≤ v)(vb:v ≤ b)(vj:v ≤ j+1)(cut:j+2 ≤ K)(kn:K ≤ N)
    (old:Mounted prog N per w pins (j+1))(fresh:Mounted prog N per w pins (j+2))
    (sale:WilsonReceivedChronologicalDualInterval.Owned (N:=N) R simple hk D Q π Γ Ψ books ahead
      (density prog N per w pins) j u b (WilsonMovingForkPrintedFile.allSlots n) p size η):
    let s:=WilsonMovingForkPrintedFile.allSlots n
    ‖WilsonThermometerUnitFilingFlatTelescope.feeAt R N per v (WilsonMovingForkPrintedFile.row prog N per w pins) (j+1)‖≤
      (WilsonOriginalOrdinaryFaceOrder.constant s s.val.card+η*(2:ℝ)^p*WilsonOriginalCensusFiledHousing.fare s size)*
        (regulatorRun R.family N per b)^p:=by
  intro s
  rw [WilsonMovingForkChronologicalTable.dated prog N per w pins vj (by omega)
    (integrable prog N per w pins (by omega) kn old) (integrable prog N per w pins cut kn fresh)]
  exact WilsonReceivedChronologicalDualInterval.purchased R simple hk D Q π Γ Ψ books ahead _ sale uv vb

end YM.Integration.WilsonMovingForkChronologicalSale
