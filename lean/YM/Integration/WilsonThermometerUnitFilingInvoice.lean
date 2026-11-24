import YM.Integration.WilsonThermometerUnitFilingWhole
import YM.Integration.WilsonThermometerUnitFilingShapeReceived

/-! The real received complete input and the independent matter filed at its original post are both tested against the same older vacuum. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingInvoice
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6
open Pert.Asymptotics Laurent Stationary Comparison.RG02 Comparison.RG02.Order Exterior Filter
open Extra.Histories Further.PhysicalPeriodLimitF933 Push.AbsoluteSums Planned.GuardedAtom

variable {G:Gauge} (R:Run G) (simple:G.Simple) {N per m k b:ℕ} (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q)
   (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
   (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (top:b≤N) {u:ℕ} (floor:m≤u) (ub:u≤b)
   (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ u)
open Source RG16 RG16.Literal WilsonThermometerUnitFilingCoarse Extraction Climb Bid
open WilsonThermometerCourseHearing WilsonThermometerCourseIntake WilsonThermometerUnitFilingCylinder
open WilsonThermometerCenteredAlgebra
open scoped Topology
open private smooth admitted from YM.Integration.WilsonThermometerUnitFilingDeposit
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "V" => Ψ b
local notation "W" => R.family.path.rep N per b
local notation "X" => Config G (R.family.side b per)


open scoped Classical BigOperators Topology
open Labels Source Push.Local Next.Foundations Planned.AtomRegular Trace.Physical.Germ
open RG16 RG16.Literal

open FVA1 OriginalForcedAddresses WilsonThermometerCourseHearing WilsonThermometerCourseIntake
open WilsonPositionThermometerCapStation WilsonThermometerCenteredAlgebra WilsonThermometerWeightedCapture
open WilsonCenteredCloseOccupiedSale WilsonCenteredCloseCaptureWallet

open RG12 Primitives.GCC.Anchor
local notation "z!" => ((N,per):UVIndex)
local notation "J!" => Stock.census (Fin 3)

theorem deposited (station:Group R.family 6) (Q:Poly J!)
    (qualified:WilsonThermometerUnitFilingShapeReceived.Qualified R station simple z!)
    (o:Positions (Fin 3) (R.family.side N per)) :
    credit R.family N per 0 (WilsonThermometerUnitFilingCylinder.source R station z! o.origin Q) b top=
      fun U=>(total (incoming R station simple top o U) Q).part full:=by
  funext U
  rw [WilsonThermometerUnitFilingCylinder.source,IntrinsicProductLinearity.credit_sum R.family N per 0 b top _ _
    (smooth R station z! o.origin),Finset.sum_apply,affine]
  simp only [Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl;intro s _
  apply congrArg (_ * ·)
  exact (congrFun (qualified.1 b top o s) U).symm

theorem credit_live (Y:Cut R.family N per) (cont:Continuous Y) : Integrable (credit R.family N per 0 Y b top) (prior G _) :=by
  rw [credit,pow_zero,one_smul]
  exact Push.GridApprox.pushTo_integrable R.family.path N per top _
    (((Complex.continuous_ofReal.comp (bare_cont _)).mul cont).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))

include simple way D Q ticket π Γ Ψ course floor ub gate in
theorem sale (station:Group R.family 6) (table:Poly J!) (qualified:WilsonThermometerUnitFilingShapeReceived.Qualified R station simple z!)
    (o:Positions (Fin 3) (R.family.side N per)) (nominal:X→ℂ) (y:Site (R.family.side b per))
    (h:Coefficient F₀ (R.family.side b per)) (law:h.Format y R.family.params V) {M:ℝ}
    (income:h.remBound y V (LocalComparison.forcedDivisor R.family b) M) (nonneg:0≤M)
    (sold:∀U,h.density y S₀ V U=(total (incoming R station simple top o U) table).part full-((W).eval U:ℂ)*nominal U) :
    let revenue:=credit R.family N per 0 (WilsonThermometerUnitFilingCylinder.source R station z! o.origin table) b top
    let reported:=fun U=>((W).eval U:ℂ)*nominal U
    ∀j,u≤j→∀jb:j≤b,‖reading R (N:=N) revenue j jb-reading R (N:=N) reported j jb‖≤‖h.x 0‖+5*M:=by
  intro revenue reported
  have eq : revenue-reported=h.density y S₀ V:=by
    dsimp only [revenue,reported];rw [deposited R simple top station table qualified o];funext U;exact (sold U).symm
  have hd:= (WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course (floor.trans ub) top S₀ R.family.params y h law income).2
  have ht:Integrable revenue (prior G _):=credit_live R top _ (admitted R station z! o.origin table)
  have hr : Integrable reported (prior G _):=by
    have different : revenue-h.density y S₀ V=reported:=by rw [←eq,sub_sub_cancel]
    rw [←different];exact ht.sub hd
  obtain ⟨one,_⟩:=WilsonThermometerUnitFilingWhole.original R simple way D Q ticket π Γ Ψ course top floor ub gate y h law income nonneg
  intro j uj jb
  have ears:=WilsonThermometerUnitFilingRaw.add R (N:=N) (h.density y S₀ V) reported hd hr jb
  rw [←eq,sub_add_cancel] at ears
  rw [ears,add_sub_cancel_right,eq]
  exact one j uj jb

end YM.Integration.WilsonThermometerUnitFilingInvoice
