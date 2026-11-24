import YM.Integration.WilsonThermometerUnitFilingFlatThermometer
import YM.Integration.WilsonThermometerUnitFilingFlatArrival
import YM.Integration.WilsonThermometerUnitFilingFlatCells
import YM.Integration.WilsonThermometerRegisteredCells

/-! The genuine registered three-site pupil and its original finite Wick material, integrated at every permitted earlier terminal. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingCompactMaterial
open Filter Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler Further.PhysicalPeriodLimitF933
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Affinity Laurent Stationary Comparison.RG02 Comparison.RG02.Order ConnectedActivityE6
open scoped Classical BigOperators Topology

open Extra.Trajectories Primitives.GCC.Anchor WilsonThermometerCenteredAlgebra
open private flag_free sample_zero from YM.Integration.WilsonReceivedIdentityField
local notation "J" => Stock.census (Fin 3)

open WilsonFiniteOrdinaryInverse WilsonThermometerRegisteredCenteredInvoice WilsonThermometerCenteredScalar
open WilsonThermometerFiniteConnectedCells OPE.Therm Pert.Asymptotics WilsonPositionThermometerGradedSource
local notation "grades₀" => WilsonThermometerUnitFilingNamedFaces.grades

open MeasureTheory XSpace Cells RG12 WilsonThermometerCourseHearing
open WilsonThermometerUnitFilingFlatCells
local notation "fo" => WilsonThermometerCourseHearing.fired

theorem original {G : Gauge} (R : Run G) (simple : G.Simple)
    (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (φ : ℕ → ℕ)
    (width : ∀ a k : ℕ, k ≤ a → ∀ b : ℝ, R.alloy.delay.betaEntry a ≤ b →
      Real.exp ((Poetry.Agenda.seed D φ (Burn.horizon k) a)⁻¹ ^ 2) ≤ b)
    (order shelf k slots loss target : ℕ)
    (deep : 2*((target+loss+4)+1+3+1)+8≤order) (aged : (target+loss+4)+1+3+4≤3*k+2) :
    ∀ K:ℝ,0≤K → ∀ᶠ b:ℕ in atTop,∀(i:ℕ)(ib:i≤b),
    R.family.S.scale b-R.family.S.scale i ≤ K*Real.log (4*R.family.path.levels.clock.hatBeta b)+(1+Real.log (R.family.path.levels.clock.hatBeta b)) →
    ∀ {m N per : ℕ} (hk : Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
      (_fit : k ≤ R.alloy.B.a.clock.J i) (Q : D.Tab R.rolls)
      (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin) (Ψ : ∀ j, RG.Rep G (R.family.side j per))
      (_course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
      (books : Mentor.Offices.Books D R.rolls Q φ) (law : VowsR.LawScroll G φ)
      (_enrolled : VowsR.Chamber law R.kit D Q books) (_fund : Volume.Fund D R.rolls Q φ books R.alloy.delay)
      (hi : m ≤ i) (top : b<N) (ahead : Mentor.Forecast D R.rolls Q φ books),
    let cut:i<N:=ib.trans_lt top
    ∀ (r:ℝ) (profile:Test 3) (A:WilsonPositionThermometerCapStation.Group R.family 6),
      let cells:=CellsAt R N per r profile
      let here:=fun c:cells=>WilsonThermometerRegisteredCells.placement (R:=R) (N,per) c.val
      ∀ (L:∀c:cells, WilsonOriginalReceivedChain.Post (N:=N) R hk D Q π Γ Ψ books ahead
         WilsonThermometerCourseHearing.disks WilsonThermometerCourseHearing.sectors grades₀ order shelf slots i hi
         (WilsonThermometerCourseHearing.offered R A simple cut (here c)))
        (F:cells → Forest (R.family.path.levels.clock.op i per).ratio)
        (tag:cells → (R.family.path.levels.clock.op i per).Choices),
        let g:=Coat.gStep (R.family.path.rep N per (i+1)).beta
        let actual:=measured R A (N,per) (fun _=>0)
        let model:=fun c:cells=>
          let T:=Oak.student (n:=per) R hk D Q π Γ books hi (L c).op (L c).lesson ahead disks (L c).model order (L c).voter
          Poly.pass (WilsonRootedKioskOccupiedSlip.bare (rendered T (Ψ i).p g) fo (1:Config G (R.family.side i per)))
        let finite:=fun c:cells=>
          let Z:=Air.craft (L c).model (fun j=>((L c).model j).paint fo) grades₀ (π (i+1))
            (AllOrder.Floe.Step.tape (Burn.horizon k+2))
          Order.value (g:ℂ) (Order.ratio (Bulk.Fk ((RunFormalChain.fromRun R).step N i per cut) (F c) (tag c) Z 0 order))
        let unitPrice:=23*(|(Fintype.card (J).Mode:ℝ)*WilsonReceivedCloseOrdinaryGrade.invoice (J) 3 0 (target+loss+4) 1| *fee (J))
        (∀v:Fin 3,‖WilsonThermometerCenteredScalar.read actual {v}‖≤1) →
        (∀c:cells,∀v,g*(L c).w v≤1) → (∀c:cells,g^(loss+2)≤Poly.toll (L c).w full) →
        ‖(∑c:cells,weights R c*((model c)*properInvoice actual 1).part full)-
          (∑c:cells,weights R c*((finite c)*properInvoice actual 1).part full)‖≤
            (∫x:Points 3,‖profile x‖)*|unitPrice| *(4*regulatorRun R.family N per (b+1))^target:=by
  intro K kp
  have terminal:=WilsonThermometerUnitFilingFlatThermometer.original R simple D φ width order shelf k slots loss target deep aged
  filter_upwards [WilsonThermometerUnitFilingFlatArrival.original R simple kp terminal] with b booked
  intro i ib nearby m N per hk fit Q π Γ Ψ course books law chamber funds hi top ahead cut r profile A cells here L F tag
    g actual model finite unitPrice means capped unscaled
  have each:∀c:cells,‖((model c)*properInvoice actual 1).part full-
      ((finite c)*properInvoice actual 1).part full‖≤unitPrice*g^target:=by
    intro c
    exact ((booked i ib nearby).1 hk fit Q π Γ Ψ course books law chamber funds hi cut ahead disks sectors
      _ (L c) fo (F c) (tag c) A means (capped c) (unscaled c)).2
  have gg:= (booked i ib nearby).2 N per top
  have thermal:g^target≤(4*regulatorRun R.family N per (b+1))^target:=pow_le_pow_left₀ gg.1.le gg.2 _
  let paid:=|unitPrice| *(4*regulatorRun R.family N per (b+1))^target
  have ok:0≤paid:=mul_nonneg (abs_nonneg _) ((pow_nonneg gg.1.le target).trans thermal)
  rw [←sum_sub_distrib]
  calc
    _ ≤ ∑c:cells,‖weights R c‖*paid:=(norm_sum_le _ _).trans <| sum_le_sum fun c _=>by
      rw [←mul_sub,norm_mul]
      exact mul_le_mul_of_nonneg_left ((each c).trans (mul_le_mul (le_abs_self _) thermal
        (pow_nonneg gg.1.le _) (abs_nonneg _))) (norm_nonneg _)
    _ = (∑c:cells,‖weights R c‖)*paid:=(sum_mul ..).symm
    _ ≤ (∫x:Points 3,‖profile x‖)*paid:=mul_le_mul_of_nonneg_right
      (WilsonThermometerSupportedCells.variation R r profile) ok
    _ = _:=by unfold paid;ring

end YM.Integration.WilsonThermometerUnitFilingCompactMaterial
