import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalBill
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalRate
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalFiber
import YM.Integration.WilsonPhysicalHistoryRetainedSpringLocalControl

/-! On each true local thermal fiber, replacing the complete incoming regular
action by its independently filed masked spring costs little-o of the squared
coupling per site. Both normalized laws retain the genuine incoming forced gas. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.OriginalMarkedRunAction
open Filter Function Lattice RG Wilson WilsonStartup AnalyticBridge PhysicalNext PhysicalNext.Repeat Legato
open Pert.Asymptotics VerifiedReset RG01Estimate Time WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Physical WilsonLimitConstruction
open Collection Function Marker IterationFour.Vacuum Extra.Iteration Push Push.AbsoluteSums Push.AbsoluteSums.Animals Song Meadow
open WilsonVacuumPreResetRenderRank WilsonVacuumPreResetPeriodEntries
open scoped Topology BigOperators Classical
variable {G:Gauge}
open MeasureTheory OriginalMarkedRowCovariance WilsonHeldRetainedAction
open OriginalMarkedConditionalAction

def LocalSpringRead (R:Run G)(m N per r:ℕ)(Z:SeriesA G)(σ C ε:ℝ):Prop:=
  let j:=m+1
  let P:=R.family.path.rep N per j
  ∀(S:Support (R.family.side j per))(exterior:Config G (R.family.side j per))(W:Config G (R.family.side m per)),
  let ξ:=OriginalMarkedConditionalAction.patch S exterior
  let μ:=reference R N per m S exterior W
  let E:=reading R N per m S exterior W P
  let L (F:Config G (R.family.side j per)→ℂ):=read μ (fun u=>maskedSpringWeight R (N:=N) r Z σ C (ξ u)) (fun u=>F (ξ u))
  E 1=1 ∧ L 1=1 ∧ ∀(F:Config G (R.family.side j per)→ℂ)(B:ℝ),(∀u,‖F u‖≤B)→
    ‖E F‖≤B ∧ ‖L F‖≤B ∧ (Measurable F→‖L F-E F‖≤ε*S.card*(regulatorRun R.family N per j)^2*B)

theorem cofinal_spring_read (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(rows:FundedMarkedCoverRows.prices v R.kit)
    (render:WilsonVacuumPreResetRenderCalendar.Issued R.kit)(income:WilsonVacuumPreResetPrecursorReserve.Issued R.kit)
    (time:RG01Estimate.Chart.Barrier R.alloy (fun _ i=>((i:ℝ)+1)⁻¹))(W:Credit)(r cap:ℕ){ε:ℝ}(ep:0<ε):
    let V:=R.family.path.levels
    ∀ᶠm:ℕ in atTop,let j:=m+1
      ∀N,j<N→∀per,let C:=W.buy (zz V j)+zz V j*V.clock.loopCap j
      ∀σ Z,0<σ→σ⁻¹≤zz V j→Draw Z σ C→(∀a∈Z,3≤a.grade ∧ a.grade≤cap)→
      Z.length ≤ meterPre cap→LocalSpringRead R m N per r Z σ C ε:=by
  intro V
  filter_upwards [cofinal_spring_change R simple render income,cofinal_mask_source R simple render income,
    (tendsto_add_atTop_nat 1).eventually (spring_model_bill R simple v rows render income time W r cap one_pos),
    (tendsto_add_atTop_nat 1).eventually (spring_local_rate R simple ep)] with m oscs layout paid rate
  intro j N live per C σ Z sp small draw grades size
  let P:=R.family.path.rep N per j
  let A:Listing G (R.family.side j per):=⟨P.activities.reg,P.activities.forced⟩
  obtain ⟨t,stock⟩:=(oscs N live per A σ C sp small Z draw r).exists
  let M:=maskedSpringModel R N per j r Z σ C A t
  have bill:M.bill≤Time.forecastE V j:=(le_abs_self _).trans (by simpa only [one_mul] using (paid N per live A σ Z sp small grades size t))
  have borel:=score_meas R N per j r live.le Z σ C A t stock.2.1 (layout N live.le per A σ C sp small Z draw r t P.p.B)
  intro S exterior Wc ξ μ E L
  letI:IsProbabilityMeasure μ:=probability R N per m S exterior Wc
  let a:=OriginalMarkedLocalPurchase.fee V j S (V.clock.allowance j+M.bill)
  have earlier (u):|maskedSpringScore R N per j r Z σ C (ξ u)-maskedSpringScore R N per j r Z σ C exterior|≤a:=
    stock.2.2 S (ξ u) exterior (outside S exterior u)
  obtain ⟨ce,cl,ctl⟩:=spring_control R live.le r Z σ C μ ξ (measurable_patch S exterior) exterior borel a earlier
  refine ⟨ce,cl,?_⟩
  intro F B bounded
  obtain ⟨e,l,delta⟩:=ctl (fun u=>F (ξ u)) B (fun u=>bounded (ξ u))
  refine ⟨e,l,fun meas=>(delta (meas.comp (measurable_patch S exterior))).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (rate N per live.le S M.bill bill) ((norm_nonneg _).trans (bounded exterior))

end YM.Integration.OriginalMarkedRunAction
