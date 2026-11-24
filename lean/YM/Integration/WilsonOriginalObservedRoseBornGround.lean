import YM.Integration.WilsonOriginalObservedRoseBornSlope
import YM.Integration.WilsonOriginalObservedRoseKineticGround

/-! One independent ground mesh pays the protected free sector and the actual Carnation slope on the original kinetic clock. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalObservedRoseBornGround
open Filter Set Function Metric Lattice Wilson RG Source Extraction Table Spec Climb Trace.Pilot PhysMS
open OPE PhysicalNext PhysicalNext.Repeat FVA2.Register Pert.Asymptotics PowerSeries
open PhysicalNext.Repeat.Legato Maxwell XSpace XSpace.Cirrus XSpace.Normalize XSpace.Rose
open WilsonMaxwellThermometerCommonTangent (Equivariant)
open WilsonMaxwellThermometerFiniteTangent (credit cost roster)
open WilsonMaxwellThermometerOriginal (lower)
open scoped Topology Classical
variable {G:Gauge}(R:Run G)(simple:G.Simple){B:ℕ}(hB:0<B)(pace:WilsonWindowReportingPace.Slow R.kit)
    (Z:WilsonPrescription G){fine index:ℝ→ℕ}
    (schedule:WilsonOriginalPositionFineScheme.enrolled (R:=R) (hG:=simple) (B:=B) Z fine index)
    {I:Type}[Fintype I](basis:Module.Basis I ℂ (Sec G 6))
local notation "g"=>regulatorRun R.family
local notation "unit"=>WilsonMaxwellThermometerKineticLog.unit G

include hB pace schedule in
theorem original (cap:ℝ→ℝ)(offered:ℝ→Set Mesh)(opened:∀r,offered r∈Front):
    ∃m:ℝ→Mesh,(∀r,m r∈offered r) ∧
    (∀η:ℝ,0<η→∀ᶠr in trail,∀N per,fine r≤N→|g N per (fine r)/unit r-1|<η) ∧
    ∀ᶠr in trail,‖coeff 1 (Detector Z.scheme Z.criterion (m r))-((c_T Z.criterion:ℝ):ℂ)‖≤r ∧
    ∀N per, fine r≤N→∀(u:Sec G 6)(P Q:Module.End ℂ (Sec G 4)),
      Equivariant P→Equivariant Q→cost basis (roster u (P (lower G)) (Q (lower G)))≤cap r→
      ‖credit Z.scheme Z.criterion (m r) u (P (lower G)) (Q (lower G))/(g N per (fine r):ℂ)‖≤2*r:=by
  let δ (r:ℝ):=if 0<r then r else 1
  let fronts (r:ℝ):=offered r ∩ {m|‖coeff 1 (Detector Z.scheme Z.criterion m)-((c_T Z.criterion:ℝ):ℂ)‖≤δ r}
  have eligible (r:ℝ):fronts r∈Front:=by
    have positive:0<δ r:=by dsimp only [δ];split <;> positivity
    have limit:=Metric.tendsto_nhds.mp (WilsonOriginalObservedRoseBornSlope.calibrated Z simple) (δ r) positive
    exact inter_mem (opened r) (limit.mono (fun m hm=>by simpa only [dist_eq_norm] using hm.le))
  obtain ⟨m,openings,sold⟩:=WilsonOriginalObservedRoseKineticGround.original R simple hB pace Z schedule
    basis cap fronts eligible
  refine ⟨m,fun r=>(openings r).1,fun η hη=>WilsonMaxwellThermometerKineticUpper.original R simple hB
    pace Z schedule hη,?_⟩
  have positive:∀ᶠr:ℝ in trail,0<r:=self_mem_nhdsWithin
  filter_upwards [positive,sold] with r live paid
  exact ⟨by simpa only [Set.mem_setOf_eq,δ,if_pos live] using (openings r).2,paid⟩

end YM.Integration.WilsonOriginalObservedRoseBornGround
