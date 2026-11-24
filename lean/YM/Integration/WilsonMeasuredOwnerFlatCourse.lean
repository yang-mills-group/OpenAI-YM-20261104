import YM.Integration.WilsonSingleHardFixedStop
import YM.Integration.WilsonMeasuredOwnerFlatReading

/-! The same physical filing dates hear every perturbative order of a native
marked hard contribution. Its birth allowance retains its full original value. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerFlatCourse
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per)) (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (top:b ≤ N) {d:ℕ} {F:Frame G d} (S:SectionData F) (A:Hol G)
   (y:Site (R.family.side b per)) (q:Coefficient F (R.family.side b per))
   (law:q.Format y A (Ψ b)) {M:ℝ} (income:q.remBound y (Ψ b) (LocalComparison.forcedDivisor R.family b) M)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "vac" => R.family.path.rep N per b
local notation "W" => Ψ b
local notation "J" => Stock.census (Fin 1)
local notation "wallet" => Wallet WilsonMeasuredOwnerReserve.disk
local notation "profile" => (fun U=>((W).eval U)⁻¹ • account q W U)
local notation "reading" h:max => actualTransport R.family (N:=N) profile h 1

include course top S A law income in
/-- The named true hard program is the same for every field and scalar tester. -/
theorem mounted (begun:m ≤ b) (room:κ ≤ 1/2) {w:ℝ} (wp:0<w) (tested:w*M ≤ 1/2) :
    ∃ Z:Hard wallet (W).p (W).activities.forced (W).activities.K (Passport.point (fun _:Fin 1=>y)).origin J,
      Z.Paid (fun _=>w) (W).p.B (W).p.supportExponent κ ∧ ∀ t U,
        ((WilsonSingleHardRadius.gallery Z).density t U).part ((J).fire 0)=
          WilsonMeasuredOwnerReserve.test t*account q W U := by
  have ak:0 ≤ κ:=Real.sqrt_nonneg _
  have sq : κ^2=R.family.path.levels.clock.forcedAllowance b:=Real.sq_sqrt (Real.exp_pos _).le
  have paid:R.family.path.levels.clock.forcedAllowance b ≤ κ/2:=by
    nlinarith only [sq,mul_nonpos_of_nonneg_of_nonpos ak (sub_nonpos.mpr room)]
  let O:=Passport.point (fun _:Fin 1=>y)
  let model : Empty→Row O J G wallet:=Empty.elim
  obtain ⟨Z,_,_,_,hard,draw⟩:=WilsonMeasuredOwnerReserve.original R π Γ Ψ course begun top
    paid S A y q law M income w wp tested
  refine ⟨Z.hard,hard,?_⟩
  intro t U
  let panel:=Tint.Patrol.picture model Z
  have lights:panel.E.log t U=0:=tsum_empty
  have blank:(WilsonSingleHardRadius.gallery Z.hard).E.log t U=0:=tsum_empty
  have whole:panel.density t U=(WilsonSingleHardRadius.gallery Z.hard).density t U := by
    rw [Gallery.density,Gallery.density,lights,blank]
    rfl
  obtain ⟨same,owners,_⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course begun top
  have quiet:(W).eval=(vac).eval:=(course.1.walk b begun top).view
  have measured:=(WilsonMeasuredOnlyHard.original q vac W same quiet owners S A y κ M law income).2.2.1
  rw [←whole]
  have observed:(panel.density t U).part ((J).fire 0)=WilsonMeasuredOwnerReserve.test t*
      (q.density y S W U-(soft q).density y S vac U):=(draw t U).2
  rw [observed,measured,add_sub_cancel_left]

variable (simple:G.Simple) (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q) {u:ℕ} (floor:m ≤ u) (ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
   {B:ℝ} (bp:0<B) (budget:M ≤ B)

include way ticket course top floor ub fixed S A law income bp budget in
/-- The bound at both flat stops is fixed before a comparison order is chosen. -/
theorem original {i:ℕ} (ui:u ≤ i) (ib:i ≤ b) : ‖reading ib‖ ≤ 4*B*β*κ := by
  let w:=1/(2*B)
  have wp:0<w:=by dsimp [w]; positivity
  have tested:w*M ≤ 1/2 := by
    calc
      _ ≤ w*B := mul_le_mul_of_nonneg_left budget wp.le
      _ = _ := by dsimp only [w]; field_simp
  obtain ⟨Z,fare,observe⟩:=mounted R π Γ Ψ course top S A y q law income (floor.trans ub)
    (WilsonSingleHardRadius.half R simple (fixed.trans ub)) wp tested
  let t:wallet:=fun _=>⟨1,by simp [WilsonMeasuredOwnerReserve.disk]⟩
  letI : Nonempty wallet:=⟨t⟩
  have test:WilsonMeasuredOwnerReserve.test t=1:=rfl
  have cost:=WilsonSingleHardRadius.retained R simple way D Q ticket π Γ Ψ course
    (Passport.point (fun _:Fin 1=>y)).origin Z top floor ub fixed wp fare ui ib t
  have quiet:(W).eval=(vac).eval:=(course.1.walk b (floor.trans ub) top).view
  simp_rw [observe,test,one_mul,←quiet] at cost
  calc
    _ ≤ 2*β*κ/w := cost
    _ = _ := by simp only [w,div_eq_mul_inv,mul_inv_rev,inv_inv]; ring

include way ticket course top floor ub fixed S A law income bp budget in
theorem order {i:ℕ} (ui:u ≤ i) (ib:i ≤ b) (p:ℕ) {ε:ℝ} (ep:0<ε)
    (late:WilsonSingleHardRadius.start R simple p ep ≤ b) :
    ‖reading ib‖ ≤ 4*B*ε/β^p := by
  have h:=original R π Γ Ψ course top S A y q law income simple way D Q ticket floor ub fixed bp budget ui ib
  have cap:=(WilsonSingleHardRadius.cash R simple p ep late).2
  have positive:0<β:=(R.alloy.B.a.fits.delayed b).trans' (by norm_num : (0:ℝ)<1)
  calc
    _ ≤ 4*B*β*κ := h
    _ ≤ 4*B*β*(ε/β^(p+1)) := mul_le_mul_of_nonneg_left cap (by positivity)
    _ = _ := by rw [pow_succ]; field_simp

end YM.Integration.WilsonMeasuredOwnerFlatCourse
