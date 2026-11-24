import YM.Integration.WilsonSingleHardStops
import YM.Integration.WilsonMeasuredOwnerReserve

/-! The two flat Wilson filings hear the genuine native forced component on its
actual measured vacuum, with its original hard partners at every intervening age. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonMeasuredOwnerFlatReading
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) (simple:G.Simple) {N per m k b:ℕ} (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q)
   (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
   (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (top:b ≤ N) {u:ℕ} (floor:m ≤ u) (ub:u ≤ b) (p:ℕ) {ε:ℝ} (ep:0<ε) (small:ε ≤ 1)
   (enrolled:WilsonSingleHardRadius.start R simple p ep ≤ u)
   {d:ℕ} {F:Frame G d} (S:SectionData F) (A:Hol G) (y:Site (R.family.side b per))
   (q:Coefficient F (R.family.side b per)) (law:q.Format y A (Ψ b))
   {M B:ℝ} (income:q.remBound y (Ψ b) (LocalComparison.forcedDivisor R.family b) M)
   (bp:0<B) (budget:M ≤ B)
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "vac" => R.family.path.rep N per b
local notation "W" => Ψ b
local notation "J" => Stock.census (Fin 1)
local notation "profile" => (fun U=>((W).eval U)⁻¹ • account q W U)
local notation "reading" h:max => actualTransport R.family (N:=N) profile h 1

include way ticket course top floor ub ep small enrolled S A law income bp budget in
theorem original {i:ℕ} (ui:u ≤ i) (ib:i ≤ b) : ‖reading ib‖ ≤ 4*B*ε/β^p := by
  obtain ⟨room,_⟩:=WilsonSingleHardRadius.cash R simple p ep (enrolled.trans ub)
  have ak:0 ≤ κ:=Real.sqrt_nonneg _
  have sq : κ^2=R.family.path.levels.clock.forcedAllowance b:=Real.sq_sqrt (Real.exp_pos _).le
  have paid:R.family.path.levels.clock.forcedAllowance b ≤ κ/2:=by
    nlinarith only [sq,mul_nonpos_of_nonneg_of_nonpos ak (sub_nonpos.mpr room)]
  let w:=1/(2*B)
  have wp : 0<w:=by dsimp [w]; positivity
  have tested:w*M ≤ 1/2 := by
    calc
      _ ≤ w*B := mul_le_mul_of_nonneg_left budget wp.le
      _ = _ := by dsimp only [w]; field_simp
  let O:=Passport.point (fun _:Fin 1=>y)
  let model : Empty→Row O J G (Wallet WilsonMeasuredOwnerReserve.disk):=Empty.elim
  obtain ⟨Z,_,_,_,hard,draw⟩:=WilsonMeasuredOwnerReserve.original R π Γ Ψ course
    (floor.trans ub) top paid S A y q law M income w wp tested
  let t:Wallet WilsonMeasuredOwnerReserve.disk:= fun _=>⟨1,by simp [WilsonMeasuredOwnerReserve.disk]⟩
  letI : Nonempty (Wallet WilsonMeasuredOwnerReserve.disk):=⟨t⟩
  have test : WilsonMeasuredOwnerReserve.test t=1:=rfl
  let panel:=Tint.Patrol.picture model Z
  have lights (U:Config G (R.family.side b per)) :panel.E.log t U=0:=tsum_empty
  have blank (U:Config G (R.family.side b per)) :(WilsonSingleHardRadius.gallery Z.hard).E.log t U=0:=tsum_empty
  have whole (U:Config G (R.family.side b per)) : panel.density t U=(WilsonSingleHardRadius.gallery Z.hard).density t U := by
    rw [Gallery.density,Gallery.density,lights,blank]
    rfl
  obtain ⟨same,owners,_⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course (floor.trans ub) top
  have quiet:(W).eval=(vac).eval:=(course.1.walk b (floor.trans ub) top).view
  have measured:=(WilsonMeasuredOnlyHard.original q vac W same quiet owners S A y κ M law income).2.2.1
  have atom (U:Config G (R.family.side b per)):
      ((WilsonSingleHardRadius.gallery Z.hard).density t U).part ((J).fire 0)=account q W U := by
    rw [←whole]
    have h:(panel.density t U).part ((J).fire 0)=WilsonMeasuredOwnerReserve.test t*
        (q.density y S W U-(soft q).density y S vac U):=(draw t U).2
    rw [h,test,one_mul,measured,add_sub_cancel_left]
  have cost:=WilsonSingleHardRadius.stopped R simple way D Q ticket π Γ Ψ course O.origin Z.hard top
    floor ub p ep small enrolled wp hard ui ib t
  simp_rw [atom,←quiet] at cost
  calc
    _ ≤ 2*ε/(w*β^p) := cost
    _ = _ := by simp only [w,div_eq_mul_inv,mul_inv_rev,inv_inv]; ring

include way ticket course top floor ub ep small enrolled S A law income bp budget in
theorem variation {i j:ℕ} (ui:u ≤ i) (ib:i ≤ b) (uj:u ≤ j) (jb:j ≤ b) :
    ‖reading ib-reading jb‖ ≤ 8*B*ε/β^p := by
  have first:=original R simple way D Q ticket π Γ Ψ course top floor ub p ep small enrolled
    S A y q law income bp budget ui ib
  have second:=original R simple way D Q ticket π Γ Ψ course top floor ub p ep small enrolled
    S A y q law income bp budget uj jb
  calc
    _ ≤ ‖reading ib‖+‖reading jb‖ := norm_sub_le _ _
    _ ≤ 4*B*ε/β^p+4*B*ε/β^p := add_le_add first second
    _ = _ := by ring

end YM.Integration.WilsonMeasuredOwnerFlatReading
