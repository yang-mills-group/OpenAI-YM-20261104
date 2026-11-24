import YM.Integration.WilsonOriginalFiledWeight
import YM.Integration.WilsonOriginalDatedCensusInput
import YM.Integration.WilsonFirstReceivedGalleryRegular
import YM.Integration.WilsonOriginalCensusAppointment
import YM.Integration.WilsonOriginalPhysicalFieldsAtBoard
import YM.Integration.WilsonOriginalMixedBlockRows

/-! Opening an authentic paid census book at its selected wallet on an original dated Wilson post. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalFiledWhole
open Function Finset Filter RG Lattice Wilson Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison Multi
open WilsonRootedKioskOccupiedSlip VowsR LocalComparison ConnectedActivityE6
open scoped Classical BigOperators

variable {G:Gauge}(R:Run G){m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(hi:m ≤ i)
  (ahead:Mentor.Forecast D R.rolls Q φ books)
  {V:Type}[Fintype V][DecidableEq V]
local notation "J" => Stock.census V
local notation "A" => WilsonOriginalMixedBlockRows.room V
local notation "K₀" => fun _:V => (⊥:Submodule ℝ ℂ)
local notation "χ" => R.family.path.levels.clock.hatBeta i


open MeasureTheory
open WilsonOriginalDatedCensusInput (Filed)

/-- The quiet part of the deposited gallery survives at the true flat connection. -/
theorem flat (cell:WilsonOriginalOccupiedWindow.Slice R (J) (Ψ i)):
    cell.A.density cell.x (1:Config G (R.family.side i per))≠0:=by
  let U:Config G (R.family.side i per):=1
  have clear:flags (Ψ i).p.threshold U=∅:=UVNext.CouplingReset.flags_one _
  have blank:=(cell.A.E.quiet_of_hasSum cell.x U (cell.earned.sums (Ψ i).p.exponent_pos.le cell.positive cell.x U))
  intro zero
  have equal:=congrArg (fun v:Poly (J)=>v.part (J).quiet) zero
  change (cell.A.density cell.x U).part (J).quiet=0 at equal
  rw [Gallery.density, WilsonFirstReceivedGalleryRegular.clear cell.A cell.x U clear,mul_one,
    Poly.part_smul,Poly.pass_part _ blank,mul_one] at equal
  exact (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) equal

/-- The identified successor's nonzero vacuum certifies integration of the entire submitted polynomial. -/
theorem original (S:V→ℝ)(a:ℕ)(submitted:Config G (R.family.side (i+1) per)→Poly (J))
    (pub:Filed (N:=N) R hk D Q π Γ Ψ books hi ahead S a submitted):Integrable submitted (prior G _):=by
  rw [←pub.atInput]
  apply WilsonOriginalFiledWeight.received (R.family.path.levels.clock.op i per)
    (R.family.path.levels.blocks i per).branches (R.family.path.β N per (i+1)) 1
  change (LocalComparison.actualPush R.family N per i (pub.law pub.x)) 1≠0
  rw [←pub.appointment.density pub.x]
  exact flat R Ψ (pub.appointment.row pub.x)

end YM.Integration.WilsonOriginalFiledWhole
end
