import YM.Integration.WilsonMovingForkEnrolledPrint

/-! At a single actual board only the chosen printed material is charged.
The columns and the programme at other sites and dates are unrestricted. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 1400000
noncomputable section
namespace YM.Integration.WilsonMovingForkEnrolledDensity
open Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6 Multi Pert.Asymptotics WilsonOriginalMixedBlockRows
open WilsonMovingForkPrintedFile (parent Program)
open WilsonMovingForkChronologicalTable (density ordinary)
open WilsonMovingForkDepositedPrint (Sheet board)
open scoped Classical BigOperators
variable {G:Gauge}(R:Run G){m i N per k:ℕ}
  (hk:Burn.horizon k+2 ≤ R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ → Layout G)(Γ:ℕ → Pace.Coin)(Ψ:∀j,Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ → ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(base:m ≤ i)(cut:i<N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ base)(ahead:Mentor.Forecast D R.rolls Q φ books)
  {n K:ℕ}{d:Fin n → ℕ}(prog:Program R d K)(w:∀a,R.family.label (d a))
  (pins:Fin n → Site (R.family.side K per))(ik:i+1<K)
  {I:Type}[Fintype I](B:I→Binder (Passport.point (parent R ik.le per pins)) (Stock.census (Fin n)))
  (grades:Fin n → ℕ)(order shelf q:ℕ)(income:Fin n → ℝ)
  (M:WilsonOriginalCensusDatedMaterial.Material R N (i+1) q grades
    (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) B)(x:Wallet (room (Fin n)))

def sheet:Sheet R N (i+1) (parent R ik.le per pins) where
  index:=I
  load:=grades
  order:=q
  strip:=_
  binder:=B
  source:=M
  wallet:=x

include course cut in
theorem original (tol:ℝ)(paid:WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books base op lesson ahead
    (Passport.point (parent R ik.le per pins)) B grades order shelf q income M tol)
    (atDate:prog N per w pins (i+1) ik=board (sheet R D pins ik B grades q M x)):
    WilsonReceivedChronologicalMaterialEndpoint.submitted R D Ψ (Passport.point (parent R ik.le per pins))
      B grades q M x=density prog N per w pins (i+1):=by
  let port:=Passport.point (parent R ik.le per pins)
  obtain ⟨_,_,_,_,film⟩:=WilsonReceivedChronologicalMaterialEndpoint.original R hk D Q π Γ Ψ course books base
    cut op lesson ahead port B grades order shelf q income M tol paid x
  let rep:=R.family.path.rep N per (i+1)
  let T:=WilsonReceivedChronologicalMaterialEndpoint.submitted R D Ψ port B grades q M x
  have heat:=WilsonReceivedChronologicalMaterialEndpoint.heat R π Γ Ψ course base cut
  funext U s
  have nz:(rep.eval U:ℂ)≠0:=Complex.ofReal_ne_zero.mpr
    (AxisShift.chosen_positive R.makes.wilson (Nat.succ_le_of_lt cut) U).ne'
  have receipt:=congrArg (fun z:ℂ=>(rep.eval U:ℂ)*z) (film U s)
  change (rep.eval U:ℂ)*((rep.eval U:ℂ)⁻¹*(T U).part s)=_ at receipt
  rw [←mul_assoc,mul_inv_cancel₀ nz,one_mul] at receipt
  refine receipt.trans ?_
  change (rep.eval U:ℂ)*(WilsonOriginalTwoFlatIRMounted.value B grades
    (WilsonOriginalCensusDatedMaterial.words M) (Coat.gStep (Ψ (i+1)).beta) x U).part s=
    (rep.eval U:ℂ)*(ordinary prog N per w pins (i+1) U).part s
  rw [heat]
  unfold ordinary
  rw [dif_pos ik,atDate]
  rfl

end YM.Integration.WilsonMovingForkEnrolledDensity
