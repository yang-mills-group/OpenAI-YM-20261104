import YM.Integration.WilsonReceivedChronologicalMaterialEndpoint
import YM.Integration.WilsonMovingForkDepositedPrint
import YM.Integration.WilsonThermometerUnitFilingFlatRead

/-! The deposited ordinary scalar and every conditional face belong to the
same paid original post. The actual issued heat enters at the receiving date. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.WilsonMovingForkPostedMaterial
open Function Finset Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor QuadraticLocal.Affinity Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open Push Push.PriceCompiler Push.AbsoluteSums Stationary Comparison.RG02 QuadraticLocal.Rebirth
open VowsR LocalComparison ConnectedActivityE6
open WilsonOriginalMixedBlockRows WilsonRegisteredPairUnaryWallet MintClock Multi WilsonOlderFreshGraphSlate
open Pert.Asymptotics WilsonThermometerUnitFilingCoarse
open WilsonOriginalCensusDatedMaterial (Material words)
open WilsonMovingForkDepositedPrint (Sheet board polynomial)
open WilsonReceivedChronologicalMaterialEndpoint (submitted word)
open scoped Classical BigOperators
variable {G:Gauge}{R:Run G}{N per i n:ℕ}{I:Type}[Fintype I]
variable {pins:Fin n→Site (R.family.side (i+1) per)}{grades:Fin n→ℕ}{q:ℕ}{σ:ℝ}
  {B:I→Earn.Binder (Passport.point pins) (Stock.census (Fin n))}

def file (M:Material R N (i+1) q grades σ B)(x:Wallet (room (Fin n))):Sheet R N (i+1) pins where
  index:=I
  load:=grades
  order:=q
  strip:=σ
  binder:=B
  source:=M
  wallet:=x

variable {m k:ℕ}(hk:Burn.horizon k+2≤R.alloy.B.a.clock.J m)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
  (π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {φ:ℕ→ℕ}(books:Mentor.Offices.Books D R.rolls Q φ)(hi:m ≤ i)(cut:i < N)
  (op:Mentor.Opportunity (R.alloy.B.a.clock.J (i+1)) (R.alloy.B.a.clock.J i))
  (lesson:Lesson (N:=N) R hk D Q π Γ hi)(ahead:Mentor.Forecast D R.rolls Q φ books)
variable (M:Material R N (i+1) q grades (Poetry.Agenda.seed D φ (Burn.horizon k) (R.alloy.B.a.clock.J (i+1))) B){order shelf:ℕ}{H₀:Fin n→ℝ}
  {tol:ℝ}(paid:WilsonOriginalCensusMaterialPosting.Posted R hk D Q π Γ Ψ books hi op lesson ahead
    (Passport.point pins) B grades order shelf q H₀ M tol)(x:Wallet (room (Fin n)))

include paid course cut in
theorem original :
    let H:=file M x
    let b:=board H
    let g:=regulatorRun R.family N per (i+1)
    let w:=submitted R D Ψ (Passport.point pins) B grades q M x
    let bank:=WilsonOriginalTwoFlatIRMounted.value b.binder b.load b.copies g b.wallet
    (∀U,w U=(((R.family.path.rep N per (i+1)).eval U:ℝ):ℂ) • bank U) ∧
    ∀s:(Stock.census (Fin n)).Mode,
      reading R (N:=N) (fun U=>(w U).part s) (i+1) le_rfl=(polynomial H g).part s:=by
  intro H b g w bank
  obtain ⟨_,_,_,_,heard⟩:=WilsonReceivedChronologicalMaterialEndpoint.original R hk D Q π Γ Ψ course books hi cut
    op lesson ahead (Passport.point pins) B grades order shelf q H₀ M tol paid x
  have heat:Coat.gStep (Ψ (i+1)).beta=g:=by
    rw [(course.1.walk (i+1) (Nat.le_succ_of_le hi) cut).beta];rfl
  have group(U):w U=(((R.family.path.rep N per (i+1)).eval U:ℝ):ℂ) • bank U:=by
    funext s
    let mass:ℂ:=(R.family.path.rep N per (i+1)).eval U
    have positive:mass≠0:=Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson cut U).ne'
    have row:mass⁻¹*(w U).part s=(bank U).part s:=by
      rw [heard U s]
      dsimp only [WilsonReceivedChronologicalMaterialEndpoint.word]
      rw [heat]
      rfl
    change (w U).part s=mass*(bank U).part s
    rw [←row,←mul_assoc,mul_inv_cancel₀ positive,one_mul]
  refine ⟨group,?_⟩
  intro s
  have atFlat:=WilsonThermometerUnitFilingFlatRead.original R cut (R.family.path.rep N per (i+1)) rfl
    (fun U=>(bank U).part s)
  simp_rw [group,Poly.part_smul]
  exact atFlat.trans (congrArg (fun V:Poly (Stock.census (Fin n))=>V.part s) (WilsonMovingForkDepositedPrint.flat H g))

end YM.Integration.WilsonMovingForkPostedMaterial
end
