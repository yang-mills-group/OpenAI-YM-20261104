import YM.Integration.WilsonThermometerUnitFilingFieldRange
import YM.Integration.WilsonThermometerUnitFilingFlatTelescope

/-! Enroll the actual signed one-mark debits in the Wilson law conditioned at the older flat field. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatCourse
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonThermometerUnitFilingCoarse
open WilsonThermometerUnitFilingFlatTelescope
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b v:ℕ}
local notation "C" => R.family
local notation "X" j:max => Config G ((C).side j per)
variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
local notation "F" d:max => R.family.labels.level d
variable (rows:∀j:ℕ,Config G (R.family.side j per)→ℂ)

def Entered (N:ℕ) (bank:∀j,RG.Rep G (R.family.side j per)) (curve:∀j:ℕ,Config G (R.family.side j per)→ℂ)
    (j d:ℕ) (y:Site ((C).side j per)) (bill:ℝ):Prop:=
  ∃ (E:Coefficient (F d) ((C).side j per)) (M:ℝ),
    E.Format y (C).params (bank j) ∧ E.remBound y (bank j) (LocalComparison.forcedDivisor (C) j) M ∧
    (∀U,((bank j).eval U:ℂ)⁻¹*E.density y ((C).localSection d) (bank j) U=
      actualAverage (C) (N:=N) (curve (j+1)) U-curve j U) ∧
    M+(F d).coeffSize E.x ≤ bill

variable (simple:G.Simple) (way:WayStation R.kit)
  (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
  (ticket:TicketP R.alloy R.kit D Q)
  (top:b ≤ N) (floor:m ≤ v) (vb:v ≤ b)
  (gate:WilsonSingleHardRadius.start R simple 0 (zero_lt_one:0<(1:ℝ)) ≤ v)

include π Γ course floor top rows simple way D Q ticket gate in
theorem installment {j d:ℕ} (vj:v ≤ j) (jb:j ≤ b)
    {y:Site ((C).side j per)} {bill:ℝ} (paid:Entered R N Ψ rows j d y bill):
    ‖feeAt R N per v rows j‖ ≤
      (WilsonThermometerUnitFilingFieldRange.cost G d (Ψ j).p.threshold+5)*bill:=by
  obtain ⟨E,M,fmt,rem,read,price⟩:=paid
  have jN:=jb.trans top
  have quiet:(Ψ j).eval=((C).path.rep N per j).eval:=
    (QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans vj) jN).view
  have exactSource:E.density y ((C).localSection d) (Ψ j)=debit R N per rows j:=by
    funext U
    have nz:((Ψ j).eval U:ℂ)≠0:=by
      rw [show (Ψ j).eval U=((C).path.rep N per j).eval U by exact congrFun quiet U]
      exact Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson jN U).ne'
    calc E.density y ((C).localSection d) (Ψ j) U=
         ((Ψ j).eval U:ℂ)*(((Ψ j).eval U:ℂ)⁻¹*E.density y ((C).localSection d) (Ψ j) U):=by
          rw [←mul_assoc,mul_inv_cancel₀ nz,one_mul]
         _=_:=by rw [read U,congrFun quiet U];rfl
  have mp:0 ≤ M:=by obtain ⟨a,c,ap,cp,bound,-⟩:=rem;exact (add_nonneg ap cp).trans bound
  have raw:=WilsonThermometerUnitFilingFieldRange.original R d simple way D Q ticket π Γ Ψ course jN floor vj gate
    y E fmt rem mp
  let cost:=WilsonThermometerUnitFilingFieldRange.cost G d (Ψ j).p.threshold
  have sz:0 ≤ (F d).coeffSize E.x:=sum_nonneg fun _ _=>norm_nonneg _
  have wage:0 ≤ cost:=by
    change 0 ≤ 1+WilsonThermometerUnitFilingFieldRange.basisCost G d*(max 1 (Ψ j).p.threshold⁻¹)^d
    have quote:0 ≤ WilsonThermometerUnitFilingFieldRange.basisCost G d:=
      zero_le_one.trans (Next.Foundations.full_value_bound (G:=G) d).choose_spec.1
    positivity
  rw [feeAt,dif_pos vj,←exactSource]
  calc _ ≤ cost*(F d).coeffSize E.x+5*M:=raw.1 v le_rfl vj
       _ ≤ (cost+5)*(M+(F d).coeffSize E.x):=by nlinarith [mul_nonneg wage mp]
       _ ≤ (cost+5)*bill:=mul_le_mul_of_nonneg_left price (by positivity)

include π Γ course floor top vb simple way D Q ticket gate in
theorem original (grades:ℕ→ℕ) (places:∀j,Site ((C).side j per)) (bills:ℕ→ℝ)
    (offered:∀j,v ≤ j → j ≤ b → Integrable (numerator R N per j (rows j)) (prior G _))
    (issued:∀j∈Ico v b,Entered R N Ψ rows j (grades j) (places j) (bills j)):
    ‖reading R (N:=N) (numerator R N per b (rows b)) v vb-rows v 1‖ ≤
    ∑j ∈ Ico v b,(WilsonThermometerUnitFilingFieldRange.cost G (grades j) (Ψ j).p.threshold+5)*(bills j):=by
  rw [WilsonThermometerUnitFilingFlatTelescope.original R N per vb top rows offered]
  refine (norm_sum_le _ _).trans (sum_le_sum ?_)
  intro j hj
  exact installment R π Γ Ψ course rows simple way D Q ticket top floor gate
    (mem_Ico.mp hj).1 (mem_Ico.mp hj).2.le (issued j hj)

end YM.Integration.WilsonThermometerUnitFilingFlatCourse
