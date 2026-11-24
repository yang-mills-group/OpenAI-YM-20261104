import YM.Integration.WilsonThermometerUnitFilingFlatCourse
import YM.Integration.WilsonCenteredFiledAtoms

/-! One original upper submission and the issued signed debits give integrability on the whole conditional interval. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxRecDepth 4096
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonThermometerUnitFilingFlatOffer
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonThermometerUnitFilingFlatTelescope WilsonThermometerUnitFilingFlatCourse WilsonCenteredFiledAtoms
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k b v:ℕ}
local notation "C" => R.family
variable (rows:∀j:ℕ,Config G (R.family.side j per)→ℂ)

theorem stored {d:ℕ} (top:b≤N) {root:Site (R.family.side b per)} {κ M:ℝ}
    (offered:Store ((C).path.rep N per b) ((C).localSection d) (C).params root κ M
      (numerator R N per b (rows b))):
    Integrable (numerator R N per b (rows b)) (prior G _):=by
  obtain ⟨E,fmt,rem,sourceEq⟩:=offered
  have complete:=(E.envelope ((C).localSection d) (R.makes.wilson.represents N per b top).good rem fmt).integrableC (prior G (R.family.side b per))
  exact complete.congr (Eventually.of_forall sourceEq)

variable (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
  (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
variable (grades:ℕ→ℕ) (places:∀j,Site (R.family.side j per)) (bills:ℕ→ℝ)

include π Γ course in
theorem original (floor:m≤v) (live:b≤N)
    (entered:∀j∈Ico v b,Entered R N Ψ rows j (grades j) (places j) (bills j))
    (paid:Integrable (numerator R N per b (rows b)) (prior G _)):
    ∀j,v≤j → j≤b → Integrable (numerator R N per j (rows j)) (prior G _):=by
  have descend:∀n:ℕ,∀j,v≤j → j≤b → b≤j+n →
      Integrable (numerator R N per j (rows j)) (prior G _):=by
    intro n
    induction n with
    | zero=>
      intro j _ jb width
      have eq:j=b:=by omega
      subst j
      exact paid
    | succ n next=>
      intro j vj jb width
      by_cases same:j=b
      · subst j;exact paid
      have younger:=next (j+1) (by omega) (by omega) (by omega)
      have y:Integrable (fun U=>(((C).path.rep N per (j+1)).eval U) • rows (j+1) U) (prior G _):=by
        rw [show (fun U=>(((C).path.rep N per (j+1)).eval U) • rows (j+1) U)=
             numerator R N per (j+1) (rows (j+1)) by funext U;simp only [numerator,Complex.real_smul]]
        exact younger
      have top:j+1≤N:=by omega
      have heat:=actualTransport_weighted_integrable_of_integrable (C) R.makes top y (Nat.le_succ j)
      rw [actualTransport_step (C) R.makes top _ (Nat.lt_succ_self j),actualTransport_base (C) R.makes top] at heat
      obtain ⟨E,M,fmt,rem,heard,-⟩:=entered j (mem_Ico.mpr ⟨vj,lt_of_le_of_ne jb same⟩)
      have total:=(WilsonMeasuredOwnerIntegrable.pair R π Γ Ψ course (floor.trans vj) (jb.trans live)
        ((C).localSection (grades j)) (C).params (places j) E fmt rem).2
      have quiet:(Ψ j).eval=((C).path.rep N per j).eval:=
        (QuadraticLocal.Advent.later R π Γ Ψ course (floor.trans vj) (jb.trans live)).view
      refine (heat.sub total).congr (Eventually.of_forall fun U=>?_ )
      have nz:((Ψ j).eval U:ℂ)≠0:=by
        rw [congrFun quiet U]
        exact Complex.ofReal_ne_zero.mpr (Multi.AxisShift.chosen_positive R.makes.wilson (jb.trans live) U).ne'
      have reading:=congrArg (fun z:ℂ=>((Ψ j).eval U:ℂ)*z) (heard U)
      change ((Ψ j).eval U:ℂ)*(((Ψ j).eval U:ℂ)⁻¹*_) = ((Ψ j).eval U:ℂ)*(_-_) at reading
      rw [←mul_assoc,mul_inv_cancel₀ nz,one_mul,congrFun quiet U] at reading
      simp only [Pi.sub_apply,Complex.real_smul,numerator]
      rw [reading];ring
  exact fun j vj jb=>descend b j vj jb (by omega)

end YM.Integration.WilsonThermometerUnitFilingFlatOffer
