import YM.Integration.WilsonReflectedPublicOpticalEstate
import YM.Integration.WilsonReflectedPublicOpticalColumns
/-! A signed fixed-K source replacement at its actual native reflected site.
The normalization is charged exactly once on the real dated source. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonReflectedPublicSignedCoefficient
open Function Filter Set Finset MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Trace.Physical Trace.Physical.GermGraph Push Push.Local Marker Motion PhysicalNext PhysicalNext.Repeat.Legato
open Trace.Physical.Germ
open Planned.GuardedAtom MergeProof MergeProof.Accent Extra.Multi RG05Readout RG05Readout.Address
open WilsonThermometerOffsetTrajectory WilsonThermometerOffsetCylinder WilsonThermometerOffsetResidue
open WilsonThermometerOwnOffsetField WilsonThermometerMarchSource WilsonThermometerReflectedTrajectory
open scoped Topology BigOperators Classical
open WilsonReflectedFundedHearing WilsonReflectedOpticalArm
variable {G:Gauge}(R:Run G){N p f K d:ℕ}
local notation "C₀" => R.family
local notation "F" => R.family.labels.level d
local notation "P₁" => R.family.path.rep N p f

theorem original (A:Arm R d N p f K) (begin:f≤K) (live:K≤N) (ref:(C₀).ref d≤f)
    {E:ℝ} (bill:Priced R A E) (c:ℂ) :
    let g:=(C₀).S.a f
    let op:Motion:=(A.s,A.b)
    let γ:ℂ:=-c/((g:ℂ)^d)
    ∃ q:Coefficient (F) ((C₀).side f p),
      (∃π:(P₁).activities.Moves op.1 A.o,q=stretch γ (audition (z:=op) π A.z)) ∧
      q.Format A.o (C₀).params (P₁) ∧
      q.remBound A.o (P₁) (safety (C₀) f) (‖γ‖*(turnCost (P₁).p.order (P₁).p.power*E)) ∧
      (F).coeffSize q.x ≤ ‖γ‖*(orbitCost (F)*E) ∧
      ∀U, q.density A.o ((C₀).localSection d) (P₁) U =
        c*((P₁).eval U:ℂ)*(WilsonReflectedOriginalTwoDeposit.held R (source R A (begin.trans live)) f U -
          WilsonReflectedRestartedPair.mean R N (cropped R A begin) f U) := by
  intro g op γ
  let π:=Classical.choice ((R.makes.wilson.represents N p f (begin.trans live)).good.labels.moves op.1 A.o)
  let Q:=audition (z:=op) π A.z
  let Z:=invoice A.z 0 ((C₀).localSection d) (P₁)
  have hn:2≤((C₀).side f p).val := (by decide : 2≤4).trans (Next.Foundations.actual_side_ge (C₀).S f p)
  have turned:=WilsonReflectedPublicOrientedCoefficient.posted op A.o π A.z hn (R.makes.sections d)
    A.filed.form bill.2.1 (View.spin_at op π (P:=Z))
  have src:Q.density A.o ((C₀).localSection d) (P₁)=fun U=>WilsonReflectedFiledArm.evaluated R (N:=N) d A.z A.b A.s A.o U:=turned.2.2.2.2.2.2
  have cost:(F).coeffSize Q.x≤orbitCost (F)*E :=by
    rw [show Q.x=Motion.patch (F) op A.z.x from turned.2.1]
    exact (patch_cost (F) op A.z.x).trans
      (mul_le_mul_of_nonneg_left bill.2.2.1 (zero_le_one.trans (orbitCost_one_le (F))))
  refine ⟨stretch γ Q,⟨π,rfl⟩,stretch_format γ turned.1,stretch_rem γ turned.2.2.2.1,?_,?_⟩
  · change (F).coeffSize (γ • Q.x) ≤ _
    rw [Size.smul]
    exact mul_le_mul_of_nonneg_left cost (norm_nonneg _)
  · intro U
    calc
      _ = γ*WilsonReflectedFiledArm.evaluated R (N:=N) d A.z A.b A.s A.o U :=
        (stretch_density _ _ _ _ _ _).trans (congrArg (γ*·) (congrFun src U))
      _ = c*((P₁).eval U:ℂ)*signed R A U :=by
        have mesh:((g:ℂ)^d)≠0:=pow_ne_zero _ (by exact_mod_cast ((C₀).S.a_pos f).ne')
        have pay:((P₁).eval U:ℂ)≠0:=by exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson (begin.trans live) U).ne'
        change γ*_ = c*((P₁).eval U:ℂ)*(-_/(((g:ℂ)^d)*((P₁).eval U:ℂ)))
        dsimp only [γ]
        field_simp [mesh,pay]
      _ = _ := congrArg (c*((P₁).eval U:ℂ)*·) (WilsonReflectedFundedHearing.swap R A begin live ref U).symm

end YM.Integration.WilsonReflectedPublicSignedCoefficient
end
