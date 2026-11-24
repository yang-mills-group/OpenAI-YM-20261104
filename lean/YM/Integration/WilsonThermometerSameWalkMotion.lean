import YM.Integration.WilsonThermometerSameWalkArm
/-! The engineering normalization and the actual one-child stock follow the
same signed microscopic field through every date of the original Wilson tower. -/
set_option quotPrecheck false
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonThermometerSameWalkMotion
open RG.Shoot Pressure Testing Input Precision Org Push SectorMeasure PriceCompiler
open ConnectedActivityE6 Progress.DirectedRecipe AllOrder AllOrder.Transit WheelP AllOrder.Floe QuadraticLocal.Advent
open WilsonThermometerOffsetCylinder WilsonThermometerOwnOffsetField
open Function Filter MeasureTheory Lattice Wilson RG Source Labels RG12
open PhysicalNext Repeat Legato Graces Roost Org RG05Readout Native Address Many Records Harvest
open Push.GridApprox Push.Local MergeProof Accent Trace.Physical Trace.Physical.GermGraph
open Extra.Histories WilsonThermometerOffsetTrajectory WilsonThermometerSameWalkArm
open scoped Classical BigOperators
variable {G:Gauge} (R:Run G) {N per d i base:ℕ}
local notation "C₀" => R.family
local notation "F" => (C₀).labels.level d
local notation "S" => (C₀).localSection d

def field (z:Site ((C₀).side N per)) (live:i ≤ N) (v:(C₀).label d) :=
    dyes (C₀) i N per live (((C₀).S.a i:ℂ)^d • (C₀).O N per (((C₀).factory d N per).terminal v) z)

theorem enrolled (z:Site ((C₀).side N per)) (r:Emblems (C₀) d) (away:base ≤ i) (live:i ≤ N)
    (y:Palette (C₀) d) : enteredField R z r live (finer r away y)=
      field R z live (finer r (away.trans live) y (primaryLetter d)):=by
  have chosen:finer r live (finer r away y)=finer r (away.trans live) y:=by
    rw [Many.sumwalk r away live];rfl
  unfold enteredField field;rw [chosen];rfl

private theorem push_scale {c f:Side} (P:StepData c f) (β:ℝ) (D:Config G f→ℂ) (a:ℂ):
    P.push β (a•D)=a•P.push β D:=by
  funext V
  simp only [StepData.push,Pi.smul_apply,smul_comm _ a,integral_smul]

theorem next (z:Site ((C₀).side N per)) (live:i<N) (v:(C₀).label d):
    transition (C:=(C₀)) d N per i (field R z live v)=field R z live.le v:=by
  unfold field
  rw [dye_pitch,dye_pitch]
  unfold transition Extra.Histories.blast
  rw [push_scale,smul_smul]
  have bill:(((C₀).S.block i).val:ℂ)^d*((C₀).S.a (i+1):ℂ)^d=((C₀).S.a i:ℂ)^d:=by
    have ne:(((C₀).S.block i).val:ℂ)≠0:=by exact_mod_cast ((C₀).S.block i).property.ne'
    rw [(C₀).S.a_step];push_cast;rw [←mul_pow]
    congr 1
    exact mul_div_cancel₀ _ ne
  rw [bill]
  unfold dyes
  rw [gust_step _ _ _ _ _ live]

theorem top {m k:ℕ} (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀ j,Rep G ((C₀).side j per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ) (started:m ≤ N)
    (z:Site ((C₀).side N per)) (v:(C₀).label d) (U:Config G ((C₀).side N per)):
    field R z (Nat.le_refl N) v U=((Ψ N).eval U:ℂ)*(S).places ((F).scaled (Ψ N).p.threshold⁻¹ v) z U:=by
  obtain ⟨pt,_,_⟩:=WilsonMeasuredCourseQuietSlots.selected R π Γ Ψ course started le_rfl
  change ((C₀).path.rep N per N).p=(Ψ N).p at pt
  have mask: (Ψ N).p.threshold=(C₀).path.levels.clock.threshold N:=by
    have eqp:((C₀).path.rep N per N).p=(C₀).path.levels.budget N:=(R.makes.wilson.represents N per N le_rfl).vac
    exact (congrArg BudgetPoint.threshold (pt.symm.trans eqp))
  have cash: (Ψ N).eval=((C₀).path.rep N per N).eval:=(QuadraticLocal.Advent.later R π Γ Ψ course started le_rfl).view
  unfold field dyes
  rw [gust_base,cash,mask]
  simp only [Family.O,TransferData.cylinder,LinearEquiv.symm_apply_apply,Pi.smul_apply,smul_eq_mul]
  have nz:((C₀).S.a N:ℂ)^d≠0:=pow_ne_zero d (Complex.ofReal_ne_zero.mpr ((C₀).S.a_pos N).ne')
  unfold initial
  simp only [Pi.smul_apply,smul_eq_mul]
  field_simp

end YM.Integration.WilsonThermometerSameWalkMotion
end
