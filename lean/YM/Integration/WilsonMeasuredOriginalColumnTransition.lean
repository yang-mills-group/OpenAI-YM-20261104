import YM.Integration.WilsonTrueProjectedDualHistory
import YM.Integration.ActualNormalizedPush

/-! Restore the engineering factor of the submitted upper block on the original Wilson transition. -/
noncomputable section
namespace YM.Integration.WilsonMeasuredOriginalColumnTransition
open Labels Lattice Wilson RG Source MeasureTheory Trace.Physical Extra.Histories
open PhysicalNext Repeat Legato Graces Roost Org

variable {G:Gauge} (R:Run G) {d N per i:ℕ}
local notation "hi" => R.family.side (i+1) per
local notation "lo" => R.family.side i per

def upper (fine:Rep G hi) (film:Config G hi→ℂ) : Config G hi→ℂ :=
  (((R.family.path.S.block i).val:ℂ)^d)⁻¹ • (fun V=>(fine.eval V:ℂ)*film V)

private theorem rescale (op:StepData lo hi) (β:ℝ) (s:ℂ) (X:Config G hi→ℂ) :
    op.push β (s • X)=s • op.push β X:=by
  funext V; simp only [StepData.push,Pi.smul_apply,smul_comm _ s,integral_smul]

theorem original (live:i≤N) (fine:Rep G hi) (coarse:Rep G lo)
    (fineEq:fine.eval=(R.family.path.rep N per (i+1)).eval)
    (coarseEq:coarse.eval=(R.family.path.rep N per i).eval) (film:Config G hi→ℂ) :
    GermGraph.transition (C:=R.family) d N per i (upper R (d:=d) fine film) =
      (fun U=>(coarse.eval U:ℂ)*actualAverage R.family (N:=N) film U):=by
  let L:ℂ:=(R.family.path.S.block i).val
  have L₀:L≠0:=by dsimp [L];exact_mod_cast (R.family.path.S.block i).pos.ne'
  funext U
  have w₀:(((R.family.path.rep N per i).eval U:ℝ):ℂ)≠0:=by
    exact_mod_cast (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
  rw [actualAverage_push R.family,coarseEq]
  change L^d*((R.family.path.levels.clock.op i per).push (R.family.path.β N per (i+1))
    ((L^d)⁻¹ • (fun V=>(fine.eval V:ℂ)*film V)) U)=_
  rw [rescale R,fineEq]
  simp only [Pi.smul_apply,smul_eq_mul,Complex.real_smul,Complex.ofReal_inv]
  field_simp

end YM.Integration.WilsonMeasuredOriginalColumnTransition
end
