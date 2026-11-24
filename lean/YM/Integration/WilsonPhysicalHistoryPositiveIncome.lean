import YM.Integration.FVA1Physical.ActualPush
import YM.Integration.FVA1Physical.DensityComparison
import YM.Integration.WilsonOffsetConditionalCharge
import YM.Integration.WilsonReportForwardTransfer
import YM.Integration.WilsonPhysicalHistoryJointResponse
import YM.RG12.Canonical.Charts

/-! Positive, normalized transfer of the complete signed tested fine field.
The true forwarded detector stays inside the original conditional integral. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryPositiveIncome
open Function Filter Finset MeasureTheory Lattice RG Wilson Source Extraction
open WilsonCoeffUV PhysicalNext.Repeat.Legato
open scoped Classical Topology BigOperators
variable {G : Gauge}

/-- On the original physical vacuum, pointwise conditional Jensen has gain one.
The right side is the actual posterior expectation, not a torus-volume norm. -/
theorem jensen (R : Run G) {N per i : ℕ} (live : i<N)
    (F : Config G (R.family.side (i+1) per) → ℂ) (V : Config G (R.family.side i per)) :
    ‖FVA1Physical.conditionalPush R.family.path N per i F V‖ ≤
      FVA1Physical.conditionalPush R.family.path N per i (fun U=>‖F U‖) V := by
  let A := R.family.path
  let S := A.levels.clock.op i per
  let β := A.β N per (i+1)
  let w := (A.rep N per (i+1)).eval
  let M := (A.rep N per i).eval V
  let μ := prior G (A.S.side (i+1) per)
  have kernel : S.IsKernel β G := A.levels.transition_mass i per β
  have Mpos : 0<M := SectorNext.Vacuum.strictly A R.T.choice N per i live.le V
  have wpos (U) : 0≤w U := A.nonnegative R.T.choice N per (i+1) live U
  change ‖M⁻¹ • (∫ U, S.density β U V • (w U • F U) ∂μ)‖ ≤
    M⁻¹*(∫ U, S.density β U V*(w U*‖F U‖) ∂μ)
  rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr Mpos.le)]
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr Mpos.le)
  apply (norm_integral_le_integral_norm _).trans_eq
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun U=>by
    change ‖S.density β U V • (w U • F U)‖ = S.density β U V*(w U*‖F U‖)
    rw [norm_smul,norm_smul,Real.norm_of_nonneg (kernel.positive U V),Real.norm_of_nonneg (wpos U)]

/-- The positive transfer is exactly the conditional operator in the original
two-offset charge. Its denominator is the measured next vacuum. -/
theorem receiver (R : Run G) {N per i : ℕ} (live : i<N)
    (F : Config G (R.family.side (i+1) per) → ℂ) (V : Config G (R.family.side i per)) :
    FVA1Physical.conditionalPush R.family.path N per i F V =
      WilsonOffsetConditionalCharge.conditional (R.family.path.levels.clock.op i per)
        (R.family.path.rep N per (i+1)) V F := by
  let S := R.family.path.levels.clock.op i per
  let P := R.family.path.rep N per (i+1)
  let Q := R.family.path.rep N per i
  have mass : S.push P.beta P.eval V = Q.eval V := (congrFun (R.makes.wilson.steps N per i live).1 V).symm
  change (Q.eval V)⁻¹ • (S.push P.beta (fun U=>P.eval U • F U) V) =
    S.push P.beta (fun U=>(P.eval U:ℂ)*F U) V / ((S.push P.beta P.eval V:ℝ):ℂ)
  rw [mass]
  simp only [Complex.real_smul,Complex.ofReal_inv,div_eq_mul_inv,mul_comm]

/-- The actual finite detector experiment at the fine end of the current
step, normalized from its original terminal physical roster at N. -/
def detector (R : Run G) {N per i q : ℕ} (live : i<N)
    (dims : Fin q→ℕ) (v : (j:Fin q)→R.family.label (dims j))
    (y : Fin q→Site (R.family.side N per)) :
    Config G (R.family.side (i+1) per)→ℂ :=
  WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) (p:=per) (k:=i+1) (i:=N) live
    (fun U=>∏ j, R.family.O N per (v j) (y j) U)

/-- Both physical child positions are fed to one signed tested expectation.
The first-crossing label is held in the actual RG12 chart at `stop`. -/
theorem tested (R : Run G) {N per i q d stop : ℕ} (live : i<N)
    (trained : R.family.ref d ≤ stop) (reached : stop ≤ N) (u : R.family.label d)
    (z : Site (R.family.side (i+1) per)) (dims : Fin q→ℕ)
    (v : (j:Fin q)→R.family.label (dims j)) (y : Fin q→Site (R.family.side N per))
    (W : Config G (R.family.side i per)) :
    let label := (RG12.chartOn R.family R.makes d stop (N,per) trained reached).symm u
    let F := detector R live dims v y
    let D := WilsonOffsetConditionalCharge.forward R.makes live z label
    ‖FVA1Physical.conditionalPush R.family.path N per i (fun U=>F U*D U) W‖ ≤
    FVA1Physical.conditionalPush R.family.path N per i (fun U=>‖F U‖*‖D U‖) W := by
  dsimp only
  let label := (RG12.chartOn R.family R.makes d stop (N,per) trained reached).symm u
  let F := detector R live dims v y
  let D := WilsonOffsetConditionalCharge.forward R.makes live z label
  simpa only [norm_mul] using jensen R live (fun U=>F U*D U) W

end YM.Integration.WilsonPhysicalHistoryPositiveIncome

