import YM.Integration.WilsonPhysicalHistoryPositiveTower

/-! Exact compatibility of one step in the complete normalized physical
tower with the original held conditional Wilson experiment. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryPositiveConditional
open Function Filter MeasureTheory Lattice RG Wilson OPE OPE.Therm Push.GridApprox
open WilsonCoeffUV PhysicalNext.Repeat.Legato WilsonReportForwardTransfer
open scoped Classical
variable {G : Gauge}

private theorem scale {c f : Side} (S : StepData c f) (β : ℝ) (z : ℂ)
    (Y : Config G f → ℂ) (W : Config G c) :
    S.push β (fun U=>z*Y U) W = z*S.push β Y W := by
  unfold StepData.push
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun U=>by
    change S.density β U W • (z*Y U) = z*(S.density β U W • Y U)
    simp only [Complex.real_smul]
    ring

/-- The fixed top partition cancels at every real stage of this exact run,
including a run whose cutoff lies strictly above the physical first stop. -/
theorem original (R : Run G) {N per j : ℕ} (live : j<N)
    (X : Config G (R.family.side (j+1) per) → ℂ) (V : Config G (R.family.side j per)) :
    exterior (C:=R.family) (N:=N) j.le_succ X V =
      FVA1Physical.conditionalPush R.family.path N per j X V := by
  let A := R.family.path
  let S := A.levels.clock.op j per
  let P := A.rep N per (j+1)
  let Q := A.rep N per j
  let Z := partition G (A.S.side N per) (A.β N per N)
  have nz : (↑Z:ℂ)≠0 := by exact_mod_cast (partition_pos (G:=G) (n:=A.S.side N per) (A.β N per N)).ne'
  have qnz : (↑(Q.eval V):ℂ)≠0 := by exact_mod_cast (SectorNext.Vacuum.strictly A R.T.choice N per j live.le V).ne'
  have mass : S.push P.beta P.eval V = Q.eval V := (congrFun (R.makes.wilson.steps N per j live).1 V).symm
  have one (Y : Config G (A.S.side (j+1) per) → ℂ) : pushTo A N per j.le_succ Y = S.push P.beta Y :=
    (pushTo_next A N per (le_refl j) Y).trans (pushTo_self A N per _)
  have wt : weighted (C:=R.family) (N:=N) X = fun U=>(↑Z:ℂ)⁻¹*((P.eval U:ℂ)*X U) := by
    funext U
    change (↑(P.eval U / Z):ℂ)*X U = _
    rw [Complex.ofReal_div,div_eq_mul_inv]
    ring
  have coarse : (↑(dose (H:=A) (p:=per) j V N):ℂ) = (Q.eval V:ℂ)/(Z:ℂ) := Complex.ofReal_div ..
  rw [WilsonPhysicalHistoryPositiveIncome.receiver R live]
  change pushTo A N per j.le_succ (weighted (C:=R.family) (N:=N) X) V / (↑(dose (H:=A) (p:=per) j V N):ℂ) =
    S.push P.beta (fun U=>(P.eval U:ℂ)*X U) V / (↑(S.push P.beta P.eval V):ℂ)
  rw [wt,one,scale,coarse,mass]
  field_simp

end YM.Integration.WilsonPhysicalHistoryPositiveConditional

