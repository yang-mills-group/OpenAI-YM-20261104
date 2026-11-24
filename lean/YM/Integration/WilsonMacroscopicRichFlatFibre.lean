import YM.Integration.WilsonMacroscopicRichCaptureRoots
import YM.Integration.WilsonMacroscopicRichLastKernelMoment
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true

noncomputable section
namespace YM.Integration.WilsonMacroscopicRichFlatFibre
open Filter Set Finset Function MeasureTheory Lattice Wilson RG Source Extraction Push.GridApprox OPE OPE.Therm Pressure
open WilsonMacroscopicForwardTransfer PhysicalNext.Repeat.Legato
open scoped Topology BigOperators
variable {G:Gauge}

/-- Actual Wilson lower kernel at V, integrated over every intermediate original field, on the same fine scale as the entire signed test. -/
def likelihood (R:Run G){u k:ℕ}(N per:ℕ)(uk:u+1≤k)(V:Config G (R.family.side u per)):=backTo R.family.path N per uk (last R u N per V)

theorem enrolled (R:Run G){u k:ℕ}(N per:ℕ)(uk:u+1≤k)(V:Config G (R.family.side u per)):Envelope (likelihood R N per uk V):=
  backTo_env R.family.path N per uk (held R u N per V)

private theorem one (R:Run G){u N:ℕ}(live:u+1≤N)(per:ℕ)(X:Config G (R.family.side (u+1) per)→ℂ)(V:Config G (R.family.side u per)):
    exterior (C:=R.family) (N:=N) (Nat.le_succ u) X V=(∫ W,X W*last R u N per V W ∂scene R.family.path N per (u+1))/(dose (H:=R.family.path) (p:=per) u V N:ℂ):=by
  let A:=weighted (C:=R.family) (N:=N) X
  let H:=R.family.path
  let S:=H.levels.clock.op u per
  let β:=H.β N per (u+1)
  have stage:pushTo H N per (Nat.le_succ u) A=S.push β A:=by
    simpa only [pushTo_self] using pushTo_next H N per (le_rfl:u≤u) A
  have receipt: (∫ W,X W*last R u N per V W ∂scene H N per (u+1))=∫ W,dose (H:=H) (p:=per) (u+1) W N • (X W*(S.density β W V:ℂ)) ∂prior G (R.family.side (u+1) per):=account (H:=H) (p:=per) R.makes.wilson live _
  apply congrArg (fun z:ℂ=>z/(dose (H:=H) (p:=per) u V N:ℂ))
  refine (congrFun stage V).trans (Eq.trans ?_ receipt.symm)
  change (∫ W, (S.density β W V) • ((dose (H:=H) (p:=per) (u+1) W N:ℂ)*X W) ∂prior G (R.family.side (u+1) per))=∫ W, dose (H:=H) (p:=per) (u+1) W N • (X W*(S.density β W V:ℂ)) ∂prior G (R.family.side (u+1) per)
  apply integral_congr_ae;filter_upwards [] with W;simp only [Complex.real_smul];ring

/-- Exact fixed-field posterior of the complete joint signed fine observable, for every V. -/
theorem measured (R:Run G){u k N per:ℕ}(uk:u+1≤k)(kN:k≤N)(X:Config G (R.family.side k per)→ℂ)(intg:Integrable X (scene R.family.path N per k))(V:Config G (R.family.side u per)):
    exterior (C:=R.family) (N:=N) ((Nat.le_succ u).trans uk) X V=(∫ W,X W*likelihood R N per uk V W ∂scene R.family.path N per k)/(dose (H:=R.family.path) (p:=per) u V N:ℂ):=by
  have both:=congrFun (WilsonMacroscopicRichCaptureRoots.through R (Nat.le_succ u) uk kN X) V
  have first:=one R (uk.trans kN) per (exterior (C:=R.family) (N:=N) uk X) V
  have rest:=WilsonMacroscopicForwardTransfer.joint R.makes uk kN X intg (last R u N per V) (held R u N per V)
  exact both.symm.trans (first.trans (congrArg (fun z:ℂ=>z/(dose (H:=R.family.path) (p:=per) u V N:ℂ)) rest))

end YM.Integration.WilsonMacroscopicRichFlatFibre

