import YM.Integration.WilsonOriginalPublicTrialPhaseScalar
import YM.Integration.WilsonOriginalPublicTrialPhaseGroup

/-! Centering each whole copy on the same finite original menu leaves all joint activities in place. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCenterMenu
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Planned.GuardedAtom Guard Push Local Next.Foundations
open MergeProof MergeProof.Accent MergeProof.Menu MergeProof.Float GridApprox.Nil Extra.Trajectories
open PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Marker Ac
open RG05Readout RG05Readout.Address RG05Readout.Many OPE.Therm
open WilsonOriginalPublicTrialPhaseScalar
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]{B:Census V}

def shift {n:Side} (z:V→ℂ)(F:Config G n→Poly B):Config G n→Poly B:=
  fun U=>Poly.pass (Mach B z)*F U

theorem live {n:Side}(z:V→ℂ){F:Config G n→Poly B}(hF:Integrable F (prior G n)):
    Integrable (shift z F) (prior G n):=by
  let s:=Poly.pass (Mach B z)
  let L:Poly B→ₗ[ℂ]Poly B:={
    toFun:=(s*·)
    map_add':=fun x y=>mul_add ..
    map_smul':=fun x y=>mul_smul_comm .. }
  exact ((L.restrictScalars ℝ).toContinuousLinearMap).integrable_comp hF

theorem branches {n:Side}(Q:Rep G n)(X:V→Three G n)(z:V→ℂ)(U:Config G n):
    Mach B (fun i=>(deposit Q (X i) (z i)).2.1 U)=Mach B z+Mach B (fun i=>(X i).2.1 U):=by
  unfold Mach
  rw [←sum_add_distrib]
  refine sum_congr rfl fun i _=>?_
  rw [←Extra.Trajectories.send_add]
  exact congrArg (Poly.send (B.fire i)) (add_comm ..)

set_option maxHeartbeats 700000 in
theorem original (R:Run G){N per k:ℕ}(hk:k≤N){X:V→Three G (R.family.side k per)}
    {F:Config G (R.family.side k per)→Poly B}{o:V→Site (R.family.side k per)}{w:V→ℝ}{d a:ℝ}
    (M:MenuBoard (R.family.path.rep N per k) X F o w d a)(z:V→ℂ):
    MenuBoard (R.family.path.rep N per k)
      (fun i=>deposit (R.family.path.rep N per k) (X i) (z i)) (shift z F) o w d a:=by
  let Q:=R.family.path.rep N per k
  obtain ⟨H,K,cart,reg,forced,bank⟩:= M.grants
  refine ⟨live z M.cleared,fun i=>useful (R.makes.wilson.represents N per k hk).good (M.fettled i) (z i),
    H,K,cart,reg,forced,?_⟩
  funext U
  change Poly.pass (Mach B z)*(F U)=_
  rw [bank]
  unfold restore
  rw [branches,add_assoc]
  have quiet:(Mach B (fun i=>(X i).2.1 U)+∑ t,H t U).part B.quiet=0:=by
    change (Mach B (fun i=>(X i).2.1 U)).part B.quiet+(∑t,H t U).part B.quiet=0
    rw [mute,zero_add,Poly.part_sum]
    exact sum_eq_zero fun i _=>(cart.exp i).1.sil U
  rw [pass_add (mute B z) quiet,mul_smul_comm,mul_assoc]
  rfl

end YM.Integration.WilsonOriginalPublicTrialPhaseCenterMenu
end
