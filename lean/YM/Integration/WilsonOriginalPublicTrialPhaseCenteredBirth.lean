import YM.Integration.WilsonOriginalPublicTrialPhaseFlock

/-! Centering a complete original K word commutes with its marked Haar evolution on every field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCenteredBirth
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Cells WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Classical BigOperators ContDiff
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]{B:Census V}

theorem planted {n:Side}(Q:Rep G n)(M:V → Config G n→ℂ)(z:V→ℂ):
    WilsonOriginalPublicTrialPhaseCenterMenu.shift z (birth B Q M)=birth B Q (fun v U=>z v+M v U):=by
  funext U
  unfold WilsonOriginalPublicTrialPhaseCenterMenu.shift birth
  rw [mul_smul_comm,←pass_add (mute B z) (mute B (fun v=>M v U))]
  congr 2
  unfold Mach
  rw [←sum_add_distrib]
  exact sum_congr rfl fun i _=>(send_add ..).symm

theorem original (A:History G)(N per K:ℕ){u:ℕ}
    {F:Config G (A.S.side K per)→Poly B}(hF:Integrable F (prior G _))(uk:u≤K)(z:V→ℂ):
    gust A N per K (WilsonOriginalPublicTrialPhaseCenterMenu.shift z F) u uk=WilsonOriginalPublicTrialPhaseCenterMenu.shift z (gust A N per K F u uk):=by
  induction uk using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ i hi ih=>
    rw [gust_step A N per K _ hi,gust_step A N per K F hi,ih]
    funext U
    exact convective _ _ _ (A.levels.transition_mass ..) (gust_live A N per K F hF hi) U

theorem hearing (R:Run G){N per K u:ℕ}(uk:u≤K)(M:V → Config G (R.family.side K per)→ℂ)
    (lot:Integrable (birth B (R.family.path.rep N per K) M) (prior G _))(z:V→ℂ):
    gust R.family.path N per K (birth B (R.family.path.rep N per K) (fun v U=>z v+M v U)) u uk=
      WilsonOriginalPublicTrialPhaseCenterMenu.shift z (gust R.family.path N per K (birth B (R.family.path.rep N per K) M) u uk):=by
  rw [←planted];exact original _ _ _ _ lot uk z

theorem tiled {n:Side}(T:Tiling n)(M:Config G n→ℂ)(a:ℂ)(v:T.Cell)(U:Config G n):
    T.copy v (fun W=>M W-a) U= -(if T.hand v then star a else a)+T.copy v M U:=by
  unfold Tiling.copy
  split <;> simp_all <;> ring

end YM.Integration.WilsonOriginalPublicTrialPhaseCenteredBirth
end
