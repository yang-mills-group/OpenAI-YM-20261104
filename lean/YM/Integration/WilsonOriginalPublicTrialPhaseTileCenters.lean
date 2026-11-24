import YM.Integration.WilsonOriginalPublicTrialPhaseFaceCenter

/-! All captured flat centers are the copies of the same physical conditional mean. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseTileCenters
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Cells WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Classical BigOperators ContDiff
open WilsonOriginalPublicTrialPhaseTiles
open WilsonOriginalPublicTrialPhaseFaceCenter WilsonOriginalPublicTrialPhaseCenterMenu
variable {G:Gauge}(R:Run G){j u c K per N:ℕ}
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" => (A).rep N per
local notation "V" => Unit × Site ((C).side j per)

theorem original (ju:j≤u)(uc:u≤c)(ck:c≤K)(live:K≤N)(M:Config G ((C).side K per)→ℂ)
    (earned:Integrable (cohort R (N:=N) ((ju.trans uc).trans ck) M) (prior G _))
    (cost:Integrable (fun U=>(((P) K).eval U:ℂ)*M U) (prior G _))
    {X:V → Three G ((C).side c per)}{o:V → Site ((C).side c per)}{w:V→ℝ}{e t:ℝ}
    (deck:MenuBoard ((P) c) X (gust (A) N per K (cohort R (N:=N) ((ju.trans uc).trans ck) M) c ck) o w e t):
    let a:=actualTransport (C) (N:=N) M (uc.trans ck) 1
    let av:=fun v:V=>gust (A) N per c (X v).1 u uc 1/(((P) u).eval 1:ℂ)
    gust (A) N per c (shift (fun v=>-av v) (gust (A) N per K (cohort R (N:=N) ((ju.trans uc).trans ck) M) c ck)) u uc=
      gust (A) N per K (cohort R (N:=N) ((ju.trans uc).trans ck) (fun U=>M U-a)) u (uc.trans ck):=by
  intro a av
  let ta:=tilesAt (C).S per ((ju.trans uc).trans ck)
  have ref(v:V):av v=Motion.scalar (motion (tilesAt (C).S per ju) v.2) a:=
    WilsonOriginalPublicTrialPhaseFaceCenter.original R ju uc ck live M earned cost deck v
  have each(v:V)(U): -av v+ta.copy v.2 M U=ta.copy v.2 (fun W=>M W-a) U:=by
    rw [ref,WilsonOriginalPublicTrialPhaseCenteredBirth.tiled]
    congr 2
    simp [motion,Motion.scalar,ta,Tiling.hand]
    rfl
  let F:=cohort R (N:=N) ((ju.trans uc).trans ck) M
  have plant:shift (fun v=>-av v) F=cohort R (N:=N) ((ju.trans uc).trans ck) (fun W=>M W-a):=by
    unfold F cohort
    rw [WilsonOriginalPublicTrialPhaseCenteredBirth.planted]
    exact congrArg (birth (Stock.census V) ((P) K)) (funext fun v=>funext fun U=>each v U)
  rw [←WilsonOriginalPublicTrialPhaseCenteredBirth.original (A) N per K (F:=F) earned ck,plant,splice]

end YM.Integration.WilsonOriginalPublicTrialPhaseTileCenters
end
