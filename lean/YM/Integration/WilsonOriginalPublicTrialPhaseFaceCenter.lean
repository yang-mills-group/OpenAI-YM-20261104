import YM.Integration.WilsonOriginalPublicTrialPhaseReplicaCenters

/-! Each captured singleton invoice has the genuine older reading of its entire K-born tile word. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseFaceCenter
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Cells WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Classical BigOperators ContDiff
open WilsonOriginalPublicTrialPhaseTiles
variable {G:Gauge}
theorem slice {V:Type}[Fintype V][DecidableEq V]{B:Census V}(A:History G)(N per K:ℕ){u:ℕ}
    (F:Config G (A.S.side K per)→Poly B)(hF:Integrable F (prior G _))(uk:u≤K)(w:B.Mode):
    (fun U=>(gust A N per K F u uk U).part w)=gust A N per K (fun U=>(F U).part w) u uk:=by
  induction uk using Nat.decreasingInduction with
  | self=>rw [gust_base,gust_base]
  | of_succ i hi ih=>
    rw [gust_step A N per K F hi,gust_step A N per K _ hi,
      push_get (A.levels.transition_mass ..) (gust_live A N per K F hF hi) w,ih]

theorem splice {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E](A:History G)(N per K:ℕ){c u:ℕ}
    (F:Config G (A.S.side K per)→E)(ck:c≤K)(uc:u≤c):
    gust A N per c (gust A N per K F c ck) u uc=gust A N per K F u (uc.trans ck):=by
  induction uc using Nat.decreasingInduction with
  | self=>rw [gust_base]
  | of_succ i hi ih=>rw [gust_step A N per c _ hi,gust_step A N per K F (hi.trans_le ck),ih]

variable (R:Run G){j N per K c u:ℕ}
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" => (A).rep N per
local notation "V" => Unit × Site ((C).side j per)
local notation "B" => Stock.census V

def cohort (jk:j≤K)(M:Config G ((C).side K per)→ℂ) :Config G ((C).side K per)→Poly (B):=
  birth (B) ((P) K) (fun v=> (tilesAt (C).S per jk).copy v.2 M)

theorem grade (ju:j≤u)(uc:u≤c)(ck:c≤K)(live:K≤N)(M:Config G ((C).side K per)→ℂ)
    (earned:Integrable (cohort R (N:=N) ((ju.trans uc).trans ck) M) (prior G _))
    {X:V → Three G ((C).side c per)} {o:V → Site ((C).side c per)} {w:V→ℝ}{e t:ℝ}
    (deck:MenuBoard ((P) c) X (gust (A) N per K (cohort R (N:=N) ((ju.trans uc).trans ck) M) c ck) o w e t)
    (v:V):
    gust (A) N per c (X v).1 u uc=
      gust (A) N per K (fun U=>(((P) K).eval U:ℂ)*(tilesAt (C).S per ((ju.trans uc).trans ck)).copy v.2 M U) u (uc.trans ck):=by
  let Q:=cohort R (N:=N) ((ju.trans uc).trans ck) M
  have head:(X v).1=(fun U=>(gust (A) N per K Q c ck U).part ((B).fire v)):=
    funext fun U=>((deck.check (R.makes.wilson.represents N per c (ck.trans live)).good.labels U).2 v).symm
  have seed:(fun U=>(Q U).part ((B).fire v))=
      (fun U=>(((P) K).eval U:ℂ)*(tilesAt (C).S per ((ju.trans uc).trans ck)).copy v.2 M U):=
    funext fun U=>boot (B) ((P) K) _ U v
  rw [head,slice (A) N per K Q earned ck,seed,splice]

theorem original (ju:j≤u)(uc:u≤c)(ck:c≤K)(live:K≤N)(M:Config G ((C).side K per)→ℂ)
    (earned:Integrable (cohort R (N:=N) ((ju.trans uc).trans ck) M) (prior G _))
    (cost:Integrable (fun U=>(((P) K).eval U:ℂ)*M U) (prior G _))
    {X:V → Three G ((C).side c per)}{o:V → Site ((C).side c per)}{w:V→ℝ}{e t:ℝ}
    (deck:MenuBoard ((P) c) X (gust (A) N per K (cohort R (N:=N) ((ju.trans uc).trans ck) M) c ck) o w e t)(v:V):
    gust (A) N per c (X v).1 u uc 1/(((P) u).eval 1:ℂ)=
      Motion.scalar (motion (tilesAt (C).S per ju) v.2) (actualTransport (C) (N:=N) M (uc.trans ck) 1):=by
  rw [grade R ju uc ck live M earned deck v,
    WilsonOriginalPublicTrialPhaseReplicaCenters.flat R (uc.trans ck) ju live M v.2 cost]
  congr 1
  simp only [actualTransport,Complex.real_smul,Complex.ofReal_inv,div_eq_inv_mul]

end YM.Integration.WilsonOriginalPublicTrialPhaseFaceCenter
end
