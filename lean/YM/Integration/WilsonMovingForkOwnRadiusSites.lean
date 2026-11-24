import YM.Integration.WilsonMovingForkScreenedSites
import YM.Integration.WilsonMovingForkSocketWalk
import YM.Integration.WilsonMovingForkElectedCaptureWidth
import YM.Integration.WilsonOriginalHeterogeneousStopSites

/-! Common numerical capture of all actual samples with their own exterior radius. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 540000
noncomputable section
namespace YM.Integration.WilsonMovingForkOwnRadiusSites
open Finset Lattice Wilson RG Extraction Function Filter
open Contacts.Mat Contacts.Sensor WilsonSeparatedPhysicalRay WilsonSeparatedBranchStencil WilsonSeparatedGridTree WilsonSeparatedGridDesign
open PhysicalNext.Repeat.Legato
open WilsonMovingForkSeededPoint (seats)
open WilsonMovingForkPrintedFile (parent)
open WilsonOriginalPublicNodalChildSites (here)
open WilsonPositionProgramTrialFixedDigits (parents)
open scoped Classical BigOperators Topology
variable {G:Gauge}(R:Run G){n:ℕ}

def size (L r t:ℝ):ℝ:=(16*(1+L*(t/r)))*r
def capture (S:Schedule)(L r t:ℝ):ℕ:=WilsonCloseCaptureDate.level S (size L r t)

theorem expanded (L:ℝ){r:ℝ}(rp:0<r)(t:ℝ):size L r t=16*(r+L*t):=by
  unfold size
  field_simp

theorem issued {L r t:ℝ}(lp:0≤L)(rp:0<r)(tp:0≤t)(fit:size L r t≤R.family.S.a 0)
    {f:ℕ}(fine:R.family.S.a f≤r):
    let c:=capture R.family.S L r t
    c≤f ∧ 8*R.family.S.a f<R.family.S.a c ∧
      R.family.S.a (c+1)<size L r t ∧ size L r t≤R.family.S.a c:=by
  let c:=capture R.family.S L r t
  have positive:0<size L r t:=by rw [expanded L rp];positivity
  have edge:=WilsonCloseCaptureDate.bracket R.family.S positive fit
  change R.family.S.a (c+1)<size L r t ∧ size L r t≤R.family.S.a c at edge
  have gap:8*R.family.S.a f<R.family.S.a c:=by
    have :=edge.2
    rw [expanded L rp] at this
    linarith only [this,fine,rp,mul_nonneg lp tp]
  have advance:c≤f:=by
    by_contra! early
    have older:=R.family.S.strictAnti.antitone early.le
    linarith only [older,gap,R.family.S.a_pos f]
  exact ⟨advance,gap,edge⟩

theorem housed {L r t:ℝ}(lp:0≤L)(rp:0<r)(tp:0≤t)(fit:size L r t≤R.family.S.a 0)
    {f K:ℕ}(fine:R.family.S.a f≤r)(fk:f≤K)(o:Fin n → Cover)
    (held:∀i,‖R.family.S.gridPoint f (o i)‖≤L*t){u:ℕ}(uc:u≤capture R.family.S L r t):
    let uk:=uc.trans ((issued R lp rp tp fit fine).1.trans fk)
    let z:=WilsonPositionProgramTrialHomeCenters.plant R.family.S fk o (fun _=>0)
    (∀per:ℕ,∀i,parent R uk per (seats (R:=R) fk per o) i=0) ∧
      here R.family.path.levels K z u=0:=by
  intro uk z
  let c:=capture R.family.S L r t
  obtain ⟨_,_,_,wall⟩:=issued R lp rp tp fit fine
  rw [expanded L rp] at wall
  have newer:R.family.S.a c≤R.family.S.a u:=R.family.S.strictAnti.antitone uc
  have old (per:ℕ)(i:Fin n):parent R uk per (seats (R:=R) fk per o) i=0:=by
    apply WilsonOriginalHeterogeneousStopSites.embedded R.family.S fk uk (o i)
    linarith only [newer,wall,held i,rp,mul_nonneg lp tp]
  refine ⟨old,?_⟩
  rw [WilsonMovingForkSocketPhysicalDigits.ancestor _ K z u uk]
  obtain ⟨per,hp⟩:=(WilsonMovingForkPhysicalCover.unwrapped R.family.S u (parents R.family.S uk z)).exists
  have eq:=WilsonMovingForkPhysicalCover.ancestor R uk per z
  rw [show (fun i=>wrap (R.family.side K per) (z i))=seats (R:=R) fk per o from
    WilsonMovingForkPhysicalCover.aligned R fk per o] at eq
  funext i
  calc
    parents R.family.S uk z i=lift (wrap (R.family.side u per) (parents R.family.S uk z i)):=(hp i).symm
    _=lift (parent R uk per (seats (R:=R) fk per o) i):=congrArg lift (congrFun eq i).symm
    _=0:=by rw [old];funext;simp [lift]

def Recorded (f c:ℕ)(o:Fin n→ Cover):Prop:=
  ∀K (fk:f≤K) u, u≤c → ∀uk:u≤K,
    (∀per:ℕ,∀i,parent R uk per (seats (R:=R) fk per o) i=0) ∧
    here R.family.path.levels K (WilsonPositionProgramTrialHomeCenters.plant R.family.S fk o (fun _=>0)) u=0

theorem recorded {L r t:ℝ}(lp:0≤L)(rp:0<r)(tp:0≤t)(fit:size L r t≤R.family.S.a 0)
    {f:ℕ}(fine:R.family.S.a f≤r)(o:Fin n→ Cover)
    (held:∀i,‖R.family.S.gridPoint f (o i)‖≤L*t):
    Recorded R f (capture R.family.S L r t) o:=by
  intro K fk u uc uk
  exact housed R lp rp tp fit fine fk o held uc

theorem tariff (simple:G.Simple)(slow:WilsonWindowReportingPace.Slow R.kit){d B f:ℕ}{L r t:ℝ}
    (lp:0≤L)(rp:0<r)(tp:0≤t)(fit:size L r t≤R.family.S.a 0)(fine:R.family.S.a f≤r)
    (fixed:48*(1+L)≤R.family.path.levels.clock.hatBeta f)
    (pace:t/r≤(R.family.path.levels.clock.hatBeta f)^(2*B))
    (scale:r≤(R.family.path.levels.clock.hatBeta f)^d*R.family.S.a f):
    R.family.S.a (capture R.family.S L r t)/R.family.S.a f≤(R.family.path.levels.clock.hatBeta f)^(d+2*B+2):=by
  obtain ⟨cf,_,opened,_⟩:=issued R lp rp tp fit fine
  exact WilsonMovingForkElectedCaptureWidth.original R simple slow rp lp (div_nonneg tp rp.le) cf opened fixed pace scale

end YM.Integration.WilsonMovingForkOwnRadiusSites
end
