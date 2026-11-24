import YM.Integration.WilsonOriginalPublicTrialPhaseCopiedCourse
import YM.Integration.WilsonOriginalPublicTrialPhasePaidBoard
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopySeedFare

/-! One posted original shoulder for the uncut fitted fields and every rolled copy. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseFittedSeats
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Cells WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Classical BigOperators ContDiff
open WilsonOriginalPublicTrialPhaseTiles
open WilsonPositionProgramBlockedTrialAddBack
open WilsonOriginalPublicTrialPhaseGroup WilsonOriginalPublicTrialPhaseFaceCenter
open WilsonOriginalPublicTrialPhaseCoFiled WilsonOriginalPublicTrialPhaseFiling WilsonOriginalPublicTrialPhaseRate
open WilsonOriginalPublicTrialPhaseCopiedCourse
open WilsonOriginalMicroscopicEntranceOpticalUnits (rank)
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G){j K N per:ℕ}
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" => (A).rep N per K
local notation "H" => (A).levels.clock.hatBeta K
local notation "V" => Site ((C).side j per)

def stock (d load K:ℕ)(α T:ℝ)(e:ℕ):ℝ:=
  WilsonMeasuredPublicEntranceTransferCopySeedFare.capital R d load α T*
    ((A).levels.clock.hatBeta K)^(16+(rank R d+e))

def fare (d:I→ℕ)(o:I→Site ((C).side K per))(v:∀i,(C).label (d i))(k:I):ℝ:=
  wage (P).p.B (Fintype.card I*Fintype.card Signed) (reserve R (N:=N) (d k) (o k) (v k))

set_option maxHeartbeats 1600000 in
theorem original {T₀:Campaign R}(book:Campaign.Pillars R T₀)(jk:j ≤ K)(live:K≤N)
    (d:I→ℕ)(o:I→Site ((C).side K per))(v:∀i,(C).label (d i))
    (small:∀k,((((C).localSection (d k)).footprint (o k)).card:ℝ)*(A).levels.clock.forcedAllowance K≤1)
    (opening:volume (P).p.B*(A).levels.clock.forcedAllowance K≤Real.log 2/2)(ex:0≤(P).p.supportExponent-3)
    (α:ℝ)(T:I→ℝ)(e:I→ℕ)(tp:∀i,0≤T i)(support:((A).levels.budget K).supportExponent≤α)
    (measured:∀i,((C).labels.level (d i)).coeffSize (v i)≤T i*H^(e i)):
    let B:=fun i=>stock R (d i) (Fintype.card I*Fintype.card Signed) K α (T i) (e i)
    let w:=fare R (N:=N) d o v
    (∀i,1≤B i ∧ 0<w i ∧ (w i)⁻¹≤B i) ∧
    ∃q:∀k:I,Coefficient ((C).labels.level (d k)) ((C).side K per),
      (∀k,(q k).x=v k ∧ (q k).Format (o k) (C).params (P) ∧
        (q k).remBound (o k) (P) (Push.Local.kappa (A) K) (B k) ∧
        ((C).labels.level (d k)).coeffSize (q k).x≤B k) ∧
      MenuBoard (P) (ink R (N:=N) (j:=j) K d (fun k=>invoice (q k) (o k) ((C).localSection (d k)) (P)))
        (WilsonOriginalPublicTrialPhaseGroupedWord.origin R (N:=N) jk d o v)
        (root R (j:=j) o) (fun u=>w u.2) ((P).p.supportExponent-3) 1:=by
  classical
  intro B w
  let t:=tilesAt (C).S per jk
  choose q x fmt writes rem ψ won hook using fun k=>WilsonOriginalPublicTrialPhaseBirth.original R book live
    (d k) (o k) (v k) (small k)
  have dom k:Dominated (q k).forced:=rem_dominated (rem k)
  obtain ⟨_,pos,upper⟩:=WilsonOriginalPublicTrialPhasePaidBoard.original R live t d o v q writes dom ψ won hook
    (moves R jk live) opening ex
  have credits k:=WilsonMeasuredPublicEntranceTransferCopySeedFare.original R live (d k)
    (Fintype.card I*Fintype.card Signed) (o k) (v k) (tp k) (e k) support (measured k)
  refine ⟨fun k=>⟨(credits k).1,pos k,(credits k).2.2.2⟩,q,fun k=>⟨x k,fmt k,rem_mono (rem k) (credits k).2.2.1,?_⟩,?_⟩
  · rw [x];exact (credits k).2.1
  let Y:=fun k=>invoice (q k) (o k) ((C).localSection (d k)) (P)
  have names:WilsonOriginalPublicTrialPhaseCopiedCourse.ink R (N:=N) (j:=j) K d Y=
      copies (P) 0 (motion t) t.translateBy (moves R jk live) Y:=by
    funext k
    simp only [WilsonOriginalPublicTrialPhaseCopiedCourse.ink,dif_pos (And.intro jk live),
      WilsonOriginalPublicTrialPhaseSpine.share_base,one_smul,t]
  have sites:root R (j:=j) o=fun k:(V)×I=>t.copyMap k.1 (o k.2):=by
    funext k;simp only [root,dif_pos jk,t]
  change MenuBoard (P) (WilsonOriginalPublicTrialPhaseCopiedCourse.ink R (N:=N) (j:=j) K d Y) _ _ _ _ _
  rw [names,sites]
  exact upper

end YM.Integration.WilsonOriginalPublicTrialPhaseFittedSeats
end
