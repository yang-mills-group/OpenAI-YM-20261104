import YM.Integration.WilsonOriginalPublicTrialPhaseGroupedWord
import YM.Integration.WilsonOriginalPublicTrialPhaseCapturePost

/-! Acquisition of the rank-zero whole-tile row from the genuine, separately marked K fields. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseGroupedCapture
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
open WilsonOriginalPublicTrialPhaseCaptureFare WilsonOriginalPublicTrialPhaseRay
open WilsonOriginalPublicTrialPhaseGroupedWord
variable {G:Gauge}{I:Type}[Fintype I][DecidableEq I](R:Run G){j c K N per:ℕ}
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" => (A).rep N per (c+1)
local notation "Q" => (A).rep N per c
local notation "O" => (A).levels.clock.op c per
local notation "V" => Site ((C).side j per)
local notation "δ" => Bandage.renal (A).levels (c+1)

theorem current (jk:j≤K)(fine:c+1≤K)(live:K≤N)(d:I→ℕ)(z:I→Site ((C).side K per))
    (v:∀i,(C).label (d i)):
    Integrable (gust (A) N per K (origin R (N:=N) jk d z v) (c+1) fine) (prior G _):=by
  apply gust_live
  let t:=tilesAt (C).S per jk
  have hc(k:(V)×I):Continuous (t.copy k.1 (uncut R (d k.2) N per K (z k.2) (v k.2))):=by
    have f:Continuous (uncut R (d k.2) N per K (z k.2) (v k.2)):=by
      unfold uncut;exact continuous_const.add (((C).localSection _).continuous_places _ _)
    have h:=f.comp (continuous_pull (G:=G) (t.omega k.1) (t.translateBy k.1))
    unfold Tiling.copy;split <;> first | exact h.star | exact h
  exact (hatCont (C) K per _ hc (RG02.Actual.eval_cont R.makes.wilson live) _).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

set_option maxHeartbeats 2400000 in
theorem original (cater:Cater (C) R.doors)(stock:RG05Readout.Many.Storage (C) R.doors)
    (jk:j≤K)(fine:c+1≤K)(live:K≤N)(grade:3≤(A).levels.clock.J c)
    (d:I→ℕ)(z:I→Site ((C).side K per))(v:∀i,(C).label (d i))(a:I)(l:ℕ)
    (o:(V)×I→Site ((C).side (c+1) per))(w:(V)×I→ℝ)(pos:∀i,0<w i)
    (X:(V)×I→Three G ((C).side (c+1) per)){t:ℝ}(paid:Furls (A).levels (c+1) t)
    (file:Alcove (P) X (gust (A) N per K (origin R (N:=N) jk d z v) (c+1) fine) o w t δ (1/2))
    (seats:Occupancy (fun i:Unit×((V)×I)=>o i.2) (apron (A).levels (c+1)))
    (joined:Occupancy (fun i:Unit×(V)=>o (i.2,a)) (apron (A).levels (c+1)))
    (hull:∀i:(V)×I,coverNumber (P).p.B ({o (i.1,a),o i}:Support _)≤l)
    (fresh:Occupancy (fun i:Unit×(V)=>o (i.2,a)) (apron (A).levels c))
    (parents:Occupancy (fun i:Unit×(V)=>(O).ratio.parent (o (i.2,a))) (apron (A).levels c))
    (B:ℝ)(base:1≤B)(fee:∀i,1/WilsonOriginalPublicTrialPhaseGroup.wage a w (P).p.supportExponent δ l i≤B):
    let r:=reserve (bling (A).levels c) (Bandage.renal (A).levels c) B
    let homes:=fun i:Unit×(V)=>(O).ratio.parent (o (i.2,a))
    let M:=cohort R (N:=N) jk (WilsonOriginalPublicTrialPhaseTrace.word R (N:=N) d z v)
    0<r ∧ ∃T:Unit×(V)→ Coefficient ((C).labels.level 0) ((C).side c per),
      (∀i,(T i).Format (homes i) (C).params (Q)) ∧
      (∀i,(T i).remBound (homes i) (Q) (Push.Local.kappa (A) c) r) ∧
      MenuBoard (Q) (fun i=>invoice (T i) (homes i) ((C).localSection 0) (Q))
        (gust (A) N per K M c (by omega)) homes
        (fun _=>weight (C).S r c c) ((A).levels.budget c).supportExponent 1:=by
  intro r homes M
  have alive:c<N:=by omega
  obtain ⟨_,_,course,_⟩:=cater.tiers c N per alive
  let g:=WilsonOriginalPublicTrialPhaseGroup.wage a w (P).p.supportExponent δ l
  have gw(i:Unit×(V)):0<g i:=by
    have hδ:=paid.eye.2.1
    have count:0<(Fintype.card I:ℝ):=by exact_mod_cast Fintype.card_pos_iff.mpr ⟨a⟩
    apply Finset.prod_pos
    intro x _
    exact div_pos (mul_pos (div_pos hδ count) (pos x.2)) (Real.exp_pos _)
  obtain ⟨Y,menu,blade⟩:=WilsonOriginalPublicTrialPhaseGroup.original R (fine.trans live) a l o w X _ file
    (current R jk fine live d z v) course.publishes.contact paid pos seats joined hull
  rw [WilsonOriginalPublicTrialPhaseGroupedWord.original R jk fine live d z v a] at menu
  obtain ⟨rp,T,fmt,rem,board⟩:=WilsonOriginalPublicTrialPhaseCapturePost.original R cater stock alive grade
    (fun i:Unit×(V)=>o (i.2,a)) g gw Y _ menu blade fresh parents B base fee
  refine ⟨rp,T,fmt,rem,?_⟩
  rw [gust_step (A) N per K M fine]
  exact board

end YM.Integration.WilsonOriginalPublicTrialPhaseGroupedCapture
end
