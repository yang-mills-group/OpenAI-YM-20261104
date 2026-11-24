import YM.Integration.WilsonOriginalPublicTrialPhaseRowRun
import YM.Integration.WilsonOriginalPublicTrialPhaseSpine
import YM.Integration.WilsonOriginalPublicTrialPhaseCopiedRide

/-! The actual reflected and translated copies pay their engineering factor on the original one-name Ride. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCopiedCourse
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
open WilsonOriginalPublicTrialPhaseSpine WilsonOriginalPublicTrialPhaseCoFiled
open WilsonOriginalPublicTrialPhaseRowRun
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G){j b K N per:ℕ}
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" i:arg => (A).rep N per i
local notation "O" i:arg => (A).levels.clock.op i per
local notation "V" => Site ((C).side j per)

def moves {i:ℕ}(ji : j ≤ i)(live:i ≤ N)(v:(V)):
    let t:=tilesAt (C).S per ji
    (P i).activities.Moves (motion t v).1 (t.translateBy v):=
  (R.makes.wilson.represents N per i live).good.labels.moves _ _ |>.some

def root {i:ℕ}(o:I→Site ((C).side i per))(v:(V)×I):Site ((C).side i per):=
  if ji : j ≤ i then (tilesAt (C).S per ji).copyMap v.1 (o v.2) else 0

def ink {i:ℕ}(K:ℕ)(d:I→ℕ)(X:I→Three G ((C).side i per))(v:(V)×I):Three G ((C).side i per):=
  if h : j ≤ i ∧ i ≤ N then
    let t:=tilesAt (C).S per h.1
    share (C).S (d v.2) K i • copies (P i) 0 (motion t) t.translateBy (moves R h.1 h.2) X v
  else 0

omit [DecidableEq I] [Fintype I] in
theorem parent {i:ℕ}(ji : j ≤ i)(o:I→Site ((C).side (i+1) per))(v:(V)×I):
    (O i).ratio.parent (root R o v)=root R ((O i).ratio.parent ∘ o) v:=by
  simp only [root,dif_pos ji,dif_pos (ji.trans i.le_succ),Function.comp_apply]
  exact WilsonOriginalPublicTrialPhaseTileSites.parent R ji v.1 (o v.2)

omit [DecidableEq I] [Fintype I] in
set_option maxHeartbeats 1600000 in
theorem edge {i:ℕ}(stock:RG05Readout.Many.Storage (C) R.doors)(ji : j ≤ i)(cut:i < K)(live:K ≤ N)
    (o:I→Site ((C).side (i+1) per))(d:I→ℕ)(l:I→ℝ)(nn:∀k,0≤l k)
    (X:I→Three G ((C).side (i+1) per))(Y:I→Three G ((C).side i per))
    (step:∀k,Ride (O i) (o k) ((O i).ratio.parent (o k)) (R.doors N per i (cut.trans_le live))
      ((((C).S.block i).val:ℂ)^(d k)) (X k) (Y k) (l k))(v:(V)×I):
    Ride (O i) (root R o v) ((O i).ratio.parent (root R o v)) (R.doors N per i (cut.trans_le live))
      1 (ink R (N:=N) K d X v) (ink R (N:=N) K d Y v) (l v.2):=by
  let fine:=ji.trans i.le_succ
  have top:i+1 ≤ N:=by omega
  have prev:i ≤ N:=by omega
  have got:=WilsonOriginalPublicTrialPhaseCopiedRide.original R stock (cut.trans_le live) ji o d l X Y step
    (moves R fine top) (moves R ji prev) v
  simp only [root,dif_pos fine,ink,dif_pos (And.intro fine top),dif_pos (And.intro ji prev)]
  have paid:=got.matchPay (share (C).S (d v.2) K (i+1)) (share (C).S (d v.2) K i) 1 (by
    rw [one_mul];exact share_step (C).S (d v.2) K i)
  exact paid.cost (mul_le_of_le_one_left (nn v.2) (max_le (paid_share _ _ _ cut) (paid_share _ _ _ cut.le)))

set_option maxHeartbeats 2400000 in
theorem original (stock:RG05Readout.Many.Storage (C) R.doors)(cater:Cater (C) R.doors)
    (jb:j ≤ b)(positive:1≤b)(before:b < K)(live:K ≤ N)(d:I→ℕ)(o:∀i:ℕ,I→Site ((C).side i per))
    (prior:∀i,(b ≤ i) → (i < K) → (O i).ratio.parent ∘ o (i+1)=o i)
    (X:∀i:ℕ,I→Three G ((C).side i per))(v:∀i,(C).label (d i))(w:I→ℝ)(pos:∀i,0<w i)
    (l:ℕ→I→ℝ)(nn:∀i k,0≤l i k)
    (slots:∀i,(b ≤ i) → (i < K) → Fintype.card I*Fintype.card Signed≤apron (A).levels i)
    (step:∀i,(b ≤ i) → ∀hi:i < K,∀k,Ride (O i) (o (i+1) k) ((O i).ratio.parent (o (i+1) k))
      (R.doors N per i (hi.trans_le live)) ((((C).S.block i).val:ℂ)^(d k)) (X (i+1) k) (X i k) (l i k))
    (born:MenuBoard (P K) (ink R (N:=N) (j:=j) K d (X K))
      (WilsonOriginalPublicTrialPhaseGroupedWord.origin R (N:=N) (jb.trans before.le) d (o K) v)
      (root R (j:=j) (o K)) (fun u=>w u.2) ((P K).p.supportExponent-3) 1):
    ∀i,(b ≤ i) → ∀hi:i < K,
      let γ:=width (Bandage.renal (A).levels) (fun u:(V)×I=>w u.2) (fun k u=>l k u.2) K i hi.le
      (∀u,0<γ u) ∧ ∃t,Furls (A).levels i t ∧
        Alcove (P i) (ink R (N:=N) K d (X i))
          (gust (A) N per K (WilsonOriginalPublicTrialPhaseGroupedWord.origin R (N:=N) (jb.trans before.le) d (o K) v) i hi.le)
          (root R (o i)) γ t (Bandage.renal (A).levels i) (1/2):=by
  have covered(i:ℕ)(bi:b ≤ i)(ik:i < K):(O i).ratio.parent ∘ root R (j:=j) (o (i+1))=root R (o i):=by
    funext p
    rw [Function.comp_apply,parent R (jb.trans bi),prior i bi ik]
  have rooms(i:ℕ)(bi:b ≤ i)(ik:i < K):Occupancy (root R (j:=j) (o (i+1))) (apron (A).levels i) ∧
      Occupancy (root R (j:=j) (o i)) (apron (A).levels i):=by
    have jm:=jb.trans bi
    have hi:=WilsonOriginalPublicTrialPhaseTileSites.original R (p:=per) jm (o (i+1))
    have eq:root R (j:=j) (o (i+1))=fun v:((V)×I)=>(tilesAt (C).S per (jm.trans i.le_succ)).copyMap v.1 (o (i+1) v.2):=by
      funext p;simp only [root,dif_pos (jm.trans i.le_succ)]
    refine ⟨fun x=>(eq ▸ hi.1 x).trans (slots i bi ik),?_⟩
    rw [←covered i bi ik,eq]
    exact fun x=>(hi.2 x).trans (slots i bi ik)
  exact WilsonOriginalPublicTrialPhaseRowRun.original R stock cater positive live _
    (fun i=>ink R (N:=N) (j:=j) K d (X i)) (fun i=>root R (j:=j) (o i)) (fun p=>w p.2)
    (fun p=>pos p.2) (fun i p=>l i p.2) born covered rooms
    (fun i bi hi p=>edge R stock (jb.trans bi) hi live (o (i+1)) d (l i) (nn i) (X (i+1)) (X i) (step i bi hi) p)

end YM.Integration.WilsonOriginalPublicTrialPhaseCopiedCourse
end
