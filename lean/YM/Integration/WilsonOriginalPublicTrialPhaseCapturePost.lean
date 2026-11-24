import YM.Integration.WilsonOriginalPublicTrialPhaseCaptureFare

/-! The authentic whole-tile capture supplies the rank-zero roster and its native menu. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseCapturePost
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open WilsonOriginalPublicTrialPhaseAccumulated WilsonOriginalPublicTrialPhaseRace
open WilsonOriginalPublicTrialPhaseRay WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Topology ContDiff BigOperators Classical
open MergeProof.Float WilsonOriginalPublicTrialPhaseCaptureFare
variable {G:Gauge}{V:Type}[Fintype V][DecidableEq V]
local notation "Z" => Stock.census V

theorem cheaper {n:Side}{Q:Rep G n}{X:V→Three G n}{o:V→Site n}{w w':V→ℝ}{e e':ℝ}
    {M:Config G n→Poly Z}(h:MenuBoard Q X M o w e 1)(pos:∀v,0<w v)(small:∀v,0<w' v)
    (shrink:∀v,w' v≤w v)(width:e'≤e):MenuBoard Q X M o w' e' 1:=by
  refine ⟨h.cleared,h.fettled,?_⟩
  have peg:Repegs o Q.p.B w w' 0 1 Z:=slighter pos small (fun i=>by simpa only [one_mul] using shrink i) zero_le_one le_rfl
  exact h.grants.prune pos small peg zero_le_one (by simpa only [add_zero] using width) (by norm_num)

variable (R:Run G){c N per:ℕ}
local notation "C" => R.family
local notation "A" => (C).path
local notation "O" => (A).levels.clock.op c per
local notation "P" => (A).rep N per (c+1)
local notation "Q" => (A).rep N per c
local notation "F" => (C).labels.level 0
local notation "loc" => (C).localSection 0

set_option maxHeartbeats 1800000 in
theorem original (cater:Cater (C) R.doors)(stock:RG05Readout.Many.Storage (C) R.doors)
    (live:c<N)(grade:3≤(A).levels.clock.J c)
    (o:V→Site ((C).side (c+1) per))(w:V→ℝ)(pos:∀i,0<w i)
    (X:V→Three G ((C).side (c+1) per))(M:Config G ((C).side (c+1) per)→Poly Z)
    (book:MenuBoard (P) X M o w ((P).p.supportExponent-2) 1)
    (blade:∀i,Blade (P) (o i) (X i).2.1 (profile (P).activities (X i).2.2) 0 (4*(1/w i)))
    (seats:Occupancy o (apron (A).levels c))(parents:Occupancy ((O).ratio.parent ∘ o) (apron (A).levels c))
    (B:ℝ)(base:1≤B)(fee:∀i,1/w i≤B):
    let r:=reserve (bling (A).levels c) (Bandage.renal (A).levels c) B
    let homes:=(O).ratio.parent ∘ o
    0<r ∧ ∃ T:V→ Coefficient (F) ((C).side c per),
      (∀i,(T i).Format (homes i) (C).params (Q)) ∧
      (∀i,(T i).remBound (homes i) (Q) (Push.Local.kappa (A) c) r) ∧
      MenuBoard (Q) (fun i=>invoice (T i) (homes i) (loc) (Q)) ((O).push (P).beta M)
        homes (fun _=>weight (C).S r c c) ((A).levels.budget c).supportExponent 1:=by
  intro r homes
  let f:=bling (A).levels c
  let δ:=Bandage.renal (A).levels c
  let a(i:V):=4*(1/w i)
  let l(i:V):=(f+2)*a i
  have fp:0<f:=Real.exp_pos _
  have dp:0<δ:=by
    obtain ⟨a,b,paid⟩:=stock.exactMoon.days N per c live
    have estate:Coursework (A) _ _ _ a b:=⟨paid.2,paid.1⟩
    exact estate.poses.hats.1
  have rp:0<r:=by
    change 0<(1+8*(f+2)*B)/min 1 δ
    exact div_pos (by positivity) (lt_min zero_lt_one dp)
  have rates (i:V):=price fp.le dp base (pos i) (fee i)
  have cap(i:V):=WilsonOriginalPublicTrialPhaseCapture.original R cater live grade (o i) (X i) (a i)
    (mul_nonneg (by norm_num) (one_div_nonneg.mpr (pos i).le)) (book.fettled i) (blade i)
  choose T fmt small _bound rides using cap
  have started:=cheaper book pos pos (fun i=>le_rfl) (show (P).p.supportExponent-3≤(P).p.supportExponent-2 by linarith)
  obtain ⟨saf,land⟩:=WilsonOriginalPublicTrialPhaseLanding.original R stock live o w l (fun _=>1) X
    (fun i=>invoice (T i) (homes i) (loc) (Q)) M pos (fun _=>by simp) started rides seats parents
  simp only [inv_one,one_smul] at land
  have hpos:0<weight (C).S r c c:=weight_pos _ rp _ _
  have spend(i:V):weight (C).S r c c≤δ*WilsonOriginalPublicTrialPhaseLanding.first (w i) (l i):=by
    simpa only [WilsonOriginalPublicTrialPhaseRay.weight,WilsonOriginalPublicTrialPhaseRace.wage,div_self ((C).S.a_pos c).ne',Real.one_rpow,one_mul] using (rates i).2.2
  refine ⟨rp,T,fmt,fun i=>?_,cheaper land saf (fun _=>hpos) spend le_rfl⟩
  obtain ⟨a,b,ap,bp,ab,rest⟩:=small i
  exact ⟨a,b,ap,bp,ab.trans (rates i).2.1,rest⟩

end YM.Integration.WilsonOriginalPublicTrialPhaseCapturePost
end
