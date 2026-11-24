import YM.Integration.WilsonOriginalPublicTrialPhaseGroupedCapture
import YM.Integration.WilsonOriginalPublicTrialPhasePlates

/-! A finite roster keeps its original density and the exact per-label widths throughout the pre-capture dates. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseRowRun
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
open WilsonOriginalPublicTrialPhaseRace WilsonOriginalPublicTrialPhaseLanding
variable {G:Gauge}{V:Type}

def width (renal:ℕ→ℝ)(w:V→ℝ)(l:ℕ→V→ℝ)(K i:ℕ)(hi:i≤K):V→ℝ:=
  back K w (fun m _ y v=>renal m*first (y v) (l m v)) i hi

theorem upper (renal:ℕ→ℝ)(w:V→ℝ)(l:ℕ→V→ℝ)(K:ℕ):
    width renal w l K K le_rfl=w:=back_head ..

theorem lower (renal:ℕ→ℝ)(w:V→ℝ)(l:ℕ→V→ℝ)(K i:ℕ)(hi:i<K):
    width renal w l K i hi.le=fun v=>renal i*first (width renal w l K (i+1) hi v) (l i v):=
  @back_step (fun _:ℕ=>V→ℝ) K w (fun m _ y v=>renal m*first (y v) (l m v)) i hi

variable [DecidableEq V][Fintype V](R:Run G){b K N per:ℕ}
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" i:arg => (A).rep N per i
local notation "O" i:arg => (A).levels.clock.op i per
local notation "Z" => Stock.census V
local notation "widths" => width (Bandage.renal (A).levels)

set_option maxHeartbeats 2200000 in
theorem original (stock:RG05Readout.Many.Storage (C) R.doors)(cater:Cater (C) R.doors)(start:1≤b)(live:K≤N)
    (M:Config G ((C).side K per)→Poly Z)(X:∀i:ℕ,V→Three G ((C).side i per))
    (o:∀i:ℕ,V→Site ((C).side i per))(w:V→ℝ)(pos:∀v,0<w v)(l:ℕ→V→ℝ)
    (top:MenuBoard (P K) (X K) M (o K) w ((P K).p.supportExponent-3) 1)
    (homes:∀i,(b ≤ i) → (i < K) → (O i).ratio.parent ∘ o (i+1)=o i)
    (room:∀i,(b ≤ i) → (i < K) → Occupancy (o (i+1)) (apron (A).levels i) ∧ Occupancy (o i) (apron (A).levels i))
    (reads:∀i,(b ≤ i) → ∀hi:i<K,∀v,Ride (O i) (o (i+1) v) ((O i).ratio.parent (o (i+1) v))
      (R.doors N per i (hi.trans_le live)) 1 (X (i+1) v) (X i v) (l i v)):
    ∀ m,(b ≤ m) → ∀fm:m<K, (∀v,0<widths w l K m fm.le v) ∧
      ∃t:ℝ,Furls (A).levels m t ∧
        Alcove (P m) (X m) (gust (A) N per K M m fm.le) (o m) (widths w l K m fm.le) t
          (Bandage.renal (A).levels m) (1/2):=by
  let F i (hi:i≤K):=gust (A) N per K M i hi
  have extend(i:ℕ)(hi:i≤K):∀ bi:b ≤ i,(∀v,0<widths w l K i hi v) ∧
      MenuBoard (P i) (X i) (F i hi) (o i) (widths w l K i hi) ((P i).p.supportExponent-3) 1:=by
    induction hi using Nat.decreasingInduction with
    | self=>
      intro _
      rw [upper,show F K le_rfl=M from gust_base ..]
      exact ⟨pos,top⟩
    | of_succ i hi ih=>
      intro bi
      obtain ⟨born,book⟩:=ih (by omega)
      have seats:=room i bi hi
      have got:=WilsonOriginalPublicTrialPhaseLanding.original R stock (hi.trans_le live)
        (o (i+1)) (widths w l K (i+1) hi) (l i) (fun _=>1) (X (i+1)) (X i) _ born (by simp) book
        (reads i bi hi) seats.1 (homes i bi hi ▸ seats.2)
      dsimp only at got
      simp only [inv_one,one_smul,homes i bi hi] at got
      have flow:(O i).push (P (i+1)).beta (F (i+1) hi)=F i hi.le:=(gust_step (A) N per K M hi).symm
      rw [flow,←lower _ w l K i hi] at got
      have current:∀v,0<widths w l K i hi.le v:=by rw [lower _ w l K i hi];exact got.1
      have here:(P i).p.supportExponent=((A).levels.budget i).supportExponent:=congrArg BudgetPoint.supportExponent (R.makes.wilson.represents N per i (hi.le.trans live)).vac
      exact ⟨current,WilsonOriginalPublicTrialPhaseCapturePost.cheaper got.2 current current (fun _=>le_rfl) (by rw [here];linarith)⟩
  intro m bm fm
  obtain ⟨born,book⟩:=extend (m+1) fm (by omega)
  have seats:=room m bm fm
  have got:=WilsonOriginalPublicTrialPhasePlates.original R cater (fm.trans_le live) (start.trans bm)
    (o (m+1)) (widths w l K (m+1) fm) (l m) (fun _=>1) (X (m+1)) (X m) _ born (by simp)
    _ (by linarith) book (reads m bm fm) seats.1 (homes m bm fm ▸ seats.2)
  dsimp only at got
  simp only [inv_one,one_smul,homes m bm fm] at got
  have flow:(O m).push (P (m+1)).beta (F (m+1) fm)=F m fm.le:=(gust_step (A) N per K M fm).symm
  rw [flow,←lower _ w l K m fm] at got
  exact ⟨by rw [lower _ w l K m fm];exact got.1,got.2.2.2⟩

end YM.Integration.WilsonOriginalPublicTrialPhaseRowRun
end
