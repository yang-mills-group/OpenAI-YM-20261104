import YM.Integration.WilsonOriginalPublicTrialPhasePlates
import YM.Integration.WilsonOriginalPublicTrialPhasePad
import YM.RG05Readout.Capture.Fronds

/-! At capture each tile becomes one color for its whole ordinary product on the same original board. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseGroup
open Function Filter Finset MeasureTheory Lattice Wilson Labels RG Source Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu MergeProof.Float Marker
open Ac GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Ribbons Ribbons.Fibers Ribbons.ManyCopies Further.ShellBirth49.Fusing
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(R:Run G){N m per:ℕ}{V I:Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
local notation "C" => R.family
local notation "H" => (C).path
local notation "Q" => (H).rep N per m
local notation "A" => (H).levels
local notation "δ" => Bandage.renal (A) m
local notation "cap" => apron (A) m
local notation "Pad" => WilsonOriginalPublicTrialPhasePad.pad
local notation "padGas" => feed (fun _=>1) WilsonOriginalPublicTrialPhasePad.license

theorem select (i:I):Policy (finishGroup V i) (Stock.census (Unit×(V×I))) (Stock.census (Unit×V)):=
  fun _=>mem_powerset.mpr (subset_univ _)
def collect (i:I)(F:Poly (Stock.census (V×I))):Poly (Stock.census (Unit×V)):=
  pilot (finishGroup V i) (select i) (padGas F)
def contents (i:I)(s:(Stock.census (Unit×V)).Mode):(Stock.census (V×I)).Mode:=
  WilsonOriginalPublicTrialPhasePad.lift ⟨_,select i s⟩
theorem part (i:I)(s:(Stock.census (Unit×V)).Mode)(F:Poly (Stock.census (V×I))):
    (collect i F).part s=F.part (contents i s):=WilsonOriginalPublicTrialPhasePad.mode ..
theorem inside (i:I)(s:(Stock.census (Unit×V)).Mode)(j:V×I):j∈(contents i s).val ↔ ((),j.1)∈s.val:=by
  change j∈ (((partialGroup Unit (finishGroup V i)).plena (route (all_le _ _) s)).val.image Prod.snd) ↔ _
  rw [mem_image]
  constructor
  · rintro ⟨⟨⟨⟩,k⟩,hk,rfl⟩
    exact ((partialGroup Unit (finishGroup V i)).reaped _ _).mp hk
  intro h
  exact ⟨((),j),((partialGroup Unit (finishGroup V i)).reaped _ _).mpr h,rfl⟩

def wage (i:I)(w:V×I→ℝ)(z a:ℝ)(l:ℕ)(j:Unit×V):ℝ:=
  ∏ k∈((partialGroup Unit (finishGroup V i)).contents j),
    Fibers.Salt.tow (fun p:Unit×(V×I)=>w p.2) (z+1/2) (a/Fintype.card I) l k

private theorem larger {n:Side}{B:Rep G n}{S:Type}[DecidableEq S][Fintype S]{Z:Census S}
    {P:S→Three G n}{F:Config G n→Poly Z}{o:S→Site n}{w:S→ℝ}{t a b d:ℝ}
    (h:Alcove B P F o w t a b)(le:b≤d):Alcove B P F o w t a d:=by
  obtain ⟨H₀,K₀,ψ,ν,hr,hk,hh,hf,hg,hp,rest⟩:=h.chamber
  exact ⟨h.clef,h.value,h.tally,h.price,H₀,K₀,ψ,ν,hr,hk,hh,hf,hg,fun j=>(hp j).trans le,rest⟩

theorem original (live:m≤N)(i:I)(l:ℕ)(o:V×I→Site ((C).side m per))
    (w:V×I→ℝ)(P:V×I→Three G ((C).side m per))(F:Config G ((C).side m per)→Poly (Stock.census (V×I)))
    {t:ℝ}(file:Alcove (Q) P F o w t δ (1/2))(integral:Integrable F (prior G _))
    (stock:Arsenal (Q))(paid:Furls (A) m t)(pos:∀j,0<w j)
    (seats:Occupancy (fun j:Unit×(V×I)=>o j.2) cap)
    (anchors:Occupancy (fun j:Unit×V=>o (j.2,i)) cap)
    (hull:∀j:V×I,coverNumber (Q).p.B ({o (j.1,i),o j}:Support _)≤l):
    ∃ P':Unit×V→Three G ((C).side m per),
      MenuBoard (Q) P' (fun U=>collect i (F U)) (fun j=>o (j.2,i))
        (wage i w (Q).p.supportExponent δ l) ((Q).p.supportExponent-2) 1 ∧
      ∀j,Blade (Q) (o (j.2,i)) (P' j).2.1 (profile (Q).activities (P' j).2.2)
        0 (4*(1/wage i w (Q).p.supportExponent δ l j)):=by
  classical
  have hr:=(R.makes.wilson.represents N per m live)
  have hparams:(Q).p=(A).budget m:=hr.vac
  have loc:0<Fintype.card I:=Fintype.card_pos_iff.mpr ⟨i⟩
  have seats' (j:Unit×V):((partialGroup Unit (finishGroup V i)).contents j).card≤Fintype.card I:=by
    rcases j with ⟨⟨⟩,j⟩
    rw [contentP,contentF]
    exact (card_image_le.trans card_image_le).trans_eq card_univ
  obtain ⟨ht,hδ,hm,he,h1,h2,h3⟩:=paid.eye
  have F':=WilsonOriginalPublicTrialPhasePad.alcove (larger file (show (1:ℝ)/2≤1 by norm_num))
    hr.good integral pos hδ.le zero_le_one
  obtain ⟨p,hp,hb⟩:=Pantry.breakfast (S:=∅) (finishGroup V i) (select i) loc seats' F'
    hr.good.labels stock (by rw [hparams];linarith) (by simp) (fun a=>pos a.2) ht hδ hm seats anchors
    (fun a=>hull a.2) (by simpa only [hparams] using h1)
    (by simpa only [hparams,Ribbons.scurry] using h2) (by simpa only [hparams,Ribbons.scurry] using h3)
    (fun U=>ne_of_gt (Tour.bright (H) R.makes.wilson N per m live U)) (feed_live _ _ integral)
  exact ⟨p,hp,fun j=>(hb j).2 (notMem_empty _)⟩

end YM.Integration.WilsonOriginalPublicTrialPhaseGroup
