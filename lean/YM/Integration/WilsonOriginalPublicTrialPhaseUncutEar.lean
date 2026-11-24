import YM.Integration.WilsonOriginalPublicTrialPhaseUncutCourse
import YM.Integration.WilsonOriginalPublicTrialPhaseCaptureSeats
import YM.Integration.WilsonOriginalPublicTrialPhaseGroupedCapture
import YM.Integration.WilsonOriginalPublicTrialPhaseAward
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyCourseFare

/-! The complete fitted K product pays its original centered all-copy phase, before both physical regulators. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseUncutEar
open Finset Function Filter MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open Cells WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Classical BigOperators ContDiff
open WilsonOriginalPublicTrialPhaseFaceCenter WilsonOriginalPublicTrialPhaseGroupedWord
open WilsonOriginalPublicTrialPhaseRay WilsonOriginalPublicTrialPhaseCopiedCourse
open WilsonOriginalPublicTrialPhaseGrant WilsonOriginalPublicTrialPhaseFlock
open WilsonOriginalPublicTrialPhaseCaptureFare (reserve)
open WilsonOriginalPublicTrialPhaseRate (volume)
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G)
local notation "C" => R.family
local notation "S" => (C).S
local notation "A" => (C).path
local notation "H" i:arg => (A).levels.clock.hatBeta i
local notation "P" N:arg per:arg i:arg => (A).rep N per i
local notation "O" i:arg per:arg => (A).levels.clock.op i per
local notation "load" => Fintype.card I*Fintype.card Signed

set_option maxHeartbeats 4200000 in
theorem original {T₀:Campaign R}(book:Campaign.Pillars R T₀)(simple:G.Simple)
    (purchase:RG05Preconstruction.ReadoutPurchase R.b)(storage:RG05Readout.Many.Storage (C) R.doors)
    (cater:Cater (C) R.doors)(d:I→ℕ)(anchor:I)(T:I→ℝ)(tp:∀k,0≤T k)(e:I→ℕ)
    (j u:ℕ)(ju:j≤u)(q aperture L:ℕ)(ceiling:∀i,((A).levels.budget i).supportExponent=100):
    ∀ᶠ c:ℕ in atTop,∀f K N per:ℕ,∀uc:u<c,c≤f → f≤K → ∀ck:c+1<K,K≤N →
    H K≤2*H c → (S).a c/(S).a K≤(H c)^aperture →
    ∀o:∀i:ℕ,I→Site ((C).side i per),
    (∀i,(u ≤ i) → (i < K) → (O i per).ratio.parent ∘ o (i+1)=o i) →
    ∀v:∀k,(C).label (d k),
    (∀k,((C).labels.level (d k)).coeffSize (v k)≤T k*(H K)^(e k)) →
    (∀k,((((C).localSection (d k)).footprint (o K k)).card:ℝ)*(A).levels.clock.forcedAllowance K≤1) →
    volume (P N per K).p.B*(A).levels.clock.forcedAllowance K≤Real.log 2/2 →
    ∀radius:ℕ,(∀k,window (o K k) (stencilRadius (C) (d k))⊆window 0 radius) →
    Push.GridApprox.room (A).levels j K radius →
    (∀k,coverNumber (P N per (c+1)).p.B ({o (c+1) anchor,o (c+1) k}:Support _)≤L) →
    (∀i,(c ≤ i) → (i < K) → load≤apron (A).levels i) →
    (∀i,(u ≤ i) → (i ≤ c) → 3≤(A).levels.clock.J i) →
    (∀i,(u ≤ i) → (i < c) → hitWidth (P N per i).p*kappa (A) i≤1) →
    (∀i,(u ≤ i) → (i ≤ c) → kappa (A) i≤1) →
    (∀i,(u ≤ i) → (i < c) → ∀ (ji : j ≤ i),
      pdist (o i anchor)+pdist (o i anchor)+((A).levels.budget i).B*
      guard (S) i (Bandage.renal (A).levels i)<((S).toDepth ji per).count.val) →
    ∃ g:Grant R (N:=N) (u:=u) d (o K) v (by omega) (1/(H f)^q),g.station=j:=by
  classical
  obtain ⟨D,E,U,one,dCap,seed⟩:=WilsonMeasuredPublicEntranceTransferCopySeedRoster.original R d load 100 T tp e
  let Z:=((S).a j/(S).a u)^4*Vac.treasury (A).levels u
  have salaries:=WilsonMeasuredPublicEntranceTransferCopyCourseFare.original R simple anchor u q aperture D E L U 100 Z
    (zero_le_one.trans one) (by norm_num)
  have incoming:=(tendsto_add_atTop_nat 1).eventually (WilsonOriginalPublicTrialPhaseUncutCourse.original R book simple purchase storage cater d)
  filter_upwards [salaries,incoming] with c sale course
  intro f K N per uc cf fk ck live heat optical o homes v measured small first radius fits space hull slots grade hit fine room
  obtain ⟨h,rfl⟩:=Nat.exists_eq_add_of_le uc.le
  have uc₀:u≤u+h:=Nat.le_add_right _ _
  have jc:j≤u+h:=ju.trans uc₀
  have uk:u≤K:=by omega
  have jk:j≤K:=ju.trans uk
  let c:=u+h
  have shape(i:ℕ)(alive:i≤N):(P N per i).p=((A).levels.budget i):=
    (R.makes.wilson.represents N per i alive).vac
  have support(i:ℕ)(alive:i≤N):(P N per i).p.supportExponent=100:=by rw [shape i alive,ceiling]
  let B:=fun k=>WilsonOriginalPublicTrialPhaseFittedSeats.stock R (d k) load K 100 (T k) (e k)
  let w:=WilsonOriginalPublicTrialPhaseFittedSeats.fare R (N:=N) d (o K) v
  let l:=fun i k=>WilsonOriginalPublicTrialPhaseSpine.capital (S) (d k) K i (B k)
  let V:=Site ((C).side j per)
  let γ:=WilsonOriginalPublicTrialPhaseRowRun.width (Bandage.renal (A).levels) (fun k:V×I=>w k.2)
    (fun i (k:V×I)=>l i k.2) K (c+1) ck.le
  obtain ⟨seeds,X,rows⟩:=course j K N per (jc.trans (Nat.le_succ _)) ck live o
    (fun i ib=>homes i (uc₀.trans ((Nat.le_succ _).trans ib))) v small first
    (by rw [support K live];norm_num) 100 T e tp (ceiling K).le measured
    (fun i ib=>slots i ((Nat.le_succ _).trans ib))
  obtain ⟨positive,t,paid,file⟩:=rows (c+1) le_rfl ck
  obtain ⟨cap,cp,spent,buy⟩:=sale f K cf fk ck.le heat optical
  have seedBound:=seed K N per live (o K) v (ceiling K).le measured
  have fee(i:Unit×V):1/WilsonOriginalPublicTrialPhaseGroup.wage anchor γ (P N per (c+1)).p.supportExponent
      (Bandage.renal (A).levels (c+1)) L i≤cap:=by
    rcases i with ⟨⟨⟩,s⟩
    rw [one_div]
    exact buy s (fun k:V×I=>d k.2) (fun k:V×I=>B k.2) (fun k:V×I=>w k.2)
      _ L (fun k=>dCap k.2) (fun k=>zero_le_one.trans (seeds k.2).1)
      (fun k=>(seedBound k.2).2.1) (fun k=>(seeds k.2).2.1) (fun k=>(seeds k.2).2.2)
      (support (c+1) (ck.le.trans live)).le le_rfl
  have parentC:=homes c uc₀ (by omega)
  obtain ⟨allSeats,joined,covered,fresh,parents⟩:=WilsonOriginalPublicTrialPhaseCaptureSeats.original R jc
    anchor L (o (c+1)) (o c) parentC (slots (c+1) (Nat.le_succ _) ck) (slots c le_rfl (by omega)) hull
  obtain ⟨rp,top,fmt,rem,board⟩:=WilsonOriginalPublicTrialPhaseGroupedCapture.original R cater storage jk ck.le live
    (grade c uc₀ le_rfl) d (o K) v anchor L (root R (o (c+1))) γ positive _ paid file
    allSeats joined covered fresh parents cap cp fee
  let ref:=fun i=>o (u+i) anchor
  have targets:(fun i:Unit×V=>(O c per).ratio.parent (root R (o (c+1)) (i.2,anchor)))=
      tiles R ju ref h:=by
    funext i
    rw [WilsonOriginalPublicTrialPhaseCopiedCourse.parent R jc,parentC]
    simp only [WilsonOriginalPublicTrialPhaseCopiedCourse.root,dif_pos jc,tiles,ref,c]
  rw [targets] at fmt rem board
  have pitch:(P N per c).p.supportExponent-4≤((A).levels.budget c).supportExponent:=by
    rw [shape c (by omega)];linarith
  obtain ⟨g,same,_,_,_⟩:=WilsonOriginalPublicTrialPhaseAward.original R simple cater purchase storage u h K ju
    (by omega) (by omega) live d (o K) v radius fits space ref
    (fun i hi=>congrFun (homes (u+i) (by omega) (by omega)) anchor)
    (fun i hi=>grade (u+i) (by omega) (by omega)) (fun i hi=>hit (u+i) (by omega) (by omega))
    (fun i hi=>fine (u+i) (by omega) (by omega)) _ rp top fmt rem _ board pitch
    (fun i hi=>room (u+i) (by omega) (by omega) _)
  exact ⟨{g with charge:=g.charge.trans spent},same⟩

end YM.Integration.WilsonOriginalPublicTrialPhaseUncutEar
end
