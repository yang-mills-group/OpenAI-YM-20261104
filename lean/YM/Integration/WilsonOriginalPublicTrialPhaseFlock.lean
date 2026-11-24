import YM.Integration.WilsonOriginalPublicTrialPhaseVault
import YM.Integration.WilsonOriginalPublicTrialPhaseCenterMenu
import YM.Integration.WilsonOriginalPublicTrialPhaseRay

/-! A whole replicated original marked menu reaches the older centered vault. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseFlock
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open WilsonOriginalPublicTrialPhaseAccumulated WilsonOriginalPublicTrialPhaseRace
open WilsonOriginalPublicTrialPhaseRay WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Topology ContDiff BigOperators Classical
variable {G:Gauge}(R:Run G){j N per:ℕ}
local notation "C" => R.family
local notation "A" => R.alloy.B.a
local notation "H" => (C).path
local notation "P" => (H).rep N per
local notation "O" => (H).levels.clock.op
local notation "F" => (C).labels.level 0
local notation "loc" => (C).localSection 0
local notation "V" => Unit × Site ((C).side j per)

def tiles {u:ℕ}(ju:j≤u)(o:∀i,Site ((C).side (u+i) per))(i:ℕ)(v:V):Site ((C).side (u+i) per):=
  (tilesAt (C).S per (ju.trans (Nat.le_add_right u i))).copyMap v.2 (o i)

set_option maxHeartbeats 1900000 in
theorem original (hG:G.Simple)(cater:Cater (C) R.doors)(purchase:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors)(u h:ℕ)(ju:j≤u)(length:0<h)(live:u+h≤N)
    (o:∀i,Site ((C).side (u+i) per))(parent:∀i,i<h→((O) (u+i) per).ratio.parent (o (i+1))=o i)
    (grade:∀i,i<h→3≤(A).clock.J (u+i))
    (hit:∀i,i<h→Push.Local.hitWidth ((P) (u+i)).p*Push.Local.kappa (H) (u+i)≤1)
    (fine:∀i,i≤h→Push.Local.kappa (H) (u+i)≤1)
    (r:ℝ)(hr:0<r)(top:V → Coefficient (F) ((C).side (u+h) per))
    (fmt:∀v,(top v).Format (tiles R ju o h v) (C).params ((P) (u+h)))
    (rem:∀v,(top v).remBound (tiles R ju o h v) ((P) (u+h)) (Push.Local.kappa (H) (u+h)) r)
    (F₀:Config G ((C).side (u+h) per)→Poly (Stock.census V))(e:ℝ)
    (fund:MenuBoard ((P) (u+h)) (fun v=>invoice (top v) (tiles R ju o h v) (loc) ((P) (u+h)))
      F₀ (tiles R ju o h) (fun _=>weight (C).S r (u+h) (u+h)) e 1)
    (pitch:((P) (u+h)).p.supportExponent-4≤e)
    (room:∀i,i<h→pdist (o i)+pdist (o i)+(((H).levels.budget (u+i)).B)*
      guard (C).S (u+i) (Bandage.renal (H).levels (u+i))<
      ((C).S.toDepth (ju.trans (Nat.le_add_right u i)) per).count.val):
    let w:=weight (C).S r (u+h) u
    let a:=fun v=> gust (H) N per (u+h) (invoice (top v) (tiles R ju o h v) (loc) ((P) (u+h))).1
      u (Nat.le_add_right ..) 1 /(((P) u).eval 1:ℂ)
    let inlet:=shift (fun v=> -a v) F₀
    ∃q:V → Coefficient (F) ((C).side u per),
      MenuBoard ((P) u) (fun v=>row (q v) (tiles R ju o 0 v) (loc) ((P) u) 0)
        (gust (H) N per (u+h) inlet u (Nat.le_add_right ..)) (tiles R ju o 0) (fun _=>w)
        ((H).levels.budget u).supportExponent 1 ∧
      Vault (fun _:V=>w) (fun v=>(row (q v) (tiles R ju o 0 v) (loc) ((P) u) 0).2.1)
        (fun v=>profile ((P) u).activities (row (q v) (tiles R ju o 0 v) (loc) ((P) u) 0).2.2)
        (w*wage (C).S r (u+h) u) (w*wage (C).S r (u+h) u):=by
  intro w a inlet
  let p:=tiles R ju o
  have par v i (t:i<h): ((O) (u+i) per).ratio.parent (p (i+1) v)=p i v:=by
    have k:=WilsonOriginalPublicTrialPhaseTileSites.parent R (ju.trans (Nat.le_add_right u i)) v.2 (o (i+1))
    change ((C).S.oneStep (u+i) per).parent (p (i+1) v)=_
    rw [show ((C).S.oneStep (u+i) per).parent (p (i+1) v)=_ from k]
    exact congrArg ((tilesAt (C).S per (ju.trans (Nat.le_add_right u i))).copyMap v.2) (parent i t)
  have sell (v:V):= WilsonOriginalPublicTrialPhaseSettled.original R hG purchase stock u h live
    (fun i=>p i v) (par v) grade hit (fun i e=>fine (i+1) e) r hr.le (top v) (fmt v) (rem v)
  choose bank z head ground center ledger rides using sell
  let F' (i)(l:i≤h):=gust (H) N per (u+h) inlet (u+i) (by omega)
  let Y (i)(t:i≤h)(v:V):=row (bank v i t) (p i v) (loc) ((P) (u+i)) (z v i)
  let s:=fun i=>weight (C).S r (u+h) (u+i)
  let tag i:=if i=h then e else ((H).levels.budget (u+i)).supportExponent
  have crew (i)(t:i≤h):MenuBoard ((P) (u+i)) (Y i t) (F' i t) (p i) (fun _=>s i) (tag i) 1:=by
    induction t using Nat.decreasingInduction with
    | self=>
      have initial:=WilsonOriginalPublicTrialPhaseCenterMenu.original R live fund (fun v=> -a v)
      have eq:Y h le_rfl=fun v=>WilsonOriginalPublicTrialPhaseScalar.deposit ((P) (u+h))
          (invoice (top v) (p h v) (loc) ((P) (u+h))) (-a v):=by
        funext v
        change row (bank v h le_rfl) _ _ _ (z v h)=_
        rw [head,center]
        simpa only [sub_eq_neg_add] using keep (top v) (p h v) (loc) ((P) (u+h)) (-a v)
      rw [eq]
      simpa only [F',gust_base,tag,if_pos rfl] using initial
    | of_succ i t ih=>
      let m:=u+i
      let g:=guard (C).S m (Bandage.renal (H).levels m)
      have door:m<N:=by dsimp [m];omega
      obtain ⟨_,_,course,-,-⟩:=cater.tiers m N per door
      have rentpos:0<Bandage.renal (H).levels m:=course.poses.hats.1
      have reach:pdist (((O) m per).ratio.parent (o (i+1)))+
          pdist (((O) m per).ratio.parent (o (i+1)))+((H).levels.budget m).B*g<
          ((C).S.toDepth (ju.trans (Nat.le_add_right u i)) per).count.val:=by
        rw [parent i t]
        exact room i t
      let E:=fun v:V=>(2+Doors.rate ((C).S.block m))*wage (C).S r (u+h) (u+(i+1))+‖z v (i+1)‖
      have audit (v:V):2*s (i+1)*E v≤1:=paid (C).S hr (u+h) m (ledger v (i+1) t).2.2
      have get:=WilsonOriginalPublicTrialPhaseRenew.original R cater door
        (ju.trans (Nat.le_add_right u i)) g (o (i+1)) (wide ..) reach
        (fun _=>s (i+1)) (fun _=>s i) E (Y (i+1) t) (Y i t.le) (F' (i+1) t) (tag (i+1)) ih
      rw [show ((O) m per).ratio.parent (o (i+1))=o i from parent i t] at get
      have pre:((P) (u+(i+1))).p.supportExponent-4≤tag (i+1):=by
        by_cases k:i+1=h
        · subst h
          simpa only [tag,if_pos rfl] using pitch
        · have pars:((P) (u+(i+1))).p=(H).levels.budget (u+(i+1)):=
            (R.makes.wilson.represents N per (u+(i+1)) (by omega)).vac
          simp only [tag,if_neg k,pars]
          linarith
      have result:=get pre (fun _=>weight_pos (C).S hr ..) (fun _=>weight_pos (C).S hr ..) audit
        (fun _=>rent (C).S hr (u+h) m rentpos) (fun v=>rides v i t)
      rw [show tag i=((H).levels.budget m).supportExponent from if_neg t.ne]
      unfold F'
      rw [gust_step (H) N per (u+h) inlet (show u+i<u+h by omega)]
      convert! result using 1
  have fin:=crew 0 (Nat.zero_le _)
  have vault:=WilsonOriginalPublicTrialPhaseVault.original ((P) u) (loc)
    (fun v=>bank v 0 (Nat.zero_le _)) (p 0) (fun v=>(ledger v 0 (Nat.zero_le _)).2.1) (fine 0 (Nat.zero_le _))
    (w:=w) (weight_pos (C).S hr (u+h) u).le
  refine ⟨fun v=>bank v 0 (Nat.zero_le _),?_,vault⟩
  simp only [Y,ground,F',tag,if_neg length.ne,Nat.add_zero] at fin
  convert! fin using 1

end YM.Integration.WilsonOriginalPublicTrialPhaseFlock
end
