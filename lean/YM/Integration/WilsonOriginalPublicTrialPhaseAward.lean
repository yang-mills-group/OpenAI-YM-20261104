import YM.Integration.WilsonOriginalPublicTrialPhaseTileCenters
import YM.Integration.WilsonOriginalPublicTrialPhaseCensusNames
import YM.Integration.WilsonOriginalPublicTrialPhaseGrant

/-! An original captured menu pays the all-copy Gibbs phase of the same complete fitted K word. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseAward
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

open WilsonOriginalPublicTrialPhaseFlock WilsonOriginalPublicTrialPhaseFaceCenter
open WilsonOriginalPublicTrialPhaseTrace WilsonOriginalPublicTrialPhaseTerminal
open WilsonOriginalPublicTrialPhaseCensusNames WilsonOriginalPublicTrialPhaseGrant
open MergeProof.Bouquet

set_option maxHeartbeats 2200000 in
theorem original (hG:G.Simple)(cater:Cater (C) R.doors)(purchase:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors)(u h K:ℕ)(ju:j≤u)(length:0<h)(ck:u+h≤K)(live:K≤N)
    {I:Type}[Fintype I](d:I→ℕ)(z:I→Site ((C).side K per))(v:∀i,(C).label (d i))
    (radius:ℕ)(fits:∀i,GridApprox.window (z i) (stencilRadius (C) (d i))⊆GridApprox.window 0 radius)
    (space:Push.GridApprox.room (H).levels j K radius)
    (o:∀i,Site ((C).side (u+i) per))(parent:∀i,i<h→((O) (u+i) per).ratio.parent (o (i+1))=o i)
    (grade:∀i,i<h→3≤(A).clock.J (u+i))
    (hit:∀i,i<h→Push.Local.hitWidth ((P) (u+i)).p*Push.Local.kappa (H) (u+i)≤1)
    (fine:∀i,i≤h→Push.Local.kappa (H) (u+i)≤1)
    (r:ℝ)(hr:0<r)(top:V → Coefficient (F) ((C).side (u+h) per))
    (fmt:∀v,(top v).Format (tiles R ju o h v) (C).params ((P) (u+h)))
    (rem:∀v,(top v).remBound (tiles R ju o h v) ((P) (u+h)) (Push.Local.kappa (H) (u+h)) r)
    (e:ℝ)
    (fund:MenuBoard ((P) (u+h)) (fun v=>invoice (top v) (tiles R ju o h v) (loc) ((P) (u+h)))
      (gust (H) N per K (cohort R (N:=N) ((ju.trans (Nat.le_add_right u h)).trans ck) (word R (N:=N) d z v)) (u+h) ck)
      (tiles R ju o h) (fun _=>weight (C).S r (u+h) (u+h)) e 1)
    (pitch:((P) (u+h)).p.supportExponent-4≤e)
    (room:∀i,i<h→pdist (o i)+pdist (o i)+(((H).levels.budget (u+i)).B)*
      guard (C).S (u+i) (Bandage.renal (H).levels (u+i))<
      ((C).S.toDepth (ju.trans (Nat.le_add_right u i)) per).count.val):
    let w:=weight (C).S r (u+h) u
    let a:=w*wage (C).S r (u+h) u
    ∃ g:Grant R (N:=N) d z v ((Nat.le_add_right u h).trans ck)
        (Real.exp (((C).S.a j/(C).S.a u)^4*Vac.treasury (H).levels u+a+a+2)/w),
      g.station=j ∧ g.salary=w ∧ g.soft=a ∧ g.hard=a:=by
  intro w a
  let uc:u≤u+h:=Nat.le_add_right u h
  let uk:=uc.trans ck
  let jk: j≤K:=ju.trans uk
  let M:=word R (N:=N) d z v
  let center:=actualTransport (C) (N:=N) M uk 1
  let qK:=cohort R (N:=N) jk M
  let qC:=gust (H) N per K qK (u+h) ck
  have reg:Continuous M:=WilsonOriginalPublicTrialPhaseWhole.continuous_file R d z v
  have earn:=funds R jk live M reg
  obtain ⟨q,board,vault⟩:=WilsonOriginalPublicTrialPhaseFlock.original R hG cater purchase stock
    u h ju length (ck.trans live) o parent grade hit fine r hr top fmt rem qC e fund pitch room
  have equation:=WilsonOriginalPublicTrialPhaseTileCenters.original R ju uc ck live M earn.1 earn.2 fund
  change gust (H) N per (u+h) _ u uc=gust (H) N per K (cohort R (N:=N) jk (fun U=>M U-center)) u uk at equation
  have served:=Relabel.moved (unmark (Site ((C).side j per))) board.grants
  rw [equation,submitted R ju uk live (fun U=>M U-center) (reg.sub continuous_const)] at served
  let b(i:Site ((C).side j per)):=row (q ((),i)) (tiles R ju o 0 ((),i)) (loc) ((P) u) 0
  let g:Grant R (N:=N) d z v uk (Real.exp (((C).S.a j/(C).S.a u)^4*Vac.treasury (H).levels u+a+a+2)/w):={
    station:=j, radius:=radius, early:=ju, fits:=fits, housing:=space,
    salary:=w, soft:=a, hard:=a, rent:=1, pos:=weight_pos _ hr _ _,
    regular:=fun i=>(b i).2.1, forced:=fun i=>profile ((P) u).activities (b i).2.2,
    homes:=fun i=>tiles R ju o 0 ((),i), serves:=served,
    vault:=⟨fun i=>vault.1 ((),i),fun i=>vault.2 ((),i)⟩, charge:=by norm_num }
  exact ⟨g,rfl,rfl,rfl,rfl⟩

end YM.Integration.WilsonOriginalPublicTrialPhaseAward
end
