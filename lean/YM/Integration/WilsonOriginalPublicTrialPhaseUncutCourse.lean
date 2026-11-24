import YM.Integration.WilsonOriginalPublicTrialPhaseFittedSeats

/-! The actual uncut finite physical roster buys its copied ordinary and hard hierarchy before capture. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseUncutCourse
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
open Filter WilsonOriginalPublicTrialPhaseSpine WilsonOriginalPublicTrialPhaseRowRun
open WilsonOriginalPublicTrialPhaseFittedSeats (fare)
open WilsonOriginalPublicTrialPhaseCopiedCourse
open WilsonOriginalPublicTrialPhaseRate (volume)
variable {G:Gauge}{I:Type}[DecidableEq I][Fintype I](R:Run G)
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" N:arg per:arg i:arg => (A).rep N per i
local notation "O" i:arg per:arg => (A).levels.clock.op i per
local notation "load" => Fintype.card I*Fintype.card Signed

def spread {F:ℕ→Type*}(b h:ℕ)(fallback:∀i,F i)(q:∀i,i≤h→F (b+i))(m:ℕ):F m:=
  if bm:b ≤ m then if mh:m-b≤h then (show b+(m-b)=m by omega) ▸ q (m-b) mh else fallback m else fallback m

theorem entry {F:ℕ→Type*}(b h:ℕ)(fallback:∀i,F i)(q:∀i,i≤h→F (b+i))(i:ℕ)(ih:i≤h):
    spread b h fallback q (b+i)=q i ih:=by
  have casted (k:ℕ)(hk:k≤h)(eq:k=i)(rel:b+k=b+i):rel ▸ q k hk=q i ih:=by
    subst k;rfl
  unfold spread
  rw [dif_pos (show b ≤ b+i by omega),dif_pos (show b+i-b≤h by omega)]
  exact casted _ _ (by omega) _

set_option maxHeartbeats 3000000 in
theorem original {T₀:Campaign R}(book:Campaign.Pillars R T₀)(simple:G.Simple)
    (purchase:RG05Preconstruction.ReadoutPurchase R.b)(storage:RG05Readout.Many.Storage (C) R.doors)
    (cater:Cater (C) R.doors)(d:I→ℕ):
    ∀ᶠ b:ℕ in atTop,∀j K N per:ℕ,∀jb:j ≤ b,∀before:b < K,K≤N →
    ∀o:∀i:ℕ,I→Site ((C).side i per),
    (∀i,(b ≤ i) → (i < K) → (O i per).ratio.parent ∘ o (i+1)=o i) →
    ∀v:∀k,(C).label (d k),
    (∀k,((((C).localSection (d k)).footprint (o K k)).card:ℝ)*(A).levels.clock.forcedAllowance K≤1) →
    volume (P N per K).p.B*(A).levels.clock.forcedAllowance K≤Real.log 2/2 → 0≤(P N per K).p.supportExponent-3 →
    ∀α:ℝ,∀T:I→ℝ,∀e:I→ℕ,(∀i,0≤T i) → ((A).levels.budget K).supportExponent≤α →
    (∀i,((C).labels.level (d i)).coeffSize (v i)≤T i*((A).levels.clock.hatBeta K)^(e i)) →
    (∀i,(b ≤ i) → (i < K) → load ≤ apron (A).levels i) →
    let B:=fun k=>WilsonOriginalPublicTrialPhaseFittedSeats.stock R (d k) load K α (T k) (e k)
    let w:=fare R (N:=N) d (o K) v
    let l:=fun i k=>capital (C).S (d k) K i (B k)
    (∀k,1≤B k ∧ 0<w k ∧ (w k)⁻¹≤B k) ∧
    ∃X:∀m:ℕ,I→Three G ((C).side m per),
      ∀i,(b ≤ i) → ∀hi:i<K,
      let γ:=width (Bandage.renal (A).levels) (fun u:Site ((C).side j per)×I=>w u.2)
        (fun m u=>l m u.2) K i hi.le
      (∀u,0<γ u) ∧ ∃t,Furls (A).levels i t ∧
        Alcove (P N per i) (ink R (N:=N) K d (X i))
          (gust (A) N per K (WilsonOriginalPublicTrialPhaseGroupedWord.origin R (N:=N) (jb.trans before.le) d (o K) v) i hi.le)
          (root R (o i)) γ t (Bandage.renal (A).levels i) (1/2):=by
  classical
  filter_upwards [eventually_all.2 (fun k:I=>WilsonOriginalPublicTrialPhaseSpine.original R simple purchase storage (d k)),
    eventually_ge_atTop 1] with b priced late
  intro j K N per jb before live o homes v small opening ex α T e tp support measured slots
  obtain ⟨h,rfl⟩:=Nat.exists_eq_add_of_le before.le
  intro B w l
  obtain ⟨receipts,q,earned,birth⟩:=WilsonOriginalPublicTrialPhaseFittedSeats.original R book (jb.trans before.le) live
    d (o (b+h)) v small opening ex α T e tp support measured
  choose t head facts steps using fun k:I=>priced k h N per live (fun i=>o (b+i) k)
    (fun i hi=>congrFun (homes (b+i) (by omega) (by omega)) k) (B k) (zero_le_one.trans (receipts k).1)
    (q k) (earned k).2.1 (earned k).2.2.1 (earned k).2.2.2
  let localRow(i:ℕ)(hi:i≤h):I→Three G ((C).side (b+i) per):=fun k=>
    invoice (t k i hi) (o (b+i) k) ((C).localSection (d k)) (P N per (b+i))
  let X:=spread b h (F:=fun m=>I→Three G ((C).side m per)) (fun _=>0) localRow
  have current(i:ℕ)(hi:i≤h):X (b+i)=localRow i hi:=entry _ _ _ _ _ hi
  have exactHead:X (b+h)=fun k=>invoice (q k) (o (b+h) k) ((C).localSection (d k)) (P N per (b+h)):=by
    rw [current h le_rfl]
    funext k
    exact congrArg (fun s=>invoice s (o (b+h) k) ((C).localSection (d k)) (P N per (b+h))) (head k)
  have signed(i:ℕ)(bi:b ≤ i)(hi:i<b+h)(k:I):
      Ride (O i per) (o (i+1) k) ((O i per).ratio.parent (o (i+1) k))
        (R.doors N per i (hi.trans_le live)) ((((C).S.block i).val:ℂ)^(d k)) (X (i+1) k) (X i k) (l i k):=by
    obtain ⟨z,rfl⟩:=Nat.exists_eq_add_of_le bi
    have zh:z<h:=by omega
    have located:(O (b+z) per).ratio.parent (o (b+z+1) k)=o (b+z) k:=congrFun (homes (b+z) bi hi) k
    rw [located]
    change Ride (O (b+z) per) _ _ _ _ (X (b+(z+1)) k) (X (b+z) k) _
    rw [current (z+1) zh,current z zh.le]
    exact (steps k z zh).1
  have nn(i:ℕ)(k:I):0≤l i k:=
    mul_nonneg (pow_nonneg (div_nonneg ((C).S.a_pos _).le ((C).S.a_pos _).le) _) (zero_le_one.trans (receipts k).1)
  refine ⟨receipts,X,?_⟩
  apply WilsonOriginalPublicTrialPhaseCopiedCourse.original R storage cater jb late before live d o homes
    X v w (fun k=>(receipts k).2.1) l nn slots signed
  rw [exactHead]
  exact birth

end YM.Integration.WilsonOriginalPublicTrialPhaseUncutCourse
end
