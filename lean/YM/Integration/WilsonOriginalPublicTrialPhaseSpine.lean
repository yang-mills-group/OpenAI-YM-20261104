import YM.Integration.WilsonOriginalPublicTrialPhaseCapturePost
import YM.Integration.WilsonMeasuredPublicEntranceTransferCopyPaidAddress

/-! The honest original one-name trajectory before capture, with its real engineering compensation. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalPublicTrialPhaseSpine
open Finset Function MeasureTheory Lattice Wilson RG Source Labels Extra.Histories
open Push Local Planned.GuardedAtom Guard MergeProof MergeProof.Accent MergeProof.Menu Marker Ac
open GridApprox.Nil Extra.Trajectories Extra.Multi PhysicalNext.Repeat PhysicalNext.Repeat.Lotus
open RG05Readout RG05Readout.Address RG05Readout.Many RG05Readout.Pantry
open OPE.Therm Push.GridApprox PhysicalNext.Repeat.Legato PhysicalNext.Repeat.Legato.Campaign
open WilsonOriginalPublicTrialPhaseAccumulated WilsonOriginalPublicTrialPhaseRace
open WilsonOriginalPublicTrialPhaseRay WilsonOriginalPublicTrialPhaseCenterMenu
open scoped Topology ContDiff BigOperators Classical
open Filter
variable {G:Gauge}

def capital (S:Schedule)(d K i:ℕ)(B:ℝ):ℝ:=(S.a i/S.a K)^(d+4)*B
def share (S:Schedule)(d K i:ℕ):ℂ:=(↑(S.a K/S.a i):ℂ)^d

theorem capital_base (S:Schedule)(d K:ℕ)(B:ℝ):capital S d K K B=B:=by
  simp [capital,div_self (S.a_pos K).ne']
theorem capital_step (S:Schedule)(d K i:ℕ)(B:ℝ):
    ((S.block i).val:ℝ)^(d+4)*capital S d K (i+1) B=capital S d K i B:=by
  have h:0<((S.block i).val:ℝ):=by exact_mod_cast (S.block i).property
  have eq:((S.block i).val:ℝ)*(S.a (i+1)/S.a K)=S.a i/S.a K:=by
    rw [S.a_step];field_simp
  rw [capital,capital,←mul_assoc,←mul_pow,eq]
theorem share_base (S:Schedule)(d K:ℕ):share S d K K=1:=by simp [share,div_self (S.a_pos K).ne']
theorem paid_share (S:Schedule)(d K:ℕ){i:ℕ}(hi:i≤K):‖share S d K i‖≤1:=by
  have mono:Antitone S.a:=antitone_nat_of_succ_le (fun i=>by
    rw [S.a_step];apply div_le_self (S.a_pos i).le;exact_mod_cast (S.block i).property)
  have h:(S.a K/S.a i)≤1:=(div_le_one (S.a_pos i)).2 (mono hi)
  simp only [share,norm_pow,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (S.a_pos _).le (S.a_pos _).le)]
  exact pow_le_one₀ (div_nonneg (S.a_pos _).le (S.a_pos _).le) h
theorem share_step (S:Schedule)(d K i:ℕ):
    share S d K i*((S.block i).val:ℂ)^d=share S d K (i+1):=by
  have ht:0<((S.block i).val:ℝ):=by exact_mod_cast (S.block i).property
  simp only [share,S.a_step,Complex.ofReal_div,Complex.ofReal_natCast,←mul_pow]
  congr 1
  field_simp [Complex.ofReal_ne_zero.mpr (S.a_pos i).ne']

variable (R:Run G)
local notation "C" => R.family
local notation "A" => (C).path
local notation "P" N:arg p:arg m:arg => (A).rep N p m
local notation "O" m:arg p:arg => (A).levels.clock.op m p

set_option maxHeartbeats 2200000 in
theorem original (simple:G.Simple)(purchase:RG05Preconstruction.ReadoutPurchase R.b)
    (stock:RG05Readout.Many.Storage (C) R.doors)(d:ℕ):
    ∀ᶠ b:ℕ in atTop,∀ h N per:ℕ,∀live:b+h≤N,
    ∀ o:∀i,Site ((C).side (b+i) per),
    (∀i,i<h→(O (b+i) per).ratio.parent (o (i+1))=o i) →
    ∀ B:ℝ,0≤B→∀seed:Coefficient ((C).labels.level d) ((C).side (b+h) per),
    seed.Format (o h) (C).params (P N per (b+h)) →
    seed.remBound (o h) (P N per (b+h)) (Push.Local.kappa (A) (b+h)) B →
    ((C).labels.level d).coeffSize seed.x≤B →
    ∃ T:∀i:ℕ,i≤h→ Coefficient ((C).labels.level d) ((C).side (b+i) per),
      T h le_rfl=seed ∧
      (∀i (hi:i≤h),(T i hi).Format (o i) (C).params (P N per (b+i)) ∧
        (T i hi).remBound (o i) (P N per (b+i)) (Push.Local.kappa (A) (b+i)) (capital (C).S d (b+h) (b+i) B) ∧
        ((C).labels.level d).coeffSize (T i hi).x≤capital (C).S d (b+h) (b+i) B) ∧
      ∀i (hi:i<h),Ride (O (b+i) per) (o (i+1)) (o i) (R.doors N per (b+i) (by omega)) ((((C).S.block (b+i)).val:ℂ)^d)
        (invoice (T (i+1) hi) (o (i+1)) ((C).localSection d) (P N per (b+i+1)))
        (invoice (T i hi.le) (o i) ((C).localSection d) (P N per (b+i)))
        (capital (C).S d (b+h) (b+i) B) ∧
      Ride (O (b+i) per) (o (i+1)) (o i) (R.doors N per (b+i) (by omega)) 1
        (share (C).S d (b+h) (b+i+1) • invoice (T (i+1) hi) (o (i+1)) ((C).localSection d) (P N per (b+i+1)))
        (share (C).S d (b+h) (b+i) • invoice (T i hi.le) (o i) ((C).localSection d) (P N per (b+i)))
        (capital (C).S d (b+h) (b+i) B):=by
  obtain ⟨floor,go⟩:=eventually_atTop.mp (WilsonMeasuredPublicEntranceTransferCopyPaidAddress.original R simple purchase stock d)
  filter_upwards [eventually_ge_atTop floor] with b hb
  intro h N per live o parent B hp seed fmt rem coeff
  let S:=(C).S
  let cap(i:ℕ):=capital S d (b+h) (b+i) B
  let Ledger (i:ℕ):={q:Coefficient ((C).labels.level d) ((C).side (b+i) per)//
    q.Format (o i) (C).params (P N per (b+i)) ∧
    q.remBound (o i) (P N per (b+i)) (Push.Local.kappa (A) (b+i)) (cap i) ∧
    ((C).labels.level d).coeffSize q.x≤cap i}
  have non(i:ℕ):0≤cap i:=mul_nonneg (pow_nonneg (div_nonneg (S.a_pos _).le (S.a_pos _).le) _) hp
  let top:Ledger h:=⟨seed,fmt,by simpa only [cap,capital_base] using rem,by simpa only [cap,capital_base] using coeff⟩
  have next(i:ℕ)(hi:i<h)(q:Ledger (i+1)):
      ∃p:Ledger i,Ride (O (b+i) per) (o (i+1)) (o i) (R.doors N per (b+i) (by omega)) ((((C).S.block (b+i)).val:ℂ)^d)
        (invoice q.val (o (i+1)) ((C).localSection d) (P N per (b+i+1)))
        (invoice p.val (o i) ((C).localSection d) (P N per (b+i))) (cap i):=by
    obtain ⟨k,kfmt,krem,kbound,ride⟩:=go (b+i) (by omega) N per (by omega) (o (i+1)) q.val
      (cap (i+1)) (cap (i+1)) (non _) le_rfl q.property.2.2 q.property.1 q.property.2.1
    rw [parent i hi] at kfmt krem ride
    have bills:(((C).S.block (b+i)).val:ℝ)^(d+4)*cap (i+1)=cap i:=capital_step S d (b+h) (b+i) B
    rw [bills] at krem kbound ride
    exact ⟨⟨k,kfmt,krem,kbound⟩,ride⟩
  let prev i hi q:=(next i hi q).choose
  let t i hi:=WilsonOriginalPublicTrialPhaseRace.back h top prev i hi
  refine ⟨fun i hi=>(t i hi).val,?_,fun i hi=>(t i hi).property,?_⟩
  · change (t h le_rfl).val=seed
    rw [show t h le_rfl=top from WilsonOriginalPublicTrialPhaseRace.back_head ..]
  · intro i hi
    have eq:t i hi.le=prev i hi (t (i+1) hi):=WilsonOriginalPublicTrialPhaseRace.back_step h top prev i hi
    dsimp only
    rw [eq]
    have step:=(next i hi (t (i+1) hi)).choose_spec
    refine ⟨step,?_⟩
    have bill:=step.matchPay (share S d (b+h) (b+i+1)) (share S d (b+h) (b+i)) 1 (by
      rw [one_mul];exact share_step S d (b+h) (b+i))
    exact bill.cost (mul_le_of_le_one_left (non i) (max_le (paid_share S d _ (by omega)) (paid_share S d _ (by omega))))

end YM.Integration.WilsonOriginalPublicTrialPhaseSpine
end
