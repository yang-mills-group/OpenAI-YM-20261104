import YM.Integration.WilsonMarkedIndependentMixedScheduledIntake

/-! One winding width and one invoice for every incoming field in the
funded ball. Both are chosen before the physical UV cutoff and period. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramUniformWindingIntake
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Bank.Carp WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket WilsonCoeffUV.Layout
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonMarkedIndependentNormalizedElection (deck)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open WilsonMarkedIndependentNormalizedHistory (planted)
open WilsonMarkedIndependentMixedHistory (Filed)
open WilsonMarkedIndependentMixedIntake (full)
open WilsonMarkedIndependentPhysicalIntake (PairedAt)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(filed:Filed R l d h e)(T:Credit){δ:ℝ}(hd:0<δ):
    let F:=deck (G:=G) l d h
    let L:=R.family.path.levels
    ∀ᶠm:ℕ in atTop,∃s A:ℝ,0<s ∧ 1≤A ∧ ∀(M:ℕ)(ρ:ℝ),δ*longLog L m≤ρ →
      (∀(X:Herit F), (∀i,fee (F i) (X i) e≤T.buy (zz L m)) →
        ∀N,m≤N → Wellness l (full R l d h X m N M ρ)) ∧
      ∀ᶠp:ℕ in atTop,∀(X:Herit F), (∀i,fee (F i) (X i) e≤T.buy (zz L m)) →
        ∀N,m≤N → PairedAt e (full R l d h X m N M ρ) (R.family.side m p) s A:=by
  intro F L
  obtain ⟨C,W,physical⟩:=filed
  obtain ⟨C',W',stock⟩:=WilsonMarkedIndependentMixedEnrollment.original R simple v funded l d h e
  obtain ⟨U,gateU⟩:=WilsonMarkedIndependentMixedOpening.prices (G:=G) d l e C W T
  obtain ⟨U',gateU'⟩:=WilsonMarkedIndependentMixedOpening.prices (G:=G) d l e C' W' T
  filter_upwards [physical,stock,exempt L simple U hd,exempt L simple U' hd] with m finite real outer inner
  obtain ⟨Q,level,ratio,clock,anchor,cloze,store,teacher⟩:=real
  have warm:1≤zz L m:=clock ▸ Q.depth m anchor.le
  let σ:=(Q.mint m anchor.le).σ
  obtain ⟨dated,crest,_⟩:=store m le_rfl anchor.le
  have hot:0<σ:=by rw [show σ=crestM L m dated from crest];exact (spatter G _ _ _ _ dated).1
  let s:=min (σ/32) (1/(16384*zz L m))
  let A:=WilsonMarkedIndependentMixedReporter.cost G l e σ (U'.buy (zz L m)) (U.buy (zz L m))
  have size:0<zz L m:=zero_lt_one.trans_le warm
  have rising:Tendsto (fun p:ℕ=>(R.family.side m p).val) atTop atTop:=
    (show StrictMono (fun p:ℕ=>(R.family.side m p).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator m).pos).tendsto_atTop
  refine ⟨s,A,lt_min (by positivity) (by positivity),
    WilsonMarkedIndependentMixedReporter.add_one G l e σ _ _ (zero_le_one.trans (U'.purchase warm))
      (zero_le_one.trans (U.purchase warm)),?_⟩
  intro M ρ openρ
  have rule (X:Herit F)(N)(top:m≤N):
      Borealis Q d l l (planted R l d h X m N) m N W' (zz L m+∑i,C'.buy (zz L m)*fee (F i) (X i) e):=by
    simpa only [planted,level,ratio] using teacher X N top
  have well (X:Herit F)(N)(top:m≤N): Wellness l (Gears L R.metals.O l l N N m (planted R l d h X m N)):=by
    have law:=Cog Q.draws Q.paid (K':=l) le_rfl (planted R l d h X m N) (rule X N top).head Q.hG Q.green top
    rwa [level,ratio] at law
  refine ⟨fun X _ N top=>WilsonMarkedIndependentMixedCompact.healthy M
    (reserveSpec L.S m m ρ (well X N top)),?_⟩
  filter_upwards [rising.eventually_ge_atTop (4*(M+12)+1)] with p big
  intro X wallet N top
  let z:=zz L m+∑i,C.buy (zz L m)*fee (F i) (X i) e
  let z':=zz L m+∑i,C'.buy (zz L m)*fee (F i) (X i) e
  have fees(i):0≤fee (F i) (X i) e:=(WilsonConditionalTaylorSeparatedPurchase.fee_pos ..).le
  have gate:galeGate G d l l e W Credit.leanC Credit.leanC z≤ρ:=by
    have t:= (gateU (zz L m) _ warm fees wallet).2.trans (outer.trans openρ)
    linarith
  have cover:galeGate G d l l e W' Credit.leanC Credit.leanC z'≤ρ:=by
    have t:= (gateU' (zz L m) _ warm fees wallet).2.trans (inner.trans openρ)
    linarith
  let Y:=Gears L R.metals.O l l N N m (planted R l d h X m N)
  have cp:1≤W'.buy z':=W'.purchase ((Q.depth m anchor.le).trans (rule X m le_rfl).yell)
  have bp:1≤W.buy z:=(finite X).1
  have priced:=earn_cap (rule X N top) cloze cover top
  change ∀q I,shingled q I (reserveGood Q.draws.S m m ρ (Gears Q.draws Q.paid l l N N m (planted R l d h X m N))) e σ (W'.buy z') at priced
  rw [level,ratio] at priced
  have posted:=WilsonMarkedIndependentMixedReporter.paired L.S m p e M Y ρ σ (zz L m) _ _ hot size cp bp
    (well X N top) priced ((finite X).2 ρ gate N p m le_rfl top)
    (by change 4*(M+12)<(R.family.side m p).val;omega)

  have up:W.buy z≤U.buy (zz L m):=(gateU _ _ warm fees wallet).1
  have up':W'.buy z'≤U'.buy (zz L m):=(gateU' _ _ warm fees wallet).1
  apply WilsonMarkedIndependentPhysicalIntake.narrow posted le_rfl
    (zero_le_one.trans (WilsonMarkedIndependentMixedReporter.add_one G l e σ _ _
      (zero_le_one.trans cp) (zero_le_one.trans bp)))
  unfold A WilsonMarkedIndependentMixedReporter.cost
  gcongr

end YM.Integration.WilsonPositionProgramUniformWindingIntake
end
