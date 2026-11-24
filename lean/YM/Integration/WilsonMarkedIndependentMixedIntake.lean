import YM.Integration.WilsonMarkedIndependentMixedReporter

/-! On the very same elected Wilson hierarchy, at the reporting date recover
the complete native mixed finite/cover income from all earlier UV births.
This income can be re-entered at any subsequent physical block. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 200000
namespace YM.Integration.WilsonMarkedIndependentMixedIntake
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonMarkedIndependentNormalizedHistory (planted)
open WilsonMarkedIndependentMixedHistory (Filed)
open WilsonMarkedIndependentMixedCompact (clipped)
open WilsonMarkedIndependentPhysicalIntake (PairedAt)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}

def full (R:Run G)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(X:Herit (deck (G:=G) l d h))
    (m N M:ℕ)(ρ:ℝ):Outerm G d:=
  let L:=R.family.path.levels
  clipped M (reserveGood L.S m m ρ (Gears L R.metals.O l l N N m (planted R l d h X m N)))

theorem original (R:Run G)(simple:G.Simple)(v:ℕ→Gear G→ℝ)(funded:FundedMarkedCoverRows.prices v R.kit)
    (l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(filed:Filed R l d h e):
    let F:=deck (G:=G) l d h
    ∀ᶠm:ℕ in atTop,∀X:Herit F,∃ρ₀:ℝ,∀ρ:ℝ,ρ₀≤ρ →
      ∃s A:ℝ,0<s ∧ 1≤A ∧ ∀M:ℕ,
        (∀N,m≤N → Wellness l (full R l d h X m N M ρ)) ∧
        ∀ᶠp:ℕ in atTop,∀N,m≤N → PairedAt e (full R l d h X m N M ρ) (R.family.side m p) s A:=by
  intro F
  let L:=R.family.path.levels
  obtain ⟨C,W,physical⟩:=filed
  obtain ⟨C',W',stock⟩:=WilsonMarkedIndependentMixedEnrollment.original R simple v funded l d h e
  filter_upwards [physical,stock] with m finite real
  obtain ⟨Q,level,ratio,clock,anchor,cloze,store,teacher⟩:=real
  intro X
  let z:=zz L m+∑i,C.buy (zz L m)*fee (F i) (X i) e
  let z':=zz L m+∑i,C'.buy (zz L m)*fee (F i) (X i) e
  let ρ₀:=galeGate G d l l e W Credit.leanC Credit.leanC z
  let ρ₁:=galeGate G d l l e W' Credit.leanC Credit.leanC z'
  let K(N:ℕ):=planted R l d h X m N
  let Y(N:ℕ):=Gears L R.metals.O l l N N m (K N)
  have rule(N)(live:m≤N):Borealis Q d l l (K N) m N W' z':=by
    simpa only [K,planted,level,ratio] using teacher X N live
  have size:0<zz L m:=lt_of_lt_of_le zero_lt_one (clock ▸ Q.depth m anchor.le)
  let σ:=(Q.mint m anchor.le).σ
  obtain ⟨dated,crest,_⟩:=store m le_rfl anchor.le
  have hot:0<σ:=by rw [show σ=crestM L m dated from crest];exact (spatter G _ _ _ _ dated).1
  have cp:1≤W'.buy z':=W'.purchase ((Q.depth m anchor.le).trans (rule m le_rfl).yell)
  have bp:1≤W.buy z:=(finite X).1
  refine ⟨max ρ₀ ρ₁,?_⟩
  intro ρ floor
  have gate:= (le_max_left ρ₀ ρ₁).trans floor
  have cover:= (le_max_right ρ₀ ρ₁).trans floor
  let s:=min (σ/32) (1/(16384*zz L m))
  let A:=WilsonMarkedIndependentMixedReporter.cost G l e σ (W'.buy z') (W.buy z)
  have sig:0<s:=lt_min (by positivity) (by positivity)
  have loaded (N)(live:m≤N):Wellness l (Y N):=by
    have ready:=Cog Q.draws Q.paid (K':=l) le_rfl (K N) (rule N live).head Q.hG Q.green live
    rw [level,ratio] at ready
    exact ready
  have growing:Tendsto (fun p:ℕ=>(R.family.side m p).val) atTop atTop:=
    (show StrictMono (fun p:ℕ=>(R.family.side m p).val) from fun _ _ h=>
      Nat.mul_lt_mul_of_pos_right (R.family.S.period_strict h) (R.family.S.denominator m).pos).tendsto_atTop
  refine ⟨s,A,sig,WilsonMarkedIndependentMixedReporter.add_one G l e σ _ _ (zero_le_one.trans cp) (zero_le_one.trans bp),?_⟩
  intro M
  refine ⟨fun N live=>WilsonMarkedIndependentMixedCompact.healthy M (reserveSpec L.S m m ρ (loaded N live)),?_⟩
  filter_upwards [growing.eventually_ge_atTop (4*(M+12)+1)] with p sits
  intro N live
  have need:=earn_cap (rule N live) cloze cover live
  change ∀q I,shingled q I (reserveGood Q.draws.S m m ρ (Gears Q.draws Q.paid l l N N m (K N))) e σ (W'.buy z') at need
  rw [level,ratio] at need
  exact WilsonMarkedIndependentMixedReporter.paired L.S m p e M (Y N) ρ σ (zz L m) _ _ hot size cp bp
    (loaded N live) need ((finite X).2 ρ gate N p m le_rfl live)
    (by change 4*(M+12)<(R.family.side m p).val;omega)

end YM.Integration.WilsonMarkedIndependentMixedIntake
end
