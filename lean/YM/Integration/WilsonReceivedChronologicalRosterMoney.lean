import YM.Integration.WilsonReceivedChronologicalRosterSalary
import YM.Integration.WilsonReceivedChronologicalRosterRanks
import YM.Integration.WilsonOriginalTwoFlatIRSocketRose
import YM.Integration.WilsonOriginalOneArmClearCash

/-! Absorb the fitted selection once on the five genuine physical-ear charges. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedChronologicalRosterMoney
open Filter Finset Lattice Wilson RG Marker PhysicalNext.Repeat.Legato ActualRunAdmissionScales
open OriginalBareMarkedInvoice Pert.Asymptotics
open WilsonReceivedCanonicalVersePortfolio (wallet)
open WilsonReceivedChronologicalFixedReserve (terms)
open scoped BigOperators Classical Topology
variable {G:Gauge}(R:Run G){n:ℕ}
local notation "H" => R.family.path.levels.clock.hatBeta
local notation "zeroFee" => (fun _:Fin n=>(0:ℕ))

def Gate (d:Fin n→ℕ)(A travel pole P promised goal p target:ℕ)(B θ η C α:ℝ)(v:ℕ):Prop:=
  ∀s:(Stock.census (Fin n)).Mode,∀{c K N per:ℕ},0<v→v≤c→c≤N→K≤N→
  R.family.S.scale K-R.family.S.scale (v-1)≤(travel:ℝ)*(1+Real.log (H v))→
    let g:=regulatorRun R.family N per
    let purse:=wallet R d (fun _=>B) s.val*(H K)^(pole*s.val.card)
    let month:=(4*((2*A:ℕ):ℝ)/Real.log 3)*WilsonReceivedChronologicalLastFlat.wage s P 1 θ*g v^promised
    let last:=WilsonOriginalTwoFlatIRSocketPower.ceiling n (terms d zeroFee P).order (∑a,d a) 1
      (Fintype.card (Multi.Hot (Stock.census (Fin n)))) C*g v^goal
    let visit:=WilsonOriginalTwoFlatIRSocketRose.charge R d zeroFee P C α 1 s*g c^p
    let base:=WilsonOriginalOneArmClearCash.wage s P θ*g v^P
    let first:=WilsonReceivedChronologicalLastFlat.wage s P 1 η*g v^P
    purse*(month+last+visit+base+first)≤g v^target ∧ purse*(month+last+base+first)≤g v^target

theorem original (simple:G.Simple)(d:Fin n→ℕ)(A travel pole P promised goal p target:ℕ)(B θ η C α:ℝ)(bp:0≤B)
    (high:target+2+2*pole*n≤P)(dated:target+2+2*pole*n≤promised)(tail:target+2+2*pole*n≤goal)
    (cross:target+2+2*pole*n≤p):∀ᶠ v:ℕ in atTop,Gate R d A travel pole P promised goal p target B θ η C α v:=by
  let ex:Fin 5→ℕ:=![promised,goal,p,P,P]
  let fare:((Stock.census (Fin n)).Mode)→Fin 5→ℝ:=fun s=>
    ![(4*((2*A:ℕ):ℝ)/Real.log 3)*WilsonReceivedChronologicalLastFlat.wage s P 1 θ,
      WilsonOriginalTwoFlatIRSocketPower.ceiling n (terms d zeroFee P).order (∑a,d a) 1
        (Fintype.card (Multi.Hot (Stock.census (Fin n)))) C,
      WilsonOriginalTwoFlatIRSocketRose.charge R d zeroFee P C α 1 s,
      WilsonOriginalOneArmClearCash.wage s P θ,WilsonReceivedChronologicalLastFlat.wage s P 1 η]
  have cost(i:Fin 5):target+2+2*pole*n≤ex i:=by fin_cases i <;> assumption
  filter_upwards [WilsonReceivedChronologicalRosterSalary.original R simple d travel pole target B bp ex cost fare]
    with v earned
  intro s c K N per vp vc cn kn span g purse month last visit base first
  let dates:Fin 5→ℕ:=![v,v,c,v,v]
  have ages(i:Fin 5):v≤dates i ∧ dates i≤N:=by
    fin_cases i <;> simp [dates,vc,cn,vc.trans cn]
  have all:=earned s (per:=per) vp kn span dates ages (Finset.univ:Finset (Fin 5))
  have young:=earned s (per:=per) vp kn span dates ages ({0,1,3,4}:Finset (Fin 5))
  constructor
  · convert all using 1
    simp [g,purse,month,last,visit,base,first,dates,fare,ex,Fin.sum_univ_succ]
    left
    ring
  · convert young using 1
    simp [g,purse,month,last,base,first,dates,fare,ex,Finset.sum_insert]
    left
    ring
end YM.Integration.WilsonReceivedChronologicalRosterMoney
end
