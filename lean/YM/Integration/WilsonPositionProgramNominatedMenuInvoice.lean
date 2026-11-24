import YM.Integration.WilsonPositionProgramUniformWindingTable
import YM.Integration.WilsonWindowJointPurchase
import Mathlib.Logic.Encodable.Basic

/-! A single before-period calendar finances every later finite slot
roster at every retained order, on the original normalized history. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 200000
noncomputable section
namespace YM.Integration.WilsonPositionProgramNominatedMenuInvoice
open Function Filter Finset Lattice RG Wilson Laurent Precision
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Mer WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.ScaleS WilsonCoeffUV.Bank.Ticket
open WilsonCoeffUV.Embroider WilsonCoeffUV.Shard
open WilsonMarkedIndependentNormalizedElection (deck normalized)
open WilsonConditionalTaylorSeparatedPurchase (fee)
open WilsonMarkedIndependentNormalizedScale (rate)
open WilsonMarkedIndependentNormalizedHistory (planted)
open WilsonMarkedIndependentMixedStep (Entries)
open WilsonLimitConstruction Next.Foundations PhysicalNext.Repeat.Legato
open scoped Classical BigOperators Topology
variable {G:Gauge}{a:ℕ}


abbrev Request:=Σ a:ℕ, (Fin (a+1)→ℕ) × (Fin (a+1)→ℕ) × ℕ
local instance : Encodable Request:=Encodable.ofCountable Request

def feeR (G:Gauge)(s:Request):Gear G→ℝ:=
  (WilsonMarkedIndependentMixedStep.original (G:=G) s.2.2.1 s.2.1 s.2.1 s.2.2.2).choose

def wallet (G:Gauge)(J:ℕ)(I:Gear G):ℝ:=
  ∑n∈range (J+1), |(Encodable.decode (α:=Request) n).elim 0 (fun s=>feeR G s I)|

theorem price (s:Request)(J:ℕ)(ok:Encodable.encode s≤J)(I:Gear G):
    feeR G s I≤wallet G J I:=by
  let cost(n:ℕ):=|(Encodable.decode (α:=Request) n).elim 0 (fun r=>feeR G r I)|
  have one:=Finset.single_le_sum (f:=cost) (fun n _=>abs_nonneg _) (mem_range.mpr (Nat.lt_succ_of_le ok))
  have atSlot:cost (Encodable.encode s)=|feeR G s I|:=by simp [cost]
  exact (le_abs_self _).trans (atSlot.symm.le.trans one)
def issued (G:Gauge):FundedCompanySelection.Prediction G:=WilsonWindowJointPurchase.Together
    (@FundedMarkedCoverRows.prices G (WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose)
    (@FundedMarkedCoverRows.prices G (wallet G))

theorem prepaid (G:Gauge):WilsonFundedWindowMenu.AllPrices (@issued G):=by
  intro s T
  apply WilsonWindowJointPurchase.joint
  · exact WilsonFundedWindowMenu.from_guard (WilsonFundedWindowCompany.of_prepaid
      (FundedMarkedCoverRows.purchase _ s T))
  · exact WilsonFundedWindowMenu.from_guard (WilsonFundedWindowCompany.of_prepaid
      (FundedMarkedCoverRows.purchase _ s T))

theorem filed (R:Run G)(simple:G.Simple)(readout:RG05Preconstruction.ReadoutPurchase R.b)
    (funded:issued G R.kit)(l d:Fin (a+1)→ℕ)(eligible:∀i,l i<d i)(e:ℕ):
    WilsonMarkedIndependentMixedHistory.Filed R l d eligible e:=by
  let req:Request:=⟨a,l,d,e⟩
  let L:=R.family.path.levels
  let F:=deck (G:=G) l d eligible
  obtain ⟨C,W,roster⟩:=WilsonMarkedIndependentMixedEnrollment.original R simple (wallet G) funded.2 l d eligible e
  obtain ⟨q₀,hq⟩:=eventually_atTop.mp ((WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose_spec R simple readout funded.1 e)
  obtain ⟨w₀,ready⟩:=eventually_atTop.mp ((WilsonMarkedIndependentMixedStep.original (G:=G) d l l e).choose_spec R simple W)
  have grows:Tendsto (fun j:ℕ=>L.clock.J (j+1)) atTop atTop:=L.fits.deep.comp (tendsto_add_atTop_nat 1)
  obtain ⟨g₀,active⟩:=eventually_atTop.mp (grows.eventually_ge_atTop (Encodable.encode req))
  refine ⟨C,W,?_⟩
  filter_upwards [roster,eventually_ge_atTop q₀,eventually_ge_atTop w₀,eventually_ge_atTop g₀] with m raw hqm hwm hgm
  obtain ⟨Q,level,scheme,clock,anchor,cloze,stored,teacher⟩:=raw
  intro X z B
  let U(N:ℕ):=normalized Q.draws Q.paid F X m N
  let P(N:ℕ):=coatA Q.draws Q.paid N m F (U N)
  have source(N:ℕ)(live:m≤N):Borealis Q d l l (P N) m N W z:=teacher X N live
  have bpos:1≤B:=W.purchase ((Q.depth m anchor.le).trans (source m le_rfl).yell)
  refine ⟨bpos,?_⟩
  intro ρ clear N p j mj upto
  have atN:=mj.trans upto
  have chosen:P N=planted R l d eligible X m N:=by dsimp only [P,U,planted];rw [level,scheme]
  let K(i:ℕ):=Gears Q.draws Q.paid l l N N i (P N)
  have march (t:ℕ):∀j:ℕ,m≤j → j+t=N →
      Entries (K j) L.S m j p e ρ B (rate L j p):=by
    induction t with
    | zero=>
      intro j _ stop
      have jN:j=N:=by omega
      subst j
      intro I y _ _ _ i _ r x
      dsimp only [K]
      rw [gearTop]
      have top:=WilsonMarkedIndependentNormalizedTop.original F Q.draws Q.paid N m (U N) y I (R.family.side N p) i r
      change WilsonCoeffUV.Bank.Carp.plume ((P N y I).2 i r) _=(P N y I).1 _ i r at top
      rw [top,sub_self,norm_zero];exact mul_nonneg (pow_nonneg (zero_le_one.trans bpos) _) (Real.exp_pos _).le
    | succ t ih=>
      intro j above stop
      have ca:Q.anchor≤j:=anchor.le.trans above
      have J:=active j (hgm.trans above)
      have receipt:=(stored j above ca).choose_spec.2
      have price:feeR G req (Q.mint j ca).gear≤Q.cash Credit.leanC j:=(price req _ J _).trans receipt
      obtain ⟨_,_,_,_,vac⟩:=hq (j+1) (by omega)
      exact ready j (hwm.trans above) Q ca level scheme clock price m N p above (by omega)
        (P N) z ρ (source N atN) cloze clear (vac N p (by omega)).1 (ih (j+1) (by omega) (by omega))
  have checked:=march (N-j) j mj (by omega)
  dsimp only [K] at checked
  rw [chosen,level,scheme] at checked
  exact checked


theorem original (R:Run G)(simple:G.Simple)(readout:RG05Preconstruction.ReadoutPurchase R.b)
    (funded:issued G R.kit)(l d:Fin (a+1)→ℕ)(h:∀i,l i<d i)(e:ℕ)(U:Credit){δ:ℝ}(hd:0<δ):
    WilsonPositionProgramUniformWindingTable.Complete R l d h e U δ:=by
  let v:ℕ→Gear G→ℝ:=(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose
  apply WilsonPositionProgramUniformWindingTable.original R simple v funded.1 l d h e U
  apply WilsonPositionProgramUniformWindingCapture.original R simple v funded.1 l d h e
    (filed R simple readout funded l d h e) U hd
  filter_upwards [(WilsonVacuumPreResetFiniteHeatHierarchy.original G).choose_spec R simple readout funded.1 e] with m data
  obtain ⟨s,V,hs,hV,row⟩:=data
  exact ⟨s,V,hs,hV,fun N p low=>(row N p low).2⟩

end YM.Integration.WilsonPositionProgramNominatedMenuInvoice
end
