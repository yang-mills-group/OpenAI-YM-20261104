import YM.Integration.WilsonOlderFreshConnectedEarning
import YM.Integration.WilsonOlderFreshConnectedCurrency
import YM.Integration.WilsonOlderFreshConnectedBoard
import YM.Integration.OriginalRunMarkedPacketPurchase
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedAppointment
open Function Filter Finset MeasureTheory Lattice RG Precision Wilson Tree Exterior
open WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Cosmos
open WilsonCoeffUV.Mer WilsonCoeffUV.Mer.Rolls WilsonCoeffUV.Wheel WilsonCoeffUV.Wheel.Mark
open WilsonCoeffUV.Wheel.Address WilsonCoeffUV.Wheel.Cadenza WilsonCoeffUV.Wheel.Express WilsonCoeffUV.Embroider
open WilsonCoeffUV.Mer.Patrol WilsonCoeffUV.Soil WilsonCoeffUV.Wheel.Flooring
open Work.F08
open scoped BigOperators Classical


open FundedMarkedPathSelection
open PhysicalNext.Repeat.Legato WilsonCoeffUV.Bank.Mosaic WilsonCoeffUV.Embroider.Canvas
open ComparisonDensity.Address WilsonCoeffUV.Shard WilsonCoeffUV.Winding OriginalIssuedMarkedRows
open ActualRunAdmissionScales OriginalBareMarkedInvoice Filter Function
open WilsonOlderFreshConnectedRobe WilsonCoeffUV.Bank.Ticket
open scoped Topology
variable {G:Gauge}{n e m N l b t:ℕ}{A:ℝ}{k D:Fin n   →   ℕ}{S J:Finset (Fin n)}{c:Fin n}


open WilsonOlderFreshConnectedBoard Push.PriceCompiler
variable {I:Type}[Fintype I][DecidableEq I]


open Finset WilsonCoeffUV.Winding WilsonCoeffUV.Cosmos.Polestar WilsonLimitConstruction
open WilsonOlderFreshConnectedCurrency OPE WilsonOriginalCompoundStrip QuadraticLocal QuadraticLocal.Advent

def Paid (R:Run G)(Q:Realm G (e+1) Credit.leanC)(hm:Q.anchor ≤ m)(D k:Fin n → ℕ)(δ σ:ℝ):Prop:=
  ∀(N:ℕ)(S J:Finset (Fin n))(c:Fin n)(A:ℝ)(X:Input Q hm S k D A),J⊆S → c∈J → 0 ≤ A → m<N → 
    let l:=mass k J
    (∀y,Rendered Q hm X J c l N y) ∧ ∀o j,j ≤ e → ∀r:Fin (l+j+1),
      Rooted Q hm X J c l N (32*σ) (R.family.path.levels.clock.hatBeta m^δ*A^J.card) o j r

theorem prices (R:Run G)(simple:G.Simple)(e n:ℕ)(D k:Fin n → ℕ){δ:ℝ}(pos:0<δ):
    ∀ᶠm:ℕ in atTop,∀(J:Finset (Fin n))(c:Fin n),
      (credit G D k J c e (mass k J)).buy (zz R.family.path.levels m) ≤ R.family.path.levels.clock.hatBeta m^δ:=by
  have h:∀s:Finset (Fin n)×Fin n,∀ᶠm:ℕ in atTop,
      (credit G D k s.1 s.2 e (mass k s.1)).buy (zz R.family.path.levels m) ≤ 
        R.family.path.levels.clock.hatBeta m^δ:=fun s=>tariff R simple _ pos
  filter_upwards [eventually_all.mpr h] with m sale J c
  exact sale (J,c)

theorem original (R:Run G)(simple:G.Simple)(P:Request G)
    (lease:WilsonThermometerUnitFilingCampus.Invoice (requested P) simple (fun _=>MintClock.splits) R.kit)
    (income:ℕ → Gear G → ℝ)(wage:FundedMarkedCoverRows.prices income R.kit)
    (n e:ℕ)(D k:Fin n → ℕ)(legal:∀c,k c<D c){δ:ℝ}(pos:0<δ):
    ∀ᶠm:ℕ in atTop,∃ (Q:Realm G (e+1) Credit.leanC),
      Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧
      Cloze D k Q Credit.leanC ∧ Insure n (mass k univ) Q Credit.leanC ∧
      ∀i,m ≤ i → ∀lo:Q.anchor ≤ i,∃five:5 ≤ R.family.path.levels.clock.J (i+1),
        (Q.mint i lo).σ=crestM R.family.path.levels i five ∧
        ∀(ψ:ℕ → ℕ)(H p z:ℕ),H ≤ R.alloy.B.a.clock.J i → 1 ≤ z → H ≤ z+1 → p ≤ R.alloy.B.a.clock.J i+1 → 
          e ≤ H → (mass k univ) ≤ H → n ≤ H → 
          let B:=WilsonThermometerUnitFilingLease.roots (requested P) simple (fun _=>MintClock.splits) R.metals.p R.metals.K
          let σ:=Poetry.Agenda.seed B ψ z (R.alloy.B.a.clock.J (i+1))
          0<σ ∧ 32*σ ≤ VestS n (mass k univ) Q i lo ∧ Paid R Q lo D k δ σ:=by
  obtain ⟨floor,spent⟩:=eventually_atTop.1 (prices R simple e n D k pos)
  filter_upwards [FundedMarkedCoverRows.realm R simple income wage n k D legal e n (mass k univ),
    eventually_ge_atTop floor] with m sale late
  obtain ⟨Q,calendar,quiet,report,entry,closed,tickets,_club,crest⟩:=sale
  refine ⟨Q,calendar,quiet,report,entry,closed,tickets,?_⟩
  intro i older lo
  obtain ⟨five,actual,_⟩:=crest i older lo
  refine ⟨five,actual,?_⟩
  intro ψ H p z fit work enough born grade rank arity B σ
  have width:=anchored P R simple lease ψ i H p z e (mass k univ) n fit work enough born grade rank arity Q lo five actual
  refine ⟨width.1,width.2,?_⟩
  intro N S J c A X sub pin massPos live
  have rows:=WilsonOlderFreshConnectedRobe.original Q lo X sub pin massPos live closed tickets
    (by simpa using Finset.card_le_card (Finset.subset_univ J))
    (by unfold mass;exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ J) (fun i _ _=>Nat.zero_le (k i)))
  refine ⟨rows.1,?_⟩
  intro o j hj r
  have pay:=charged (k:=k) (D:=D) (mass k J) Q lo pin tickets A massPos
  have upper:Q.cash (credit G D k J c e (mass k J)) i ≤ R.family.path.levels.clock.hatBeta i^δ:=by
    simpa only [WilsonCoeffUV.Bank.Realm.cash,report] using spent i (late.trans older) J c
  exact WilsonOlderFreshConnectedEarning.payroll Q lo X (posted _ _ X (rows.2 o j hj r)
    (pay.trans (mul_le_mul_of_nonneg_right upper (pow_nonneg massPos _)))) width.2

end YM.Integration.WilsonOlderFreshConnectedAppointment
end
