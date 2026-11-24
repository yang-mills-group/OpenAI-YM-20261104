import YM.Integration.WilsonOlderFreshConnectedAppointment
import YM.Integration.WilsonOlderFreshConnectedPin
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOlderFreshConnectedReceiver
open Filter Function Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato
open Bloch Wilson Precision Laurent WilsonCoeffUV WilsonCoeffUV.Bank WilsonCoeffUV.Bank.Mosaic
open WilsonCoeffUV.Cosmos WilsonCoeffUV.Cosmos.Polestar WilsonCoeffUV.Blue WilsonCoeffUV.Mer WilsonCoeffUV.Soil
open WilsonCoeffUV.Bank.Realm WilsonCoeffUV.Wheel WilsonCoeffUV.Winding ActualRunAdmissionScales Next.Foundations
open WilsonCoeffUV.Bank.Ticket FormalBulk08 WilsonOriginalCompoundStrip
open scoped Classical BigOperators
universe u
variable {G:Gauge}


open WilsonCoeffUV.Wheel.Flooring WilsonCoeffUV.Wheel.Cadenza Push.PriceCompiler
open FullQLocal FullQLocal.RenderedStep WilsonLimitConstruction QuadraticLocal QuadraticLocal.Advent QuadraticLocal.Mentor AllOrder AllOrder.Floe

open WilsonOlderFreshConnectedBoard
theorem upper (Q:Request G)(R:Run G)(simple:G.Simple)
    
    (ψ:ℕ → ℕ)(i H k e l b:ℕ)(work:1 ≤ k)(enough:H ≤ k+1)
    (grade:e ≤ H)(rank:l ≤ H)(arity:b ≤ H)
    (T:Realm G (e+1) Credit.leanC)(lo:T.anchor ≤ i)(five:5 ≤ R.family.path.levels.clock.J (i+1))
    (crest:(T.mint i lo).σ=crestM R.family.path.levels i five):
    let roots:=WilsonThermometerUnitFilingLease.roots (requested Q) simple (fun _=>MintClock.splits) R.metals.p R.metals.K
    let width:=Poetry.Agenda.seed roots ψ k (R.alloy.B.a.clock.J i)
    0<width ∧ 32*width ≤ VestS b l T i lo:=by
  intro old σ
  let m:=R.alloy.B.a.clock.J i
  let seat:WilsonThermometerUnitFilingLease.Rooms k:=(⟨H,by omega⟩,⟨0,by omega⟩)
  have lease:=WilsonThermometerUnitFilingLease.smaller (requested Q) simple (fun _=>MintClock.splits)
      R.metals.p R.metals.K ψ k m work seat
  dsimp [seat] at lease
  let P:=WilsonThermometerUnitFilingCampus.seated (requested Q) simple (fun _=>MintClock.splits) R.metals.p R.metals.K
  let V:=WilsonOriginalCompoundVertexStrip.narrowed P
  let K:=R.metals.p.kernel
  let x:=R.alloy.B.a.clock.J i
  have weak:width (WilsonThermometerUnitFilingWeakStrip.enrolled V) K x H ≤ width V K x H:=by
    apply min_le_min_left
    exact div_le_div₀ (V.positive ..).le (min_le_left ..) (mul_pos (by norm_num) (V.grows H))
      (mul_le_mul_of_nonneg_left (le_max_right 1 (V.multiplier H)) (by norm_num))
  have seat:width P K x H ≤ width (requested Q) K x H:=by
    apply min_le_min_left
    exact div_le_div_of_nonneg_right (min_le_left ..) (mul_pos (by norm_num) (Q.grows H)).le
  have cash:=lease.trans (weak.trans ((WilsonOriginalCompoundVertexStrip.widths P K x H).1.trans
    (seat.trans (retained Q K x H).2)))
  have h:= (one_slot G R.metals.p.kernel (R.family.path.levels.clock.J i) H).2
    (⟨e,by omega⟩,⟨l,by omega⟩,⟨b,by omega⟩)
  have hh:=FundedPresoldPacketWidths.live R l b whole i T lo five crest
  have kernel:R.family.path.levels.clock.kernel=R.metals.p.kernel:=R.alloy.B.valid.kernel
  rw [kernel] at hh
  change room G R.metals.p.kernel (R.family.path.levels.clock.J i) H
      (⟨e,by omega⟩,⟨l,by omega⟩,⟨b,by omega⟩) ≤ VestS b l T i lo at hh
  refine ⟨Poetry.Agenda.stem ..,?_⟩
  change σ ≤ reserve G R.metals.p.kernel (R.alloy.B.a.clock.J i) H/32 at cash
  have reach:=h.trans hh
  calc
    32*σ=σ*32:=mul_comm .. 
    _ ≤ reserve G R.metals.p.kernel (R.family.path.levels.clock.J i) H:=(le_div_iff₀ (by norm_num:0<(32:ℝ))).1 cash
    _ ≤ _:=reach

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

theorem original (R:Run G)(simple:G.Simple)(P:Request G)
    (income:ℕ → Gear G → ℝ)(wage:FundedMarkedCoverRows.prices income R.kit)
    (n e:ℕ)(D k:Fin n → ℕ)(legal:∀c,k c<D c){δ:ℝ}(pos:0<δ):
    ∀ᶠm:ℕ in atTop,∃ (Q:Realm G (e+1) Credit.leanC),
      Q.draws=R.family.path.levels ∧ Q.paid=R.metals.O ∧ Q.y=zz R.family.path.levels ∧ Q.anchor=m ∧
      Cloze D k Q Credit.leanC ∧ Insure n (mass k univ) Q Credit.leanC ∧
      ∀i,m ≤ i → ∀lo:Q.anchor ≤ i,∃five:5 ≤ R.family.path.levels.clock.J (i+1),
        (Q.mint i lo).σ=crestM R.family.path.levels i five ∧
        ∀(ψ:ℕ → ℕ)(H z:ℕ),1 ≤ z → H ≤ z+1 → 
          e ≤ H → (mass k univ) ≤ H → n ≤ H → 
          let B:=WilsonThermometerUnitFilingLease.roots (requested P) simple (fun _=>MintClock.splits) R.metals.p R.metals.K
          let σ:=Poetry.Agenda.seed B ψ z (R.alloy.B.a.clock.J i)
          0<σ ∧ 32*σ ≤ VestS n (mass k univ) Q i lo ∧ WilsonOlderFreshConnectedAppointment.Paid R Q lo D k δ σ:=by
  obtain ⟨floor,spent⟩:=eventually_atTop.1 (WilsonOlderFreshConnectedAppointment.prices R simple e n D k pos)
  filter_upwards [FundedMarkedCoverRows.realm R simple income wage n k D legal e n (mass k univ),
    eventually_ge_atTop floor] with m sale late
  obtain ⟨Q,calendar,quiet,report,entry,closed,tickets,_club,crest⟩:=sale
  refine ⟨Q,calendar,quiet,report,entry,closed,tickets,?_⟩
  intro i older lo
  obtain ⟨five,actual,_⟩:=crest i older lo
  refine ⟨five,actual,?_⟩
  intro ψ H z work enough grade rank arity B σ
  have width:=upper P R simple ψ i H z e (mass k univ) n work enough grade rank arity Q lo five actual
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


end YM.Integration.WilsonOlderFreshConnectedReceiver
end
