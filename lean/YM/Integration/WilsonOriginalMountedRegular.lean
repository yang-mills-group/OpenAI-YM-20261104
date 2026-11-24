import YM.Integration.WilsonOriginalSeparatedPaidSlice
import YM.Integration.WilsonOriginalFiledBochner

/-! The two compact prints, accounts and mounted identities at one actual numerical slice. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalMountedRegular
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm Multi Push.AbsoluteSums.Animals
open WilsonRootedKioskOccupiedSlip WilsonOriginalOrdinaryFlatHulls
open WilsonOriginalSeparatedRegular WilsonOriginalSeparatedMask Comparison.Density.Transport
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){i per:ℕ}{V:Type}[Fintype V][DecidableEq V]
    {J:Census V}(vac:RG.Rep G (R.family.side i per))

structure Filing (row:WilsonOriginalOccupiedWindow.Slice R J vac)(lower:Config G (R.family.side i per) → Poly J)(s:J.Mode) where
  X : Type
  X' : Type
  I : Type
  Iold : Type
  I' : Type
  [count : Countable I]
  [countOld : Countable Iold]
  [countNext : Countable I']
  o : V→Site (R.family.side i per)
  o' : V→Site (R.family.side i per)
  nextBudget : BudgetPoint
  L : Lamps X I G vac.p o J
  old : Lamps X Iold G vac.p o J
  next : Lamps X' I' G nextBudget o' J
  x : X
  z : X'
  mounted : ∀U,row.A.E.log row.x U=(L.join old).log x U
  declared : ∀U,lower U=(vac.eval U:ℂ) • Poly.pass (bare next z U)
  w : V→ℝ
  w' : V→ℝ
  hw : ∀a,0<w a
  hw' : ∀a,0<w' a
  α : ℝ
  α' : ℝ
  regular : ℝ
  gross : ℝ
  rent : ℝ
  nextGross : ℝ
  width : 0 ≤ α
  nextWidth : 0 ≤ α'
  paid : L.Paid w vac.p.B α regular
  refund : old.Paid w vac.p.B α rent
  stock : Gross L w vac.p.B α gross
  other : Gross next w' nextBudget.B α' nextGross
  regular_nn : 0 ≤ regular
  gross_nn : 0 ≤ gross
  rent_nn : 0 ≤ rent
  other_nn : 0 ≤ nextGross
  W : ℝ
  W' : ℝ
  M : ℝ
  δ : ℝ
  wallet_nn : 0 ≤ W
  M_nn : 0 ≤ M
  delta_nn : 0 ≤ δ
  source : ∀t:Hot J,t.val.val⊆s.val→(Poly.toll w t.val)⁻¹ ≤ W
  target : ∀t:Hot J,t.val.val⊆s.val→(Poly.toll w' t.val)⁻¹ ≤ W'
  amount : W*(regular+rent) ≤ M ∧ W'*nextGross ≤ M
  h : ℕ
  tube : LinkTube G
  front : Hot J→V
  mem : ∀t,front t∈t.val.val
  words : ∀t:Hot J,t.val.val⊆s.val→Row vac.p tube (o (front t))
    (fun U=>(bare L x U).part t.val) (fun U=>(bare next z U).part t.val)
  due : ∀t ht,(words t ht).price ≤ δ

variable {R vac}

def Filing.bill {row:WilsonOriginalOccupiedWindow.Slice R J vac}
    {targetField:Config G (R.family.side i per) → Poly J}{s:J.Mode}(F:Filing R vac row targetField s)(base:ℕ)(tol β spring:ℝ)(p:ℕ):ℝ:=
  let g:=F.W*F.rent+F.W*((Real.exp (F.α*F.h))⁻¹*F.gross)+F.δ
  let span:=max vac.p.B (reach vac.p.B F.h)
  WilsonOriginalOrdinaryFlatHulls.change s F.M g+(if base=i then 0 else (2*cost s F.M)*((s.val.card*(span+span+1)^4:ℕ):ℝ)*
    (4*Real.exp (vac.p.supportExponent+2))*tol/β^p*(Real.exp spring)^2)


variable {N m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)(Ψ:∀j,RG.Rep G (R.family.side j per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ){d:ℕ}{frame:Frame G d}
    (section_:SectionData frame)(group:Hol G)(simple:G.Simple)(way:WayStation R.kit)
    (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)(Q:D.Tab R.rolls)
    (ticket:TicketP R.alloy R.kit D Q)

include course section_ group way ticket in
theorem Filing.original (mb:m ≤ b)(bi:b ≤ i)(cut:i<N)(fixed:WilsonSingleHardRadius.first R simple ≤ b)
    (capture:WilsonCenteredCaptureClock.first R simple ≤ i)(p:ℕ){tol:ℝ}(tp:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose ≤ i)
    {P:WilsonOriginalOccupiedWindow.Slice R J (Ψ i)}{Y:Config G (R.family.side i per) → Poly J}{s:J.Mode}
    (F:Filing R (Ψ i) P Y s)(U:Config G (R.family.side b per))(clear:flags (Ψ b).p.threshold U=∅):
    ‖WilsonOriginalOccupiedJointEdge.ordinary R J Ψ (N:=N) bi P Y s U‖ ≤
      F.bill b tol (R.alloy.B.a.clock.hatBeta i)
        (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op b per)
          (R.family.path.β N per (b+1)) U) p:=by
  letI := F.count
  letI := F.countOld
  letI := F.countNext
  obtain ⟨rentable,filed⟩:=WilsonOriginalFiledBochner.original R course (mb.trans bi) cut.le
    F.L F.old F.next F.hw F.hw' F.width F.nextWidth F.paid F.refund F.other F.x F.z
  exact WilsonOriginalSeparatedPaidSlice.original R π Γ Ψ course cut section_ group simple way D Q ticket
    mb bi fixed capture p tp late F.L F.old F.next F.w F.w' F.hw F.hw' F.width F.nextWidth
    F.paid F.refund F.stock F.other F.regular_nn F.gross_nn F.rent_nn F.other_nn F.wallet_nn F.M_nn F.delta_nn
    F.x F.z s F.h F.tube F.source F.target F.amount F.front F.mem F.words F.due le_rfl bi U clear
    P F.mounted Y F.declared rentable filed

end YM.Integration.WilsonOriginalMountedRegular
end
