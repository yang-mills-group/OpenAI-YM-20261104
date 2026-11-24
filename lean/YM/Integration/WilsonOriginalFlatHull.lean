import YM.Integration.WilsonOriginalFlatHaloRate
import YM.Comparison.Density.Mirrors.Anchor

/-! Read the cropped difference of two genuine group functions at the native
Wilson threshold. Rank zero only needs the scalar transport at an axial cut,
independently of the number of derivatives bought for other purposes. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonOriginalFlatHull
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm
open scoped BigOperators Classical


open Comparison.Density Comparison.Density.Transport Comparison.Density.Mirrors
open AnalyticBridge.SectorAffine.Offset
open scoped ContDiff Matrix.Norms.Frobenius
open private YM.Comparison.Density.Mirrors.Anchor.cut YM.Comparison.Density.Mirrors.Anchor.cut_to
  YM.Comparison.Density.Mirrors.Anchor.cut_reads from YM.Comparison.Density.Mirrors.Anchor

/-- A rooted angular receipt on the two actual group words and their actual path tail.
The small numbers in the low rows may include a winding discrepancy. -/
structure Crop {G:Gauge}{n:Side}(B:BudgetPoint)(L:LinkTube G)(o:Site n)
    (f h tail:Config G n→ℂ)(s m:ℕ)(w jets high tailJet tailValue:ℝ):Prop where
  radius : ∃k<B.B,LocalOn (neighborhood k o) (f-h-tail)
  ward : GaugeInvariant (f-h-tail)
  room : Room B n L B.B w
  order : s ≤ m
  salary : ∀A:Directions G n,‖A‖≤w → Through m ((f-h-tail) ∘ increment 1) A high
  smooth : ContDiffAt ℝ m ((f-h) ∘ increment 1) 0
  low : ∀i<s,‖iteratedFDeriv ℝ i ((f-h) ∘ increment 1) 0‖≤jets
  long : Through m (tail ∘ increment 1) 0 tailJet
  outside : ∀U,‖tail U‖≤tailValue
  nonnegative : 0≤jets

theorem healthy {G:Gauge}{n:Side}{B:BudgetPoint}{L:LinkTube G}{o:Site n}
    {f h tail:Config G n→ℂ}{s m:ℕ}{w jets high tailJet tailValue:ℝ}
    (c:Crop B L o f h tail s m w jets high tailJet tailValue)(U:Config G n)
    (clear:Healthy B.threshold (halo B.B {o}) U):
    ‖f U-h U‖≤groupPrice L 0*((s:ℝ)*(jets+tailJet)+high*w^s)+tailValue:=by
  obtain ⟨k,hk,locality⟩:=c.radius
  let X:=neighborhood k o
  obtain ⟨z,core,logPrice⟩:=YM.Comparison.Density.Mirrors.Anchor.cut_to B L U (Finset.Subset.refl X) clear hk c.room
  have atzero (i:ℕ)(lt:i<s):‖iteratedFDeriv ℝ i ((f-h-tail) ∘ increment 1) 0‖≤jets+tailJet:=by
    have le : i ≤ m :=lt.le.trans c.order
    change ‖iteratedFDeriv ℝ i (((f-h) ∘ increment 1)-(tail ∘ increment 1)) 0‖≤_
    rw [iteratedFDeriv_sub_apply (c.smooth.of_le (mod_cast le)) (through_le c.long le).smooth]
    exact (norm_sub_le ..).trans (add_le_add (c.low i lt) (c.long.pay i le))
  have hw:0<w:=B.threshold_pos.trans_le c.room.budget
  have nonneg:0≤high:=(c.salary 0 (by simpa only [norm_zero] using hw.le)).nonneg
  have pt:=transport (f-h-tail) L w (YM.Comparison.Density.Mirrors.Anchor.cut X z U) core hw c.room.small logPrice
    m 0 s high (jets+tailJet) c.order (Nat.zero_le _) nonneg (add_nonneg c.nonnegative c.long.nonneg)
    c.salary atzero [] (Nat.zero_le _) (by simp)
  change ‖(f-h-tail) (YM.Comparison.Density.Mirrors.Anchor.cut X z U)‖≤_ at pt
  rw [YM.Comparison.Density.Mirrors.Anchor.cut_reads (f-h-tail) X z U locality c.ward] at pt
  calc
    _=‖(f-h-tail) U+tail U‖:=by simp
    _≤_ := (norm_add_le ..).trans (add_le_add pt (c.outside U))

variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "κ" => LocalComparison.forcedDivisor R.family b
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "Space" => Config G (R.family.side b per)



include course cut way ticket floor ub fixed S A in
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p d₀:ℕ){tol:ℝ}(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple (p+d₀) positive)).choose ≤ b)
    {α:ℝ}(strength:(Ψ b).p.supportExponent≤α)(L:LinkTube G)(o:Site (R.family.side b per))
    (f h tail:Space→ℂ)(borel:Measurable (f-h)){s m':ℕ}{w jets high tailJet tailValue:ℝ}
    (c:Crop (Ψ b).p L o f h tail s m' w jets high tailJet tailValue)
    {B:ℝ}(bp:0≤B)(gross:∀U,‖f U-h U‖≤B*β^d₀){i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b):
    ‖actualTransport R.family (N:=N) (f-h) ((Nat.le_succ i).trans ib) 1‖≤
      groupPrice L 0*((s:ℝ)*(jets+tailJet)+high*w^s)+tailValue+B*(4*Real.exp (α+2))*tol/β^p:=by
  have ep:0≤groupPrice L 0*((s:ℝ)*(jets+tailJet)+high*w^s)+tailValue:=
    (norm_nonneg (f 1-h 1)).trans (healthy c 1 (by
      unfold Healthy;rw [Progress.DirectedRecipe.no_flags (Ψ b).p.threshold_pos.le];simp))
  have pay:=WilsonOriginalFlatHaloRate.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture p d₀ positive late {o} id strength (f-h) borel ep bp gross
    (fun U clear=>healthy c U (clear o (Finset.mem_singleton_self _))) ui ib
  simpa only [Finset.card_singleton,Nat.cast_one,mul_one] using pay

end YM.Integration.WilsonOriginalFlatHull
end

