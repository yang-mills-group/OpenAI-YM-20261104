import YM.Integration.WilsonCapturedPrimaryWeakTileColumn
import YM.Integration.WilsonOriginalSeparatedDecoder

/-! Full weak column of the original signed two-print posterior. Its regular
and failed-halo invoices are taken at the same registered physical fields. -/
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
noncomputable section
namespace YM.Integration.WilsonCapturedPrimarySeparatedTiles
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm Multi Push.AbsoluteSums.Animals
open WilsonRootedKioskOccupiedSlip WilsonOriginalOrdinaryFlatHulls
open WilsonOriginalSeparatedRegular WilsonOriginalSeparatedMask Comparison.Density.Transport
open WilsonCapturedPrimaryWeakTileColumn RG17 Next.Rank.Spindle
open scoped BigOperators Classical
variable {G:Gauge}(R:Run G){N per m k b:ℕ}(π:ℕ→Layout G)(Γ:ℕ→Pace.Coin)
   (Ψ:∀j,RG.Rep G (R.family.side j per))(course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (cut:b<N){d:ℕ}{F:Frame G d}(S:SectionData F)(A:Hol G)
   (simple:G.Simple)(way:WayStation R.kit)(D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
   (Q:D.Tab R.rolls)(ticket:TicketP R.alloy R.kit D Q){u:ℕ}(floor:m ≤ u)(ub:u ≤ b)
   (fixed:WilsonSingleHardRadius.first R simple ≤ u)
local notation "β" => R.alloy.B.a.clock.hatBeta b
local notation "fp" => (Ψ b).p
local notation "Z" => Site (R.family.side b per)

include course cut way ticket floor ub fixed S A in
theorem original
    (columns:∀ᶠ j in atTop,(R.family.path.levels.params j).columns ≤ R.family.path.levels.clock.hatBeta j)
    (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p:ℕ){tol:ℝ}(positive:0<tol)
    (late:(eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p positive)).choose ≤ b)
    {V X X' ι μ ι':Type}[Fintype V][DecidableEq V][Countable ι][Countable μ][Countable ι']
    {J:Census V}{o o':V→Z}{p':BudgetPoint}
    (L:Lamps X ι G fp o J)(old:Lamps X μ G fp o J)(next:Lamps X' ι' G p' o' J)
    (w w':V→ℝ)(hw:∀a,0<w a)(hw':∀a,0<w' a){a a' E C rent C' W W' M δ:ℝ}
    (width:0 ≤ a)(width':0 ≤ a')(paid:L.Paid w (fp).B a E)(refund:old.Paid w (fp).B a rent)
    (stock:Gross L w (fp).B a C)(other:Gross next w' p'.B a' C')
    (ep:0 ≤ E)(cp:0 ≤ C)(rp:0 ≤ rent)(np:0 ≤ C')(wp:0 ≤ W)(mp:0 ≤ M)(dp:0 ≤ δ)
    (x:X)(z:X')(s:J.Mode)(h:ℕ)(tube:LinkTube G)
    (source:∀t:Hot J,t.val.val⊆s.val→(Poly.toll w t.val)⁻¹ ≤ W)
    (target:∀t:Hot J,t.val.val⊆s.val→(Poly.toll w' t.val)⁻¹ ≤ W')
    (amount:W*(E+rent) ≤ M ∧ W'*C' ≤ M)(front:Hot J→V)(mem:∀t,front t∈t.val.val)
    (words:∀t:Hot J,t.val.val⊆s.val→Row fp tube (o (front t))
      (fun U=>(bare L x U).part t.val) (fun U=>(bare next z U).part t.val))
    (due:∀t ht,(words t ht).price ≤ δ){i:ℕ}(ui:u ≤ i)(ib:i+1 ≤ b)(D₄:ClockFace R 4 i N per)
    (stage:(eventually_atTop.mp ((WilsonCapturedPrimaryWeakTileColumn.four R simple columns).and
      (WilsonOriginalClockFacePosterior.original R simple))).choose ≤ i):
    let soft:=change s M (W*rent+W*((Real.exp (a*h))⁻¹*C)+δ)
    let span:=max (fp).B (reach (fp).B h)
    let failed:=(2*cost s M)*((s.val.card*(span+span+1)^4:ℕ):ℝ)*(4*Real.exp ((fp).supportExponent+2))*tol/β^p
    let earlier:=(Nat.le_succ i).trans ib
    let Y:=actualTransport R.family (N:=N) (defect L old next x z s) earlier
    (∀α,‖Y (node R D₄ α)‖ ≤ soft+2*failed) ∧
    Next.Rank.Spindle.paid R.family 4 i N per (column R D₄ Y) ≤ 44*(R.family.path.levels.clock.hatBeta i)^27*(soft+2*failed):=by
  intro soft span failed earlier Y
  obtain ⟨read,tilt⟩:=(eventually_atTop.mp ((WilsonCapturedPrimaryWeakTileColumn.four R simple columns).and
    (WilsonOriginalClockFacePosterior.original R simple))).choose_spec i stage
  have live:i<N:=(Nat.lt_of_succ_le ib).trans cut
  have pp:0 ≤ β:=zero_le_one.trans ((R.family.path.levels.fits.delayed b).le)
  have fee:0 ≤ failed:=by
    have nc:0 ≤ 2*cost s M:=by dsimp [cost];positivity
    dsimp only [failed]
    positivity
  have bounds (α):‖Y (node R D₄ α)‖ ≤ soft+2*failed:=by
    have atNode:=WilsonOriginalSeparatedDecoder.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
      capture p positive late L old next w w' hw hw' width width' paid refund stock other
      ep cp rp np wp mp dp x z s h tube source target amount front mem words due ui ib (node R D₄ α)
    exact atNode.trans (add_le_add le_rfl ((mul_le_mul_of_nonneg_left (tilt live D₄ α) fee).trans_eq (mul_comm _ _)))
  refine ⟨bounds,?_⟩
  simpa only [sub_zero,column_zero] using read live.le D₄ Y (fun _=>0) (soft+2*failed)
    (fun α=>by simpa only [sub_zero] using bounds α)

end YM.Integration.WilsonCapturedPrimarySeparatedTiles
end
