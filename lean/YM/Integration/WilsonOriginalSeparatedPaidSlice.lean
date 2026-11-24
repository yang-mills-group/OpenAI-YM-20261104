import YM.Integration.WilsonOriginalSeparatedRealHearing
import YM.Integration.WilsonOriginalOccupiedJointEdge

/-! The two literal unnormalized ordinary faces in the dated telescope, divided
by the same measured Wilson vacuum at the earlier field. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonOriginalSeparatedPaidSlice
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
theorem original (capture:WilsonCenteredCaptureClock.first R simple ≤ b)(p:ℕ){tol:ℝ}(positive:0<tol)
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
    (due:∀t ht,(words t ht).price ≤ δ){i:ℕ}(ui:u ≤ i)(ib:i ≤ b)(U:Config G (R.family.side i per))(clear:flags (Ψ i).p.threshold U=∅)
    (row:WilsonOriginalOccupiedWindow.Slice R J (Ψ b))
    (mounted:∀F,row.A.E.log row.x F=(L.join old).log x F)
    (lower:Config G (R.family.side b per)→Poly J)
    (declared:∀F,lower F=((Ψ b).eval F:ℂ) • Poly.pass (bare next z F))
    (rentable:Integrable (fun Y=>((Ψ b).eval Y:ℂ) • Poly.pass ((L.join old).log x Y)) (prior G _))
    (filed:Integrable (fun Y=>((Ψ b).eval Y:ℂ) • Poly.pass (bare next z Y)) (prior G _)):
    let g:=W*rent+W*((Real.exp (a*h))⁻¹*C)+δ
    let e:=change s M g
    let span:=max (fp).B (reach (fp).B h)
    ‖WilsonOriginalOccupiedJointEdge.ordinary R J Ψ (N:=N) ib row lower s U‖ ≤ 
      e+(if i=b then 0 else (2*cost s M)*((s.val.card*(span+span+1)^4:ℕ):ℝ)*(4*Real.exp ((fp).supportExponent+2))*tol/β^p*
        (Real.exp (WilsonOriginalDecoderSpring.bill (R.family.path.levels.clock.op i per)
          (R.family.path.β N per (i+1)) U))^2):=by
  have equalUpper:(fun F=>((Ψ b).eval F:ℂ) • Poly.pass (row.A.E.log row.x F))=
      (fun F=>((Ψ b).eval F:ℂ) • Poly.pass ((L.join old).log x F)):=funext fun F=>by rw [mounted F]
  unfold WilsonOriginalOccupiedJointEdge.ordinary
  rw [equalUpper,funext declared]
  exact WilsonOriginalSeparatedRealHearing.original R π Γ Ψ course cut S A simple way D Q ticket floor ub fixed
    capture p positive late L old next w w' hw hw' width width' paid refund stock other ep cp rp np wp mp dp
    x z s h tube source target amount front mem words due ui ib U clear rentable filed

end YM.Integration.WilsonOriginalSeparatedPaidSlice
end
