import YM.Integration.ManuscriptQLocalHardRun
import YM.Integration.ManuscriptQLocalHardGraded

/-! Genuine joint marked hard and ordinary degree purchase on the original
issued conditional law, at every stated cutoff, datum and independent offer. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalHardConditional
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy
open MergeProof LocalLTE
open scoped Topology BigOperators Classical


variable {G:Gauge} {V:Type} [DecidableEq V] [Fintype V] {Γ:Marker.Census V}
variable {c f L:Side} {S:StepData c f} {T:Tube G S} {Y:Rep G f}
  {P:Teller G} {Q:ConnectedActivityE6.Target G P} {W b μ x:ℝ} {o:Target.Order G W}
  (E:Q.Expense) (H:Cash W x μ L Q o b T Y)

def Joint (J:Request V) (Γ:Marker.Census V) (g:ℝ) : Prop :=
  ∃A b C' d rv s z B e q:ℝ,∃k:ℕ,∃N:Captain H J.outputFieldOrder C' d rv s A b z B e k Chi.canonical,
    ManuscriptQLocalHeightPaidRows.Ready J.outputFieldOrder d B k ∧
    HostQ H N.conduit A B k ∧ Bikes Q L μ x E.earn q B J.outputFieldOrder k ∧
    ∀(ι:Type)[Fintype ι] (M:ι→Menu.Hat Γ Y) (ν:ι→ℕ) (origin:V→Site f) (w:V→ℝ) (b':ℝ),
    (∀v,0<w v) → Menu.Offer origin (fun i=>Menu.gradedHat (M i) (2*g)⁻¹ (ν i)) w Y.p.B Y.p.supportExponent b' →
    (Fintype.card V:ℝ)*b'≤betaF G x L →
    ∀degree:Fan.Stars H (fun i=>(M i).M)→ℕ,
    (∀z,ManuscriptQLocalForcedClusters.alive H Chi.canonical (fun i=>(M i).M) z→
      ManuscriptQLocalExceptionalCounts.Invoice H (ManuscriptQLocalMarkedHeightRun.length J) z.1 (degree z)) →
    (∀ζ:ℂ,‖ζ‖≤(2*g)⁻¹ →
      Ac.Hit (fun z:Fan.Stars H (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB x)
        (fun z=>if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H Chi.canonical (fun i=>(M i).M) z then
          Poly.price w (ManuscriptQLocalHardGraded.term H M ν degree (J.order+1) ζ z)*
            Captain.wife N z.1 (fun i=>(M i).M) z.2 J.outputDistanceOrder else 0) E.earn 1) ∧
    ∀cut:ℕ,Ac.Hit (fun z:Fan.Stars H (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if cut≤ManuscriptQLocalHardGraded.total H M ν degree (J.order+1) z then
        (if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H Chi.canonical (fun i=>(M i).M) z then
          Poly.price w (ManuscriptQLocalMarkedHeightTail.matrix H M z)*
            Captain.wife N z.1 (fun i=>(M i).M) z.2 J.outputDistanceOrder else 0) else 0)
        E.earn ((2*g)^cut)

/-- This spends only the original offered vertices enlarged on their own source
grades. The full input gas can always use grade zero on its individual slots. -/
theorem purchased (J:Request V) (Γ:Marker.Census V) {g:ℝ} (hg:0<g) (half:2*g≤1)
    (fund:ManuscriptQLocalHardRun.Purchased E H J Γ (2*g)⁻¹) : Joint E H J Γ g := by
  obtain ⟨A,b,C,d,rv,s,z,B,e,q,k,N,ready,host,bikes,buy⟩ := fund
  refine ⟨A,b,C,d,rv,s,z,B,e,q,k,N,ready,host,bikes,?_⟩
  intro ι instanceF M ν origin w bill hw offer cap degree locate
  have hρ:1≤(2*g)⁻¹:=(one_le_inv₀ (mul_pos (by norm_num) hg)).mpr half
  have bought:=buy ι (fun i=>Menu.gradedHat (M i) (2*g)⁻¹ (ν i)) origin w bill hw offer cap degree locate
  refine ⟨fun ζ hz=>ManuscriptQLocalHardGraded.circle_price H M ν N w hw (zero_le_one.trans hρ)
    (J.order+1) J.outputDistanceOrder degree bought ζ hz,fun cut=>?_⟩
  simpa only [inv_pow,inv_inv,mul_one] using ManuscriptQLocalHardGraded.purchased_tail H M ν N w hw hρ
    (J.order+1) J.outputDistanceOrder degree bought cut

section Original
open ManuscriptQLocalMarkedHeightRun
variable (R:Run G) {J:Request V} (A:NumericSchedule R.family J)
  (extra:Stage→ℕ→ℝ) (γ:ℝ) (paid:QLocalRequestedSectorCalendar.Paid J (acquisition G J) extra γ R.kit)

/-- The genuine funded input chooses one full hard-component radius for every
cutoff, independent mark roster and measured original input after one stage. -/
theorem issued (hG:G.Simple) :
    ∀ᶠ m in (atTop:Filter ℕ),∀(d:LocalFormal.Datum R.family Γ),d.level=m →
      ∀(F:AnalyticInput J A d) {η:ℝ} (I:FullPreparedInputAt F η),Retained.NativeIntake I →
      let lev:=R.alloy.B.a
      let i:=lev.clock.J d.level
      let j:=lev.clock.J (d.level+1)
      let book:=paid.choose j i
      let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
      let Y:=QLocalInheritedRegularSlots.carrier (ManuscriptQLocalVacuumFamily.source
        (QLocalInheritedPhysicalInlet.rep I) F.layers g 1)
      ∃H:Cash book.W (lev.clock.hatBeta d.level) book.μ (lev.clock.op d.level d.period).patch.L
        (target J (R.kit.target j i)) book.order book.c (ships R.alloy.B d.cutoff d.level d.period) Y,
        Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
          Crossed J γ R A d book H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
          Joint (expense J (R.kit.target j i)) H J Γ g ∧
          (∀(a x:IndependentTests J.tests) (E:Finset ℕ) (K:Finset (ℕ×ℕ)),
            Menu.Offer F.fineRoots (ManuscriptQLocalMarkedRoster.promised (rosterBudget I) a x E K).terms
              F.inputRadii Y.p.B Y.p.supportExponent (rosterBill I)) ∧
          (Fintype.card V:ℝ)*rosterBill I≤betaF G (lev.clock.hatBeta d.level) (lev.clock.op d.level d.period).patch.L := by
  filter_upwards [ManuscriptQLocalHardRun.issued (Γ:=Γ) R A extra γ paid hG,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small hG R.makes (1/2) (by norm_num))]
    with m source small d hm F η I hi
  subst m
  obtain ⟨H,renewed,crossed,sold,full,fee⟩ := source d rfl F I hi
  have hg := IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  have hsmall := small d.cutoff d.period d.below
  change Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)<(1/2:ℝ) at hsmall
  exact ⟨H,renewed,crossed,purchased _ H J Γ hg (by linarith only [hsmall]) sold,full,fee⟩

end Original
end YM.Integration.ManuscriptQLocalHardConditional
