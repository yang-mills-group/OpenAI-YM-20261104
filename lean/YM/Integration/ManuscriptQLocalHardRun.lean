import YM.Integration.ManuscriptQLocalHardDisk
import YM.Integration.ManuscriptQLocalMarkedHeightRun

/-! Same-run, preselected hard disk with all independent offers, original roots,
the complete signed physical matrix, and the native integrated derivative costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.ManuscriptQLocalHardRun
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

def Purchased (J:Request V) (Γ:Marker.Census V) (ρ:ℝ) : Prop :=
  ∃A b C' d rv s z B e q:ℝ,∃k:ℕ,∃N:Captain H J.outputFieldOrder C' d rv s A b z B e k Chi.canonical,
    ManuscriptQLocalHeightPaidRows.Ready J.outputFieldOrder d B k ∧
    HostQ H N.conduit A B k ∧ Bikes Q L μ x E.earn q B J.outputFieldOrder k ∧
    ∀(ι:Type)[Fintype ι] (M:ι→Menu.Hat Γ Y) (origin:V→Site f) (w:V→ℝ) (b':ℝ),
    (∀v,0<w v) → Menu.Offer origin M w Y.p.B Y.p.supportExponent b' →
    (Fintype.card V:ℝ)*b'≤betaF G x L →
    ∀degree:Fan.Stars H (fun i=>(M i).M)→ℕ,
    (∀z,ManuscriptQLocalForcedClusters.alive H Chi.canonical (fun i=>(M i).M) z→
      ManuscriptQLocalExceptionalCounts.Invoice H (ManuscriptQLocalMarkedHeightRun.length J) z.1 (degree z)) →
    Ac.Hit (fun z:Fan.Stars H (fun i=>(M i).M)=>Captain.reachability z.1) (radiusB x)
      (fun z=>if 0<degree z ∧ ManuscriptQLocalForcedClusters.alive H Chi.canonical (fun i=>(M i).M) z then
        ρ^((J.order+1)*degree z)*(Poly.price w (ManuscriptQLocalMarkedHeightTail.matrix H M z)*
          Captain.wife N z.1 (fun i=>(M i).M) z.2 J.outputDistanceOrder) else 0) E.earn 1

theorem funded (J:Request V) (Γ:Marker.Census V) {price ρ:ℝ} (hρ:0≤ρ)
    (circle:ρ^(J.order+1)*price≤1) (high:ManuscriptQLocalMarkedHeightRun.High E H J Γ price) :
    Purchased E H J Γ ρ := by
  obtain ⟨A,b,C,d,rv,s,z,B,e,q,k,N,ready,host,bikes,window,buyer⟩ := high
  refine ⟨A,b,C,d,rv,s,z,B,e,q,k,N,ready,host,bikes,?_⟩
  intro ι instanceF M origin w bill hw offer budget degree locate
  have hg:1≤Height.grow G L x:=Real.one_le_rpow window.1 (by norm_num)
  have cap:=ManuscriptQLocalHardDisk.birthday (pow_pos (zero_lt_one.trans_le hg) _) hρ
    (Fintype.card V) (J.order+1) window.2.2.2 circle
  exact ManuscriptQLocalHardDisk.financed H M N J.outputDistanceOrder
    (ManuscriptQLocalMarkedHeightRun.length J) (J.order+1) w hw window.1 hρ cap degree
    (fun z live=>ManuscriptQLocalHardDisk.aggregate H (ManuscriptQLocalMarkedHeightRun.length J)
      window.1 window.2.1 window.2.2.1 z.1 (locate z live)) (buyer ι M origin w bill hw offer budget).1

theorem physical (J:Request V) (Γ:Marker.Census V) {g:ℝ} (hg:0<g)
    (high:ManuscriptQLocalMarkedHeightRun.High E H J Γ ((2*g)^(J.order+1))) :
    Purchased E H J Γ (2*g)⁻¹ :=
  funded E H J Γ (inv_nonneg.mpr (mul_nonneg (by norm_num) hg.le))
    (ManuscriptQLocalHardDisk.physical_radius hg _) high

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
          Purchased (expense J (R.kit.target j i)) H J Γ (2*g)⁻¹ ∧
          (∀(a x:IndependentTests J.tests) (E:Finset ℕ) (K:Finset (ℕ×ℕ)),
            Menu.Offer F.fineRoots (ManuscriptQLocalMarkedRoster.promised (rosterBudget I) a x E K).terms
              F.inputRadii Y.p.B Y.p.supportExponent (rosterBill I)) ∧
          (Fintype.card V:ℝ)*rosterBill I≤betaF G (lev.clock.hatBeta d.level) (lev.clock.op d.level d.period).patch.L := by
  filter_upwards [ManuscriptQLocalMarkedHeightRun.issued (Γ:=Γ) R A extra γ paid hG] with m source d hm F η I hi
  obtain ⟨H,renewed,crossed,sold,full,fee⟩ := source d hm F I hi
  have hg := IterationFour.Currency.g_pos R.makes d.cutoff d.period (d.level+1) d.below
  exact ⟨H,renewed,crossed,physical _ H J Γ hg sold,full,fee⟩

end Original
end YM.Integration.ManuscriptQLocalHardRun
