import YM.Integration.WilsonRootedJointCalendar

/-! Apply the complete high-occurrence bound to the physical signed menu on its
submitted radii. Every finite independent-test roster uses the same Captain. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonRootedSubmittedTail
open Filter Function Lattice Wilson Pressure RG Marker Precision ConnectedActivityE6
open ConnectedActivityE6.Blaze Blaze.March Captain Extra.Multi
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato PhysicalNext.JointLoad
open Heir Heir.Suite Push.PriceCompiler Supply Testing Push.SectorMeasure Push
open IterationFour IterationFour.Vacuum LocalComparison LocalComparison.Global
open FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open QLocalRequestedHeirQuote QLocalRequestedSectorSale QLocalRequestedSectorCalendar
open PhysicalNext.Repeat.Opera PhysicalNext.Repeat.Daisy MergeProof LocalLTE
open RGLocalTaylor RGLocalTaylor.Laminate
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
    {R : Run G} {J : Request V} {A : NumericSchedule R.family J}
    {d : LocalFormal.Datum R.family Γ} {F : AnalyticInput J A d} {η : ℝ}
    (I : FullPreparedInputAt F η)
abbrev CashAt (book : Booking G) :=
  let lev := R.alloy.B.a
  let g := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  let Q := R.kit.target (lev.clock.J (d.level+1)) (lev.clock.J d.level)
  let Y := QLocalInheritedRegularSlots.carrier (ManuscriptQLocalVacuumFamily.source
    (QLocalInheritedPhysicalInlet.rep I) F.layers g 1)
  Cash book.W (lev.clock.hatBeta d.level) book.μ (lev.clock.op d.level d.period).patch.L
    (target J Q) book.order book.c (ships R.alloy.B d.cutoff d.level d.period) Y

variable {book : Booking G} (H : CashAt I book)

def Submitted (price : ℝ) : Prop :=
  let lev := R.alloy.B.a
  let Q := R.kit.target (lev.clock.J (d.level+1)) (lev.clock.J d.level)
  let S := lev.clock.op d.level d.period
  let β := lev.clock.hatBeta d.level
  ∃ a b C' d' rv s z B e q : ℝ, ∃ k : ℕ,
    ∃ N : Captain H J.outputFieldOrder C' d' rv s a b z B e k Chi.canonical,
      ManuscriptQLocalHeightPaidRows.Ready J.outputFieldOrder d' B k ∧
      HostQ H N.conduit a B k ∧ Bikes (target J Q) S.patch.L book.μ β
        (expense J Q).earn q B J.outputFieldOrder k ∧
      ∀ (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
        let M := (ManuscriptQLocalMarkedRoster.promised
          (ManuscriptQLocalMarkedHeightRun.rosterBudget I) base x E K).terms
        Ac.Hit (fun z : Fan.Stars H (fun i => (M i).M) => Captain.reachability z.1) (radiusB β)
          (fun z => if Height.tiredN H (ManuscriptQLocalMarkedHeightRun.length J) z.1 then
            Poly.price F.inputRadii (ManuscriptQLocalMarkedHeightTail.matrix H M z) *
              Captain.wife N z.1 (fun i => (M i).M) z.2 J.outputDistanceOrder else 0)
          (expense J Q).earn price

theorem accepted {price : ℝ} (high : ManuscriptQLocalMarkedHeightRun.High (expense J (R.kit.target (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))) H J Γ price)
    (reserve : (Fintype.card V : ℝ) * ManuscriptQLocalMarkedHeightRun.rosterBill I ≤
      betaF G (R.alloy.B.a.clock.hatBeta d.level) (R.alloy.B.a.clock.op d.level d.period).patch.L) : Submitted I H price := by
  obtain ⟨a,b,C',d',rv,s,z,B,e,q,k,N,ready,host,bikes,_,tested⟩ := high
  refine ⟨a,b,C',d',rv,s,z,B,e,q,k,N,ready,host,bikes,?_⟩
  intro base x E K
  exact (tested _ _ F.fineRoots F.inputRadii (ManuscriptQLocalMarkedHeightRun.rosterBill I)
    (ManuscriptQLocalMarkedHeightRun.rosterBudget I).radii
    (ManuscriptQLocalMarkedHeightRun.enrolled I base x E K) reserve).2

variable (R J A) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (WilsonRootedJointCalendar.scheme G J) extra γ R.kit)

theorem measured (hG : G.Simple) :
    ∀ᶠ m in (atTop : Filter ℕ), ∀ (d : LocalFormal.Datum R.family Γ), d.level=m →
    ∀ (F : AnalyticInput J A d) {η : ℝ} (I : FullPreparedInputAt F η), Retained.NativeIntake I →
    let lev := R.alloy.B.a
    let i := lev.clock.J d.level
    let j := lev.clock.J (d.level+1)
    let book := paid.choose j i
    let g := Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
    let Y := QLocalInheritedRegularSlots.carrier (ManuscriptQLocalVacuumFamily.source
      (QLocalInheritedPhysicalInlet.rep I) F.layers g 1)
    let S := lev.clock.op d.level d.period
    let Q := R.kit.target j i
    ∃ H : Cash book.W (lev.clock.hatBeta d.level) book.μ S.patch.L (target J Q) book.order book.c
          (ships R.alloy.B d.cutoff d.level d.period) Y,
      Submitted I H ((2*g)^(J.order+1)) ∧
      (∀ M ≤ S.patch.J, ∃ a : ℝ, Laminate.Known H (toll J) a 1 (Height.asset (expense J Q))
        J.outputFieldOrder J.outputDistanceOrder M) ∧
      ∀ (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
        QLocalMarkedSourceCalendar.Priced (ManuscriptQLocalMarkedHeightRun.rosterBudget I) H base x E K := by
  filter_upwards [WilsonRootedJointCalendar.issued (Γ:=Γ) R A extra γ paid hG] with m issued d hm F η I hi
  obtain ⟨H,_,_,h,low,phases,_,reserve⟩ := issued d hm F I hi
  exact ⟨H,accepted I H h reserve,low,phases⟩

end YM.Integration.WilsonRootedSubmittedTail
end
