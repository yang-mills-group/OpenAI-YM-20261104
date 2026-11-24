import YM.Integration.WilsonGaussianDeterminantCash

/-! The single physical reporting conductor meeting the high, laminate, and
incoming marked-source obligations, the packed connected word and the Gaussian determinant for every finite order, and any further original physical chart prescription on that very same H and booking. -/
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonGaussianDeterminantTender
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

open RGLocalTaylor RGLocalTaylor.Laminate

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}

universe u

def joined (G : Gauge) {V : Type} [Fintype V] [DecidableEq V] (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G) :=
  (WilsonReportingDecoratedStage.joined G J χ).paired ((WilsonGaussianDeterminantStage.decal G χ).paired δ)

def On {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] (R : Run G)
    (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (joined G J χ δ)
      extra γ R.kit) : Prop := ∀ {Γ : Census V} (A : NumericSchedule R.family J),
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
      let β := lev.clock.hatBeta d.level
      let Q := R.kit.target j i
      ∃ H : Cash book.W β book.μ S.patch.L (target J Q) book.order book.c
            (ships R.alloy.B d.cutoff d.level d.period) Y,
        Cash.Renewed J.outputFieldOrder (toll J) 1 1 H ∧
        Crossed J γ R A d book H (I.inherited+ManuscriptQLocalVacuumRadius.bill F.vacuum.packets g 1) ∧
        ManuscriptQLocalMarkedHeightRun.High (expense J Q) H J Γ ((2*g)^(J.order+1)) ∧
        (∀ M ≤ S.patch.J, ∃ a : ℝ, Laminate.Known H (toll J) a 1 (Height.asset (expense J Q))
          J.outputFieldOrder J.outputDistanceOrder M) ∧
        (∀ (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
          QLocalMarkedSourceCalendar.Priced (ManuscriptQLocalMarkedHeightRun.rosterBudget I) H base x E K) ∧
        (∀ (base x : IndependentTests J.tests) (E : Finset ℕ) (K : Finset (ℕ×ℕ)),
          Menu.Offer F.fineRoots (ManuscriptQLocalMarkedRoster.promised
            (ManuscriptQLocalMarkedHeightRun.rosterBudget I) base x E K).terms
            F.inputRadii Y.p.B Y.p.supportExponent (ManuscriptQLocalMarkedHeightRun.rosterBill I)) ∧
        (Fintype.card V : ℝ) * ManuscriptQLocalMarkedHeightRun.rosterBill I ≤ betaF G β S.patch.L ∧
        (∀ q ≤ S.patch.J, WilsonReportingDecoratedStage.Bought χ H q ∧
          betaF G β S.patch.L ^ (-((q:ℝ)+1-1/2)/2) ≤ (2*g)^((q:ℝ)+1-1/2)) ∧
        δ.rub (teller J (query R.metals.p R.metals.K j i)) (target J Q) (expense J Q)
          S.patch.L book.W book.μ book.order (teller J (query R.metals.p R.metals.K j i)).below S.patch.J β ∧
        Coat.gStep Y.beta = g ∧
        ∀ p ≤ S.patch.J, ∀ j ≤ S.patch.J, ∀ k ≤ S.patch.J,
          WilsonGaussianDeterminantStage.Bought χ H p j k

theorem opens (R : Run G) (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (joined G J χ δ)
      extra γ R.kit) (hG : G.Simple) : On R J χ δ extra γ paid := by
  intro Γ A
  have old := WilsonReportingPairedCash.original (Γ:=Γ) R A χ ((WilsonGaussianDeterminantStage.decal G χ).paired δ)
    extra γ paid hG
  filter_upwards [old] with m ready d hm F η I hi
  obtain ⟨H,renewed,crossed,high,laminate,sources,menu,card,⟨determinant,added⟩,word⟩ := ready d hm F I hi
  refine ⟨H,renewed,crossed,high,laminate,sources,menu,card,word,added,rfl,?_⟩
  intro p hp j hj k hk
  exact determinant p hp j hj k hk _ _ (R.alloy.B.a.clock.op d.level d.period) _ _ _ H

theorem purchased {G : Gauge} {V : Type} [Fintype V] [DecidableEq V]
    (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) (J : Request V) (χ : Chi) (δ : Charity.RG12.Decal G)
    (extra : Stage → ℕ → ℝ) (γ : ℝ) (hγ : -(1/2:ℝ) < γ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T)
      (affine : ManuscriptQLocalCofinalAffineFields.Paid R)
      (paid : QLocalRequestedSectorCalendar.Paid J (joined G J χ δ) extra γ R.kit),
      WilsonRootedPhysicalSpringGaussian.Receipt.{u} hG ε J extra γ ManuscriptQLocalCofinalAffineFields.schedule
        R T W affine.1 ∧
      ManuscriptQLocalScalarProgramSelection.ConditionalJetsOn R ∧
      (∀ through, ∃ first, WilsonRootedPhysicalSpringAffineRows.After R affine through first) ∧
      On R J χ δ extra γ paid := by
  let Δ := joined G J χ δ
  obtain ⟨R,T,W,affine,paid,physical,jets,rows⟩ :=
    WilsonRootedPhysicalSpringAffineRows.purchasedWith.{u} hG hε J extra γ hγ
      (@QLocalRequestedSectorCalendar.Paid G V J Δ extra γ)
      (fun s t => QLocalRequestedSectorCalendar.prepaid J Δ extra γ hG hγ s (ThroughLaunch.raging s t))
  exact ⟨R,T,W,affine,paid,physical,jets,rows,opens R J χ δ extra γ paid hG⟩

end YM.Integration.WilsonGaussianDeterminantTender
