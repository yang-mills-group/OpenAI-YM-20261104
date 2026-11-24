import YM.Integration.WilsonReportingDecoratedStage

/-! The single physical reporting conductor meeting the high, laminate, and
incoming marked-source obligations and the paid decorated integral. -/
set_option maxHeartbeats 200000
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonReportingDecoratedCash
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

variable (R : Run G) {J : Request V} (A : NumericSchedule R.family J)
    (χ : Chi) (extra : Stage → ℕ → ℝ) (γ : ℝ)
    (paid : QLocalRequestedSectorCalendar.Paid J (WilsonReportingDecoratedStage.joined G J χ) extra γ R.kit)

theorem original (hG : G.Simple) :
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
        ∀ q ≤ S.patch.J, WilsonReportingDecoratedStage.Bought χ H q ∧
          betaF G β S.patch.L ^ (-((q:ℝ)+1-1/2)/2) ≤ (2*g)^((q:ℝ)+1-1/2) := by
  have h₀:=(tendsto_add_atTop_nat 1).eventually (QLocalRequestedSectorIntake.affordable (J:=J) R hG)
  have deep : Tendsto R.alloy.B.a.clock.J atTop atTop := R.family.path.levels.fits.deep
  have cards := (deep.comp (tendsto_add_atTop_nat 1)).eventually (eventually_ge_atTop (Fintype.card V))
  filter_upwards [ManuscriptQLocalVacuumCash.funds (Γ:=Γ) R A hG, h₀, cards,
    ManuscriptQLocalMarkedHeightRun.reserve (Γ:=Γ) R A hG] with m charge money card reserve d hm F η I hi
  subst m
  let g:=Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
  let old:=ManuscriptQLocalVacuumFamily.source (QLocalInheritedPhysicalInlet.rep I) F.layers g 1
  let Y:=QLocalInheritedRegularSlots.carrier old
  let Δ:=WilsonReportingDecoratedStage.joined G J χ
  let S:=R.alloy.B.a.clock.op d.level d.period
  let T:=ships R.alloy.B d.cutoff d.level d.period
  let x:=R.alloy.B.a.clock.hatBeta d.level
  let β:=betaF G x S.patch.L
  have row:=ManuscriptQLocalVacuumFamily.bought I hi 1
  have hin:=QLocalRequestedSectorIntake.intake R I hi
    (I.inherited_bound.trans (money d.cutoff d.period d.below))
  have e:=ManuscriptQLocalVacuumCash.intake R A d F I hi hin (charge d rfl F I)
  have orig:=QLocalInheritedRegularSlots.intake old e
  have full:=(QLocalInheritedRegularSlots.original old).Ebound row.1.boundE
  obtain ⟨H,ren,cross⟩:=QLocalRequestedSectorCalendar.source_for_on (J:=J) (Δ:=Δ)
    (extra:=extra) (γ:=γ) (R:=R) (paid:=paid) (A:=A) (z:=d) Y orig rfl rfl _ full
  have win:=QLocalRequestedSectorCalendar.selected J Δ extra γ R paid d
  have works:Works _ S.patch.L x S T:=⟨orig.ready,rfl,by rw [add_comm 1];exact R.alloy.B.a.fits.sizeT _ _⟩
  have stamp:=protocol (n:=d.period) R.alloy.B d.below R.kit.pledging.conducts.full
  have hb:R.alloy.B.a.clock.hatBeta (d.level+1)=β:=Application.clock_next R.alloy.B.a d.level d.period
  have hp:0<β:=zero_lt_one.trans_le win.analytic.1.1.1
  have hh:(Real.sqrt β)⁻¹≤2*g:=by
    rw [←hb]
    exact (IterationFour.Currency.hat_g R.makes d.cutoff d.period (d.level+1) d.below).1
  have hpow:(Real.sqrt β)⁻¹=β^(-(1/2:ℝ)):=by rw [Real.rpow_neg hp.le,Real.sqrt_eq_rpow]
  have rounded : β^(-((J.order:ℝ)+1)/2) ≤ (2*g)^(J.order+1) := by
    calc
      β^(-((J.order:ℝ)+1)/2)=((Real.sqrt β)⁻¹)^(J.order+1):=by
        rw [hpow,←Real.rpow_natCast,←Real.rpow_mul hp.le]
        congr 1
        push_cast
        ring
      _ ≤ _:=pow_le_pow_left₀ (inv_nonneg.mpr (Real.sqrt_nonneg β)) hh _
  have high : ManuscriptQLocalMarkedHeightRun.High (expense J (R.kit.target _ _)) H J Γ ((2*g)^(J.order+1)) := by
    exact ManuscriptQLocalMarkedHeightRun.certificate _ H J Γ (i:=S.patch.J)
      (h:=(teller J (query R.metals.p R.metals.K (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level))).below) win.analytic.1.1 works stamp orig.cap.labels.boundE _ rounded
  have hcard : Fintype.card V ≤ S.patch.J+1 := by
    rw [(Testing.proceeds R.alloy.B d.cutoff d.level d.period d.below).atStep]
    exact card.trans (Nat.le_succ _)
  refine ⟨H,ren,cross,high,?_,?_,ManuscriptQLocalMarkedHeightRun.enrolled I,reserve d rfl F I hi,?_⟩
  · intro M hm
    obtain ⟨a,read⟩ := win.analytic.1.2.1 M hm
    exact ⟨a,read _ _ S T stamp Y _ H⟩
  · intro base x E K
    exact QLocalMarkedSourceCalendar.source (ManuscriptQLocalMarkedHeightRun.rosterBudget I) H stamp
      win.analytic.1.2.2 (QLocalMarkedSourceCalendar.requested J _) hcard base x E K
  · intro q payment
    refine ⟨win.analytic.2 q payment _ _ S T Y _ H,?_⟩
    change β^(-((q:ℝ)+1-1/2)/2) ≤ (2*g)^((q:ℝ)+1-1/2)
    calc
      _ = ((Real.sqrt β)⁻¹)^((q:ℝ)+1-1/2) := by
        rw [hpow,←Real.rpow_mul hp.le]
        congr 1
        ring
      _ ≤ _ := Real.rpow_le_rpow (inv_nonneg.mpr (Real.sqrt_nonneg β)) hh (by have : (0:ℝ)≤q := Nat.cast_nonneg q; linarith)

end YM.Integration.WilsonReportingDecoratedCash
