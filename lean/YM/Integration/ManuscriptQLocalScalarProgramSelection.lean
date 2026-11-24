import YM.Integration.ManuscriptQLocalScalarClockPurchase
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun
import YM.Integration.ManuscriptQLocalMeasuredConditional

noncomputable section
namespace YM.Integration.ManuscriptQLocalScalarProgramSelection
open PhysicalNext.Repeat.Legato WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
universe u
variable {G : Gauge}

/-- Joint source and cutoff prices filed before selecting the original physical campaign. -/
theorem original (simple : G.Simple) {penalty : ℝ} (hp : 0 < penalty) (order : ℕ → ℕ → ℕ) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      FundedPredictionSupply.Both (@ManuscriptQLocalScalarSourcePurchase.Paid G order)
        (@ManuscriptQLocalScalarClockPurchase.Paid G order) R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple penalty W :=
  fundedOriginalRun_with_prediction.{u} simple hp _ (ManuscriptQLocalScalarClockPurchase.both order)

/-- The same selected run carries each additional independently prepaid prediction. -/
theorem alongside (simple : G.Simple) {penalty : ℝ} (hp : 0 < penalty)
    (order : ℕ → ℕ → ℕ) (extra : Prediction G) (funded : FundedPredictionSupply.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      FundedPredictionSupply.Both (@ManuscriptQLocalScalarSourcePurchase.Paid G order)
        (@ManuscriptQLocalScalarClockPurchase.Paid G order) R.kit ∧ extra R.kit ∧
      NativeFVAPlateau.Correlations R ∧ FundedOriginalProperties.{u} simple penalty W := by
  let pair : Prediction G := @FundedPredictionSupply.Both G
    (@ManuscriptQLocalScalarSourcePurchase.Paid G order) (@ManuscriptQLocalScalarClockPurchase.Paid G order)
  obtain ⟨R,T,W,bought,corr,props⟩ := fundedOriginalRun_with_prediction.{u} simple hp
    (@FundedPredictionSupply.Both G (@pair) (@extra))
    (fun s q => FundedPredictionSupply.both (ManuscriptQLocalScalarClockPurchase.both order s q) (funded s q))
  exact ⟨R,T,W,bought.1,bought.2,corr,props⟩

end YM.Integration.ManuscriptQLocalScalarProgramSelection
end

noncomputable section
namespace YM.Integration.ManuscriptQLocalScalarProgramSelection
universe u
open Marker PhysicalNext.Repeat.Legato Progress.DirectedRecipe
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection
open Next.SectorChange Next.SectorChange.Gaussian AnalyticBridge.GaussianFieldAlignment
open Push.SectorMeasure FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open LocalComparison Comparison.RG02 Precision FreeResolvent.Affine
open scoped Topology Classical ContDiff

/-- Every finite physical charged-to-quiet conditional jet on this original run
is the jet of the same paid marked rows, including all holes in the denominator. -/
def ConditionalJetsOn {G : Gauge} (R : Run G) : Prop :=
  ∀ {I : Type} [DecidableEq I] {Γ : Census I} (d : LocalFormal.Datum R.family Γ)
    (D : Allocation G (R.family.path.levels.clock.op d.level d.period)
      (R.alloy.B.a.clock.hatBeta d.level)
      (R.kit.walls (R.alloy.B.a.clock.J (d.level+1)) (R.alloy.B.a.clock.J d.level)))
    (q : Chi) [Fintype I] {J : Request I} {A : NumericSchedule R.family J}
    (H : AnalyticInput J A d) (x : TestSpace J.tests)
    (k₀ : (R.family.path.levels.clock.op d.level d.period).Choices) (s : Γ.Mode) (j : ℕ)
    (v : Fin j → Gaussian.Vec (Raw G (R.family.side d.level d.period))),
      iteratedFDeriv ℝ j (fun B : Gaussian.Vec (Raw G (R.family.side d.level d.period)) =>
        (Actual.Push (R.family.path.levels.clock.op d.level d.period)
          (R.family.path.rep d.cutoff d.period (d.level+1)).beta
          (ManuscriptQLocalActualLog.source R d H x) (represent (decode B))).part s /
          ((R.family.path.rep d.cutoff d.period d.level).eval (represent (decode B)) : ℂ)) 0 v =
        iteratedFDeriv ℝ j (ManuscriptQLocalMeasuredConditional.measured R d D q H x k₀ s) 0 v

theorem measuredOn {G : Gauge} (R : Run G) : ConditionalJetsOn R := by
  intro I inst Γ d D q fi J A H x k₀ s j v
  exact ManuscriptQLocalMeasuredConditional.conditional_jet R d D q H x k₀ s j v

/-- The schedule is funded before selecting this one run. Its original
measured jets keep their physical charged and quiet columns on that run. -/
theorem attained_with_jets {G : Gauge} (simple : G.Simple) {penalty : ℝ}
    (hp : 0 < penalty) (order : ℕ → ℕ → ℕ)
    (extra : Prediction G) (funded : FundedPredictionSupply.AllPrices (@extra)) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      FundedPredictionSupply.Both (@ManuscriptQLocalScalarSourcePurchase.Paid G order)
        (@ManuscriptQLocalScalarClockPurchase.Paid G order) R.kit ∧ extra R.kit ∧
      ConditionalJetsOn R ∧ NativeFVAPlateau.Correlations R ∧
      FundedOriginalProperties.{u} simple penalty W := by
  obtain ⟨R,T,W,hpaid,other,hcorr,hfunded⟩ := alongside.{u} simple hp order (@extra) funded
  exact ⟨R,T,W,hpaid,other,measuredOn R,hcorr,hfunded⟩
end YM.Integration.ManuscriptQLocalScalarProgramSelection
end

