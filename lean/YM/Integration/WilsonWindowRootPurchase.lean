import YM.AllOrder.Floe.Campus
import YM.Integration.WilsonLimitConstruction.FundedOriginalRun

/-! Select the roots and their physical roll tab for the marked-window comparison
on the same campaign that supplies the original Wilson continuum. -/
set_option autoImplicit false
noncomputable section

namespace YM.Integration.WilsonWindowRootPurchase

open RG RG.Supply Precision Org
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Next.Foundations Push.PriceCompiler
open AllOrder.Floe.Step.PlanV
open WilsonLimitConstruction WilsonLimitConstruction.FundedCompanySelection

universe u

/-- This choice sees only the original stage profile, price, and kernel. In
particular it is unchanged by increasing the block-length floor of the sheet. -/
def roots {G : Gauge} (hG : G.Simple) (s : Sheet G) (price : MapPrices) :
    Roots (G := G) s.profile price s.kernel :=
  Classical.choice (acquire hG s.profile price s.kernel)

/-- Keep the same tab in every subsequent purchase made on these actual rolls. -/
def rollTab {G : Gauge} (hG : G.Simple) (M : Metals G) (D : Rolls M.p) :
    Roots.Tab (X := M) (roots hG M.p M.K) D :=
  Classical.choice (Roots.options (X := M) D (roots hG M.p M.K) hG)

/-- Both the physical length bound and all of the tab's later numerical
receipts, for these particular roots and the actual delay of the factor. -/
def Granted {G : Gauge} (hG : G.Simple) : Prediction G := fun {M} {D} {A} _ =>
  (∀ j, (roots hG M.p M.K).Rise j ((D.L j).val : ℝ)) ∧
    Roots.Receives (X := M) D (roots hG M.p M.K) (rollTab hG M D) A.delay

theorem prepaid {G : Gauge} (hG : G.Simple) (s : Sheet G) (price : MapPrices) :
    Prepaid (@Granted G hG) s price := by
  intro targets expenses chartEq programs wages baton wanting
  obtain ⟨floor, high⟩ := (roots hG s price).prize
  refine ⟨floor, ?_⟩
  intro l hl D w duration register post scouts protection stages cost V quarter
  let M : Metals G := ⟨ThroughLaunch.raise s l, price, chart G, chart_ok G⟩
  have rise (j : ℕ) : (roots hG M.p M.K).Rise j ((D.L j).val : ℝ) :=
    high j (D.L j) ((hl j).trans (D.large j).need)
  obtain ⟨W, hVW, receive⟩ := Roots.summit (X := M) D (roots hG M.p M.K)
    rise (rollTab hG M D) V
  refine ⟨W, hVW, ?_⟩
  intro W' hWW' bar wait priced directed
  dsimp only
  intro η q exchange menu auxiliary quotes booth
    shelter works divides
  exact ⟨rise, receive W' hWW'⟩

/-- The roots that meet the marked comparison costs belong to the original
funded run, with its moving correlations and original physical conclusions. -/
theorem selected {G : Gauge} (hG : G.Simple) {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : Run G) (T : Campaign R) (W : Campaign.Pillars R T),
      Granted hG R.kit ∧ NativeFVAPlateau.Correlations R ∧
        FundedOriginalProperties.{u} hG ε W :=
  fundedOriginalRun_with_prediction.{u} hG hε (@Granted G hG)
    (fun s T => prepaid hG s (ThroughLaunch.raging s T))

end YM.Integration.WilsonWindowRootPurchase
end

