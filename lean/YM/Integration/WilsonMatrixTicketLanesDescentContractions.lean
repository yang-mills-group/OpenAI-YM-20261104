import YM.Integration.WilsonMatrixTicketLanesDescentWords
import YM.Integration.WilsonConditionalTaylorThermalBidScore
import YM.FVA2.OrbitWick

/-! The actual leading conditional profile as a finite signed Wick matrix sum. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonMatrixTicketLanesDescentContractions
open Function Filter MeasureTheory Lattice RG Tree Wilson Precision Push.BetaTransport PhysicalNext.Repeat.Legato
open PertExtension PertExtension.Series PertExtension.GaussianScore RGComparison.Core16 RGComparison.Core16.Descent
open Next.Rank.Normal ThermalShortcuts.ThermalJets WilsonConditionalTaylorThermalCensus
open WilsonConditionalTaylorThermalBidScore WilsonMatrixTicketLanesDescentWords
open scoped Topology BigOperators Classical

variable {G : Gauge} (R : Run G) {I : Type} [Fintype I] (k : I → ℕ)
    (i : ∀ s, (R.family.labels.level (k s)).Index) {N p : ℕ} {c : Side}
    (d : Descent (R.family.side N p) c) (x : I → Site (R.family.side N p))

/-- Each real part or imaginary part is contracted with the genuine signed
coefficient of the recorded face/color polynomial, on the same complete Hessian. -/
theorem original (P : ChartRatio G) (chart : LocalRatio P) (room : d.Room G)
    (t : d.Tags) (u : ℕ → ℝ) (b : Bool) :
    let S := entries R.family k i (fun s => CoefficientBridge.run_valuation R (k s))
    let L := fun s => leg G d (face S x s) (color S s)
    let amount := ∑ m ∈ rows S, bill S b m *
      (blend (FVA2.Wick.color (ambient t room) L) 0 (glyphs id (parties S m))).re
    let f := word R k i x b
    let w := Spool.power (lamps R k i)
    Tendsto (fun a : ℝ => a⁻¹^w * d.conditioned (offset u a) f 1) Tested.germ (𝓝 amount) ∧
      ranking P d u f w = amount := by
  intro S L amount f w
  let Γ := ambient t room
  let μ := Chart.tangent G d.Links
  let A (m) := Law.product L (parties S m)
  have registered (y : Coordinates G d) : Radial.jet (f ∘ d.fine 1 ∘ d.tablePath) w y =
      ∑ m ∈ rows S, bill S b m * A m y :=
    WilsonConditionalTaylorThermalBidScore.original R.family k i
      (fun s => CoefficientBridge.run_valuation R (k s)) d x R.makes b y
  have settled (m) : Integrable (fun y => A m y * Γ.kern y) μ :=
    Γ.integrable_entry μ (Law.product_bound L (parties S m)) (Law.product_cont L (parties S m))
  have wick (m) : Γ.average μ (A m) =
      (blend (FVA2.Wick.color Γ L) 0 (glyphs id (parties S m))).re :=
    congrArg Complex.re (FVA2.Wick.monomial_wick Γ L μ id (parties S m))
  have computed : Γ.average μ (Radial.jet (f ∘ d.fine 1 ∘ d.tablePath) w) = amount := by
    change (∫ y, Radial.jet (f ∘ d.fine 1 ∘ d.tablePath) w y * Γ.kern y ∂μ) / (∫ y, Γ.kern y ∂μ) = amount
    simp_rw [registered,Finset.sum_mul,mul_assoc]
    rw [integral_finsetSum _ (fun m _ => (settled m).const_mul (bill S b m))]
    simp_rw [integral_const_mul]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro m _
    rw [mul_div_assoc,← wick m]
    rfl
  obtain ⟨actual,rank⟩ := WilsonMatrixTicketLanesDescentWords.original R k i d x P chart room t u b
  exact ⟨computed ▸ actual,rank.trans computed⟩

end YM.Integration.WilsonMatrixTicketLanesDescentContractions
