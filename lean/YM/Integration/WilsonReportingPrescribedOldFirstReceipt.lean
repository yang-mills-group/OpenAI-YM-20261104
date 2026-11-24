import YM.Integration.WilsonReportingPrescribedOldFirstRadii

/-! The original successor's actual normalized test budget on every component
of the first nonbare deposited MS program. -/
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldFirstReceipt
open Filter Lattice Wilson RG Source Marker Precision Pert.Asymptotics IterationFour
open PhysicalNext.Repeat.Legato LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open IterationFour.Vacuum FullQLocal.RenderedStep.Numeric Comparison.RG02 WilsonLimitConstruction
open FullQLocal.PreRun.SuccessiveRequests RG3.Script.Picnic
open MergeProof MergeProof.Accent
open scoped Topology Classical
variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {B : MS.Local.Physical.Deck G}
    (R : Run G) (hG : G.Simple) (u : V → MS.Rake.Label B) (J : Request V) (A : NumericSchedule R.family J)
    (caps : Handoff.OutputCapacities) (r : ℕ)
local notation "J₀" => ActualOriginalQPointSetup.request R u J
local notation "A₀" => ActualOriginalQInitialInput.schedule R hG u J A
local notation "F₀" => ActualOriginalQInitialInput.input R hG u J A

/-- The radius stamp is the one returned by the original
`FundedCoverStepPrice.eventually_issued_with_radii` on the same chosen bank. -/
theorem original (A' : NumericSchedule R.family (nextRequest (J₀) caps r)) :
    ∀ᶠ m : ℕ in atTop, ∀ (d : LocalFormal.Datum R.family (Stock.census V)) (dm : d.level=m+1)
      (P : MS.Land.Prescription B) (o : V → Site (R.family.side (d.level+1) d.period)) (μ : ℝ) (ks : V → ℕ)
      (ord : ∀ k, k≤(R.metals.p.profile k).order ∧ k≤(R.metals.p.profile k).power)
      (first : ActualOriginalQInitialInput.start R hG u J A ord ≤ d.level)
      (per : (J₀).physicalPeriodLower ≤ (R.family.S.period d.period).val),
      let F := F₀ d P o μ ks ord first per
      ∀ (K : NumericPrices (A₀)) (I : FullPreparedInputAt F 0) (M : FundedPhysicalCatalogue.Purchase caps K F)
        (S : FundedRenderedBank.Chosen K I M.toCatalogue) (bank : FundedRenderedBank.Canonical S)
        (W : Bulk.Colors (Stock.census V) G (R.family.side (m+1) d.period))
        (x : Exterior.fieldDir G (R.family.side m d.period) 1) (q : ℕ)
        (next : FundedCoverStepPrice.Receipt R M S bank r dm A' W x q),
        next.analytic.outputRadii = (fun v=>F.outputRadii v/A'.radiusLoss m) →
        ∀ s : (Stock.census V).Mode,
          let w := fun v=>next.analytic.outputRadii v/next.analytic.kernelCosts v
          let radius := ((A₀).radiusLoss (m+1)*A'.radiusLoss m)^s.val.card
          Poly.toll w s = radius⁻¹ ∧ (regulatorRun R.family d.cutoff d.period (m+1))^2 ≤ 2*Poly.toll w s := by
  filter_upwards [WilsonReportingPrescribedOldFirstRadii.adjacent R hG (A₀) A'] with m funded
  intro d dm P o μ ks ord first per
  dsimp only
  intro K I M S bank W x q next chosen s
  obtain ⟨fine,fees⟩ := WilsonReportingPrescribedOldFirstRadii.initial R hG u J A d P o μ ks ord first per
  let a := (A₀).radiusLoss (m+1)*A'.radiusLoss m
  have pos : 0<a := mul_pos ((A₀).radius_loss_positive _) (A'.radius_loss_positive _)
  have weight (v : V) : next.analytic.outputRadii v/next.analytic.kernelCosts v = a⁻¹ := by
    rw [chosen,next.shared.costs,fine,fees,dm]
    simp [a,div_eq_mul_inv,mul_comm]
  have all : Poly.toll (fun v=>next.analytic.outputRadii v/next.analytic.kernelCosts v) s = (a^s.val.card)⁻¹ := by
    simp only [Poly.toll,weight,Finset.prod_const,inv_pow]
  refine ⟨all,?_⟩
  rw [all,←div_eq_mul_inv]
  apply (le_div_iff₀ (pow_pos pos _)).2
  have live : m+1<d.cutoff := by have h:=d.below;omega
  rw [mul_comm]
  exact funded d.cutoff d.period live s.val

end YM.Integration.WilsonReportingPrescribedOldFirstReceipt
