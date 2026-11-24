import YM.Integration.QLocalVacuumOrderRestriction
import YM.Integration.FullQLocalCostSubpower

/-! Physical price of the omitted genuine outgoing vacuum pieces on the same received plan. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.QLocalSelectedVacuumGrades

open Filter Lattice Wilson RG Marker PhysicalNext.Repeat.Legato IterationFour IterationFour.Vacuum
open LocalComparison FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open Comparison.RG02 PhysicalWilsonActionConvention QLocalVacuumOrderRestriction
open FullQLocal.PreRun.CostProfile Pert.Asymptotics
open scoped Topology BigOperators Classical

variable {G : Gauge} {V : Type} {J : Request V} (R : Run G) (A : NumericSchedule R.family J)

private theorem dominated {f F : ℕ→ℝ} (b : ∀ m,f m≤F m)
    (paid : ActualRunSubpowerShift.Subpower R F) : ActualRunSubpowerShift.Subpower R f := by
  intro eta pos
  filter_upwards [paid eta pos] with m hm N t hN using (b m).trans (hm N t hN)

private theorem geometry (hG : G.Simple) (K : NumericPrices A) :
    ActualRunSubpowerShift.Subpower R K.geometry := by
  have hW := scalar_subpower_of_schedule R A
  have h1 := scalar_subpower_constant R hG A 1
  have sum := scalar_subpower_add R hG A _ _ h1 hW
  have pow := scalar_subpower_pow R hG A _ (fun m=>add_nonneg zero_le_one (A.admitted_cost_nonnegative m))
    sum K.polynomialDegree
  have c := scalar_subpower_constant R hG A K.polynomialConstant
  exact dominated R K.polynomial_bound (scalar_subpower_mul R _ _
    (fun m=>pow_nonneg (add_nonneg zero_le_one (A.admitted_cost_nonnegative m)) _) c pow)

private theorem widths (hG : G.Simple) :
    ActualRunSubpowerShift.Subpower R (fun m=>1+(A.outputWidth m)⁻¹) := by
  apply scalar_subpower_add R hG A _ _ (scalar_subpower_constant R hG A 1)
  apply dominated R (fun m=>?_) (scalar_subpower_of_schedule R A)
  have h := A.cost_covers_widths m
  linarith [(inv_pos.mpr (A.input_width_pos m)).le,(A.radius_loss_positive m).le]

theorem tariff (hG : G.Simple) (K : NumericPrices A) (C : ℝ) (d rank : ℕ) :
    ActualRunSubpowerShift.Subpower R (fun m=>C*(K.geometry m)^2*
      (1+(A.outputWidth m)⁻¹)^d*A.admittedCost m^rank) := by
  have h₀ := scalar_subpower_constant R hG A C
  have h₁ := scalar_subpower_pow R hG A K.geometry K.geometry_nonnegative (geometry R A hG K) 2
  have h₂ := scalar_subpower_pow R hG A _ (fun m=>add_nonneg zero_le_one (inv_pos.mpr (A.output_width_pos m)).le)
    (widths R A hG) d
  have h₃ := scalar_subpower_pow R hG A _ A.admitted_cost_nonnegative (scalar_subpower_of_schedule R A) rank
  have f₁ := scalar_subpower_mul R _ _ (fun m=>sq_nonneg (K.geometry m)) h₀ h₁
  have f₂ := scalar_subpower_mul R _ _ (fun m=>pow_nonneg (add_nonneg zero_le_one (inv_pos.mpr (A.output_width_pos m)).le) d) f₁ h₂
  exact scalar_subpower_mul R _ _ (fun m=>pow_nonneg (A.admitted_cost_nonnegative m) _) f₂ h₃

variable [DecidableEq V]

/-- The chosen family and all independent field/test data follow this common physical tail.
The returned per-piece charges are genuine local Invoices at the original requested +3 norm. -/
theorem bank [Fintype V] {Γ : Census V} (hG : G.Simple) (K : NumericPrices A) (caps : Handoff.OutputCapacities)
    (p : ℕ) (eta epsilon : ℝ) (he : 0<eta) (hε : 0<epsilon) :
    ∀ᶠ m : ℕ in atTop, ∀ (z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀ (S : List (Piece G (R.family.side z.level z.period)))
        (B : GradedVacuumLayers S (A.outputNorm z.level) J.order caps.vacuumRank
          (A.outputWidth z.level) (K.geometry z.level)), Render.permits S (A.outputNorm z.level) →
        let H := B.packets
        let g := regulatorRun R.family z.cutoff z.period (z.level+1)
        ∀ g' : ℝ, g≤2*g' → g'≤2*g →
        (∀ a∈extra S p, a.packet.Invoice (A.outputNorm z.level) (ZeroAwareCappedRenderInvoice.credit H a)) ∧
        debit H p g' ≤ epsilon*g^((p:ℝ)+1-eta) := by
  obtain ⟨C,hC,d,paid⟩ := priced G caps.vacuumRank J.outputFieldOrder J.outputDistanceOrder
  let C' := C*(2:ℝ)^(caps.vacuumRank+(p+1))
  filter_upwards [tariff R A hG K (C'/epsilon) d caps.vacuumRank eta he,
    (tendsto_add_atTop_nat 1).eventually (IterationFour.Currency.g_small hG R.makes (1/2) (by norm_num))]
    with m limits weak
  intro z hz S B permits
  dsimp only
  intro g' low high
  subst m
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  have hg : 0<g := IterationFour.Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt z.below)
  have hweak : g<1/2 := weak z.cutoff z.period (Nat.succ_le_of_lt z.below)
  change g≤2*g' at low
  change g'≤2*g at high
  have hg' : 0<g' := by linarith only [hg,low]
  have hg1 : g'≤1 := by linarith only [hweak,high]
  have units := A.cost_covers_units z.level z.cutoff z.period z.below
  have θ : 0≤R.family.path.levels.clock.threshold (z.level+1) / g :=
    div_nonneg (R.family.path.levels.budget (z.level+1)).threshold_pos.le hg.le
  have ratio : (A.outputNorm z.level).threshold/g≤A.admittedCost z.level := by
    rw [(A.output_norm z.level).threshold]
    change R.family.path.levels.clock.threshold z.level/g ≤ _
    linarith only [units,θ]
  have r' : (A.outputNorm z.level).threshold/g'≤2*A.admittedCost z.level := by
    apply (div_le_iff₀ hg').2
    calc
      _ ≤ A.admittedCost z.level*g := (div_le_iff₀ hg).1 ratio
      _ ≤ A.admittedCost z.level*(2*g') := mul_le_mul_of_nonneg_left low (A.admitted_cost_nonnegative _)
      _ = _ := by ring
  obtain ⟨rows,amount⟩ := paid B.packets (A.output_norm z.level).order
    (A.output_norm z.level).distance (A.output_width_pos z.level) permits
    p g' _ hg' hg1 (by linarith only [A.admitted_cost_ge_one z.level]) r'
  refine ⟨rows,amount.trans ?_⟩
  have hearn := limits z.cutoff z.period z.below
  have scale : C'*(K.geometry z.level)^2*(1+(A.outputWidth z.level)⁻¹)^d*A.admittedCost z.level^caps.vacuumRank ≤
      epsilon*g^(-eta) := by
    calc
      _ = epsilon*((C'/epsilon)*(K.geometry z.level)^2*(1+(A.outputWidth z.level)⁻¹)^d*
          A.admittedCost z.level^caps.vacuumRank) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hearn hε.le
  calc
    _ ≤ C*(K.geometry z.level)^2*(1+(A.outputWidth z.level)⁻¹)^d*(2*A.admittedCost z.level)^caps.vacuumRank*(2*g)^(p+1) :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hg'.le high (p+1))
        (by have := A.admitted_cost_nonnegative z.level; have := A.output_width_pos z.level; positivity)
    _ = (C'*(K.geometry z.level)^2*(1+(A.outputWidth z.level)⁻¹)^d*A.admittedCost z.level^caps.vacuumRank)*g^(p+1) := by
      dsimp only [C']
      rw [mul_pow,mul_pow,pow_add]
      ring
    _ ≤ (epsilon*g^(-eta))*g^(p+1) := mul_le_mul_of_nonneg_right scale (pow_nonneg hg.le _)
    _ = epsilon*g^((p:ℝ)+1-eta) := by
      rw [mul_assoc,← Real.rpow_natCast,← Real.rpow_add hg]
      congr 2
      push_cast
      ring

variable [Fintype V] {Γ : Census V}

theorem forecast (hG : G.Simple) (K : NumericPrices A) (caps : Handoff.OutputCapacities)
    (p : ℕ) (eta epsilon : ℝ) (he : 0<eta) (hε : 0<epsilon) :
    ∀ᶠ m : ℕ in atTop, ∀ (z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A z) (M : SignedAnalyticOutput caps Y K F),
        let S := M.plan.layers z.level
        let H := M.vacuum.packets
        let g := regulatorRun R.family z.cutoff z.period (z.level+1)
        ∀ g' : ℝ, g≤2*g' → g'≤2*g →
        (∀ a∈extra S p, a.packet.Invoice (A.outputNorm z.level) (ZeroAwareCappedRenderInvoice.credit H a)) ∧
        debit H p g' ≤ epsilon*g^((p:ℝ)+1-eta) := by
  filter_upwards [bank (Γ:=Γ) R A hG K caps p eta epsilon he hε] with m h z hz Y F M
  exact h z hz _ M.vacuum M.output_layers_paid

theorem selected (hG : G.Simple) (K : NumericPrices A) (caps : Handoff.OutputCapacities)
    (p : ℕ) (eta epsilon : ℝ) (he : 0<eta) (hε : 0<epsilon) :
    ∀ᶠ m : ℕ in atTop, ∀ (z : LocalFormal.Datum R.family Γ), z.level=m →
      ∀ (Y : Bulk.Chain R.family.path) (F : AnalyticInput J A z) (M : SignedAnalyticOutput caps Y K F),
        let S := M.plan.layers z.level
        let H := M.vacuum.packets
        let g := regulatorRun R.family z.cutoff z.period (z.level+1)
        (∀ a∈extra S p, a.packet.Invoice (A.outputNorm z.level) (ZeroAwareCappedRenderInvoice.credit H a)) ∧
        debit H p g ≤ epsilon*g^((p:ℝ)+1-eta) := by
  filter_upwards [forecast (Γ:=Γ) R A hG K caps p eta epsilon he hε] with m h z hz Y F M
  let g := regulatorRun R.family z.cutoff z.period (z.level+1)
  have hg : 0<g := Currency.g_pos R.makes _ _ _ (Nat.succ_le_of_lt z.below)
  exact h z hz Y F M g (by linarith only [hg]) (by linarith only [hg])

end YM.Integration.QLocalSelectedVacuumGrades
end
