import YM.Integration.QLocalInheritedPrincipal
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Brim.Lit

/-! Use the original uniform finite forest and block-angle average for every
actual incoming inherited row. The price and common regular footprint are
independent of the coarse configuration. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.QLocalInheritedPrincipalScroll
open Function Finset Lattice Wilson Pressure RG Tree Next Next.SectorChange Next.Fluctuations
open PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open Push.AbsoluteSums Push.SectorMeasure JointLoad JointLoad.Heir
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir
open ConnectedActivityE6 AnalyticBridge.LocalGaussianLaws AnalyticBridge.LocalGaussian
open Marker Comparison.RG02 IterationFour IterationFour.Vacuum
open LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric
open scoped BigOperators Classical

variable {G : Gauge} {c f : Side} (S : StepData c f) (B : BudgetPoint)
  (x u : ℝ) (D : Heir.Record) (Z : RegularAddress f) (χ : Chi)
  (l r : ℕ) (hB : 0 < radiusB x) (hl : 500 ≤ l) (hr : l+5 ≤ r)

def source : Script G S Z.support (headed (S := S) Z x l).support r x where
  Tag := Greenbelt.Reserve S × S.Choices
  Keys a := Key Z.support x (Greenbelt.allot a.1)
  chart _ := bareStores S
  forest a := Greenbelt.allot a.1
  θ a := a.2
  fits a := seatsAt Z.support x l hB hl (Greenbelt.allot a.1) (bareStores S) (nearby_zero ..)
  profile a := guard χ G (Key Z.support x (Greenbelt.allot a.1)) u (D.ε*B.threshold)
  moves _ := guard_natural _ _
  coefficient _ := (Fintype.card (Greenbelt.Reserve S × S.Choices):ℝ)⁻¹
  admissible := by
    letI : Nonempty (Forest S.ratio) := Tree.select S.ratio S.patch.odd_side
    let t : ℝ := Fintype.card (Greenbelt.Reserve S × S.Choices)
    have ht : 0 < t := Nat.cast_pos.mpr Fintype.card_pos
    rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    change t*|t⁻¹| ≤ 1
    rw [abs_of_pos (inv_pos.mpr ht),mul_inv_cancel₀ ht.ne']
  fields := (Footprint.inspected_price S.ratio l _ _ hB).trans
    (Corona.halo_mono (Nat.mul_le_mul_right _ hr) (Finset.Subset.refl _))

theorem played (n : ℕ) (hu : 0 < u) :
    (source (G:=G) S B x u D Z χ l r hB hl hr).Played n u (D.ε*B.threshold) :=
  ⟨fun _ => guard_silent χ hu (mul_pos D.guards B.threshold_pos)⟩

variable {V : Type} [DecidableEq V] [Fintype V] {Γ : Marker.Census V}
  (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
  {datum : LocalFormal.Datum R.family Γ} {F : AnalyticInput J A datum}
  {η : ℝ} (I : FullPreparedInputAt F η)

local notation "p₀" => A.outputNorm datum.level
local notation "p₁" => A.inputNorm datum.level
local notation "S₀" => R.family.path.levels.clock.op datum.level datum.period
local notation "x₀" => R.family.path.levels.clock.hatBeta datum.level
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family datum.cutoff datum.period (datum.level+1)
local notation "L₀" => fun i => headed (S := S₀) (I.error.labels i) (x₀) l

theorem purchased {n : ℕ} (C : Libretto G n) (hG : G.Simple)
    {Pt : Teller G} (T : Tube G (S₀)) (D : Heir.Record)
    (hT : Plays C D (p₀) (p₁) Pt T (x₀))
    (hA : Release.accepts r (p₁).supportExponent (p₀).supportExponent (S₀).patch.L)
    (hC : Lute.Plented C D (p₀) (p₁) (S₀).patch.L r (x₀) (g₁))
    (χ q : Chi) (d : ℝ) (hl : 500 ≤ l) (hr : l+5 ≤ r) :
    let hB : (p₀).B = radiusB (x₀) := (A.output_norm datum.level).block
    let σ := fun i => source (G:=G) (S₀) (p₁) (x₀) (g₁) D (I.error.labels i) χ l r
      (hB ▸ (p₀).B_pos) hl hr
    ∃ v : ℕ → ℝ, (∀ i, let f := (σ i).tuning (g₁) q d (I.error.action i) T
      (p₀).Regular (L₀ i).support f ∧ (p₀).supBounds (L₀ i).site (L₀ i).support f (v i)) ∧
      Footprint.Anchored (fun i => (L₀ i).site) v (fun i => coverNumber (p₀).B (L₀ i).support)
        (p₀).supportExponent (QLocalInheritedPrincipal.fee J C r/((S₀).patch.L.val:ℝ)*I.inherited) := by
  intro hB σ
  have hg := Currency.g_pos R.makes datum.cutoff datum.period (datum.level+1) datum.below
  exact QLocalInheritedPrincipal.principal R I C hG T hT hA hB hC
    (L₀) σ (fun _ => rfl) (fun i => played (G:=G) _ _ _ _ _ (I.error.labels i) χ l r _ hl hr n hg) q d

end YM.Integration.QLocalInheritedPrincipalScroll
end
