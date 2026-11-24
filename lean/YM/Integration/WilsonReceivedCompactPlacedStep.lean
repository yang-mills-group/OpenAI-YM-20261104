import YM.Integration.WilsonReceivedCloseGeometricPlacedCourse
import YM.Integration.WilsonReceivedCompactPriorIntegral
import YM.Integration.WilsonMeasuredOwnerIntegrable

set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
universe u
namespace YM.Integration.WilsonReceivedCompactPlacedStep
open Filter Finset Multi Lattice Wilson RG Tree Marker QuadraticLocal QuadraticLocal.Earn QuadraticLocal.Advent QuadraticLocal.Advent.Oak
open QuadraticLocal.Mentor Org AllOrder AllOrder.Floe AllOrder.Floe.Step AllOrder.Floe.Step.PlanV
open AllOrder.Transit PhysicalNext PhysicalNext.Repeat PhysicalNext.Repeat.Legato
open PhysicalNext.Repeat.Boulevard Push Push.PriceCompiler
open AllOrder.Transit.WheelP AnalyticBridge VerifiedReset RemainderComparison
open QuadraticLocal.Rebirth QuadraticLocal.Affinity Pressure ConnectedActivityE6

open Extra.Histories MergeProof.Accent Pert.Asymptotics Filter WilsonOriginalReceivedChain
open Laurent Stationary Comparison.RG02 Comparison.RG02.Order Extra Source
open FullQLocal FullQLocal.RenderedStep Multi Exterior Comparison.RG02.Cumulants
open OPE.Therm WilsonLimitConstruction RG16.Literal Source Labels Extra.Histories
open scoped BigOperators Classical

open Trace.Physical WilsonMeasuredCoefficientTransport MeasureTheory Extra.Histories XSpace XSpace.Rose OPE.Orbits
variable {G:Gauge} (R:Run G) {N per i:ℕ}
local notation "F₀" => R.family.labels.level 0
local notation "S₀" => R.family.localSection 0
local notation "κ" j:max => LocalComparison.forcedDivisor R.family j
local notation "sheet" => R.family.path.levels.clock.op i per
local notation "top" => R.family.side (i+1) per
local notation "bot" => R.family.side i per
variable {O:Type} [Fintype O]

/-- The original rank-zero transition commutes with a signed sum on its actual Haar integrable inputs. -/
theorem linear (w:O → ℂ) (f:O → Config G (top) → ℂ)
    (paid:∀o,Integrable (f o) (prior G (top))) :
    GermGraph.transition (C:=R.family) 0 N per i (fun U=>∑o,w o*f o U) =
      fun U=>∑o,w o*GermGraph.transition (C:=R.family) 0 N per i (f o) U := by
  let β:=R.family.path.β N per (i+1)
  have valid:(sheet).IsKernel β G:=R.family.path.levels.transition_mass ..
  have step (t:Finset O):(sheet).push β (fun U=>∑o∈t,w o*f o U) =
      fun V=>∑o∈t,w o*(sheet).push β (f o) V := by
    induction t using Finset.induction_on with
    | empty => funext V;simp [RG.StepData.push]
    | @insert a t ha ih =>
      simp only [Finset.sum_insert ha]
      have combined:(fun U=>w a*f a U+∑o∈t,w o*f o U)=w a • f a+(fun U=>∑o∈t,w o*f o U):=rfl
      have gathered:Integrable (fun U=>∑o∈t,w o*f o U) (prior G (top)):=
        integrable_finsetSum t (fun o _=>(paid o).const_mul (w o))
      rw [combined,RG.StepData.push_add valid (w a • f a) (fun U=>∑o∈t,w o*f o U) ((paid a).smul (w a)) gathered,
        RG.StepData.push_smul _ _ _ _ (paid a),ih]
      rfl
  simpa only [GermGraph.transition,Extra.Histories.blast,pow_zero,one_smul] using step Finset.univ

variable {m k:ℕ} (π:ℕ → Layout G) (Γ:ℕ → Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
    (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
    [MeasurableSpace O] [MeasurableSingletonClass O] (test:Test 3) (χ:Points 3 → O) (measured:Measurable χ)
local notation "w" => WilsonSeparatedOriginalThermometerCells.weight test χ
local notation "cost" u:max => (2+4*(R.family.path.levels.params i).columns)*u
local notation "L" => ((R.family.S.block i).val:ℝ)^(-(1/8:ℝ))

def Returned (y:Site (top)) (h:Coefficient (F₀) (top)) (z:Coefficient (F₀) (bot)) (u B:ℝ):Prop:=
  (z.Format ((sheet).ratio.parent y) R.family.params (Ψ i) ∧
    z.remBound ((sheet).ratio.parent y) (Ψ i) (κ i) u) ∧ (F₀).coeffSize z.x ≤ u ∧
  GermGraph.transition (C:=R.family) 0 N per i (account h (Ψ (i+1))) =
    z.density ((sheet).ratio.parent y) (S₀) (Ψ i) ∧ cost u ≤ L*B

def Integrated (y:O → Site (top)) (B:ℝ) (h:∀o:O,w o≠0 → Coefficient (F₀) (top))
    (z:∀o:O,w o≠0 → Coefficient (F₀) (bot)) (u:∀o:O,w o≠0 → ℝ):Prop :=
    let incoming:=fun o U=>if a:w o≠0 then account (h o a) (Ψ (i+1)) U else 0
    let outgoing:=fun o V=>if a:w o≠0 then (z o a).density ((sheet).ratio.parent (y o)) (S₀) (Ψ i) V else 0
    let fare:=fun o=>if a:w o≠0 then cost (u o a) else 0
    GermGraph.transition (C:=R.family) 0 N per i (fun U=>test.applyTo (fun x=>incoming (χ x) U)) =
       (fun V=>test.applyTo (fun x=>outgoing (χ x) V)) ∧
    (∑o,‖w o‖*fare o) ≤ (∫x:Points 3,‖test x‖)*(L*|B|)

include course measured in
theorem original (begun:m ≤ i+1) (live:i+1 ≤ N) (y:O → Site (top)) (B:ℝ)
    (h:∀o:O,w o≠0 → Coefficient (F₀) (top))
    (fit:∀o a,(h o a).Format (y o) R.family.params (Ψ (i+1)))
    (income:∀o a,(h o a).remBound (y o) (Ψ (i+1)) (κ (i+1)) B)
    (z:∀o:O,w o≠0 → Coefficient (F₀) (bot)) (u:∀o:O,w o≠0 → ℝ)
    (posted:∀o a,Returned (N:=N) R Ψ (y o) (h o a) (z o a) (u o a) B) :
    Integrated (N:=N) R Ψ test χ y B h z u :=by
  let incoming:=fun o U=>if a:w o≠0 then account (h o a) (Ψ (i+1)) U else 0
  let outgoing:=fun o V=>if a:w o≠0 then (z o a).density ((sheet).ratio.parent (y o)) (S₀) (Ψ i) V else 0
  let fare:=fun o=>if a:w o≠0 then cost (u o a) else 0
  have integrable (o:O):Integrable (incoming o) (prior G (top)):=by
    by_cases a:w o≠0
    · simpa only [incoming,dif_pos a] using (WilsonMeasuredOwnerIntegrable.original R π Γ Ψ course begun live
        (S₀) R.family.params (y o) (h o a) (fit o a) (income o a))
    · simp only [incoming,dif_neg a];simp
  have responds (o:O):GermGraph.transition (C:=R.family) 0 N per i (incoming o)=outgoing o:=by
    by_cases a:w o≠0
    · simpa only [incoming,outgoing,dif_pos a] using (posted o a).2.2.1
    · funext V
      simp only [incoming,outgoing,dif_neg a,GermGraph.transition,Extra.Histories.blast,pow_zero,one_smul,RG.StepData.push]
      simp
  have rate:0 ≤ L:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have nonneg:0 ≤ L*|B|:=mul_nonneg rate (abs_nonneg _)
  constructor
  · have fromSource:(fun U=>test.applyTo (fun x=>incoming (χ x) U))=fun U=>∑o,w o*incoming o U:=
      funext (fun U=>WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>incoming o U))
    change GermGraph.transition (C:=R.family) 0 N per i (fun U=>test.applyTo (fun x=>incoming (χ x) U))=
      fun V=>test.applyTo (fun x=>outgoing (χ x) V)
    rw [fromSource,linear R w incoming integrable]
    funext V
    rw [WilsonSeparatedOriginalThermometerCells.tested test χ measured (fun o=>outgoing o V)]
    simp only [responds]
  · change (∑o,‖w o‖*fare o) ≤ _
    calc
      _ ≤ ∑o:O,‖w o‖*(L*|B|):=Finset.sum_le_sum (fun o _=>mul_le_mul_of_nonneg_left (by
        by_cases a:w o≠0
        · simpa only [fare,dif_pos a] using ((posted o a).2.2.2.trans (mul_le_mul_of_nonneg_left (le_abs_self B) rate))
        · simpa only [fare,dif_neg a] using nonneg) (norm_nonneg _))
      _ = (∑o:O,‖w o‖)*(L*|B|):= (Finset.sum_mul ..).symm
      _ ≤ _:=mul_le_mul_of_nonneg_right (WilsonSeparatedOriginalThermometerCells.variation test χ measured) nonneg

end YM.Integration.WilsonReceivedCompactPlacedStep
