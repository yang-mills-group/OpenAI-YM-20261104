import YM.Integration.FullQLocalFullPreparedInputAt
import YM.Integration.RunFormalChain
import YM.Comparison.RG02.Step.History

/-! The complete marked conditional logarithm of the analytic incoming source
on every interior step in the actual Wilson history.  The native integrated
error retains its included and exceptional sectors on the identical marked
measure. The formal polynomial is the independent full Wick prescription. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.ManuscriptQLocalActualLog
open Filter Function Finset MeasureTheory Lattice Wilson RG Precision Marker Multi Exterior Tree
open RG3.Script.Picnic LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric PhysicalNext.Repeat.Legato Comparison.RG02 Integral
open Actual Order Next.SectorChange Push.SectorMeasure
open scoped BigOperators Classical Topology ContDiff Matrix.Norms.Frobenius

variable {G : Gauge} {V : Type} [DecidableEq V] [Fintype V] {Γ : Census V}
    (R : Run G) {J : Request V} {A : NumericSchedule R.family J}
    (d : LocalFormal.Datum R.family Γ) (F : AnalyticInput J A d)
    (x : TestSpace J.tests)
local notation "P" => R.family.path.rep d.cutoff d.period (d.level+1)
local notation "P₀" => R.family.path.rep d.cutoff d.period d.level
local notation "Δ" => R.family.path.levels.clock.op d.level d.period
local notation "g" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)
local notation "W" => F.colors x
local notation "Y" => RunFormalChain.fromRun R
local notation "K" => d.kernel Y

/-- The full unnormalized joint polynomial of the analytic marks on the
actual physical incoming vacuum, retaining every global marked constant. -/
def source (U : Config G (R.family.side (d.level+1) d.period)) : Poly Γ :=
  ((P).eval U : ℂ) • Poly.pass (Integral.markedLog g U (W))

theorem literal (U : Config G (R.family.side (d.level+1) d.period)) :
    source R d F x U = ((P).eval U : ℂ) • Poly.pass (F.packets.read x g U) := by
  rw [source,F.convention.marks x g
    (Local.RealStep.coupling_pos R.family d.cutoff d.period (d.level+1) R.makes d.below).ne' U]

theorem floor : Actual.Floor P (source R d F x) := by
  have ht := Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below
  have hw := F.convention.well x
  refine ⟨fun U => ?_,?_,?_⟩
  · rw [source,Poly.part_smul,Integral.markedLog,Poly.pass_part _ (part_lit_quiet _),mul_one]
  · apply Leaf.smul ht.safe.ofReal_env
    exact Leaf.sum _ _ (fun i => Leaf.smul (Leaf.atom _) (Leaf.pow (Integral.leaf_mark g (W) hw) i))
  · intro k U
    have hP : (P).eval (gauge k U) = (P).eval U :=
      Presented.lawful_gi (R.makes.wilson.represents d.cutoff d.period (d.level+1) d.below).good k U
    simp only [source,hP,Integral.markedLog,show ∀ i,(W).mark i g (gauge k U)=(W).mark i g U from fun i => hw.gauges i g k U]

theorem input (U : Config G (R.family.side (d.level+1) d.period)) :
    Actual.errorLog (source R d F x) (W) U g P = 0 := by
  have hp := (Normal.actual R.family.path R.makes.wilson d.cutoff d.period (d.level+1) d.below).positive U
  rw [Actual.errorLog,Actual.markWeight,source,smul_smul,inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hp.ne'),
    one_smul,Integral.markedLog,Cumulants.connected_pass (part_lit_quiet _),sub_self]

/-- Preserve the original rough/forced remainder of the full prepared input
in the same signed polynomial before performing any subsequent physical push. -/
theorem inherited {η : ℝ} (I : FullPreparedInputAt F η)
    (U : Config G (R.family.side (d.level+1) d.period)) :
    (I.input.leaf x).density U-source R d F x U =
      Poly.pass (F.packets.read x g U) * ((I.prepared.remainder.leaf x).density U-
        ((P).eval U : ℂ) • (1:Poly Γ)) := by
  calc
    _ = Poly.pass (F.packets.read x g U) * (I.prepared.remainder.leaf x).density U -
        source R d F x U := congrArg (fun a : Poly Γ => a - source R d F x U) (I.prepared.full x U)
    _ = _ := by rw [literal,mul_sub,mul_smul_comm,mul_one]

variable (B : fieldDir G (R.family.side d.level d.period) 1)
local notation "D" => ({d with colors := W,field := B} : LocalFormal.Datum R.family Γ)
local notation "Z" => fun _ : (Δ).Choices => Integral.zone K (P).p d.forest g B
local notation "v" => Integral.sample g B
local notation "Π" => source R d F x
local notation "err" => Local.markingError P Π K g d.forest d.tag (W) Z B J.order (Fintype.card V)

/-- Every normalized marked coefficient of the true physical quotient and
the explicit signed cutoff discrepancy before the independent field and
mode readings. The quiet normalization is the actual field-dependent one. -/
theorem conditional :
    Local.cumulant P Π Δ v = Order.value (g:ℂ) ((D).markedLog Y J.order) + err ∧
    Actual.Push Δ (P).beta Π v = ((P₀).eval v : ℂ) • (Local.cumulant P Π Δ v).pass := by
  have h := Local.RealStep.genuine R.family d.cutoff d.period d.level Y d.below Π (W)
    d.forest d.tag B R.makes (floor R d F x) (F.convention.well x) J.order (Fintype.card V)
    (fun _ => Finset.card_le_univ _) Z
    (fun _ => (Integral.plausible K d.forest (P).p g B).1) (fun _ => Set.Subset.refl _)
  exact h.2.2

/-- Cancellation on the entire prescribed polynomial jet in the actual
physical coupling convention. The marked constant and every positive
coupling order use the same independent tests and physical denominator. -/
theorem residual {M : MarkedPackets J.tests G (R.family.side d.level d.period) Γ}
    (H : PrescribedPackets Y d F.colors M J.order) :
    Local.cumulant P Π Δ v -
      ∑ k∈range (J.order+1), (g:ℂ)^k •
        (((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k (fun t:ℝ => H.extension x t B) 0 (fun _ => 1)) =
      err := by
  have poly : Order.value (g:ℂ) ((D).markedLog Y J.order) =
      ∑ k∈range (J.order+1), (g:ℂ)^k •
        (((k.factorial:ℝ)⁻¹) • iteratedFDeriv ℝ k (fun t:ℝ => H.extension x t B) 0 (fun _ => 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [H.coefficients x B k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))]
  rw [(conditional R d F x B).1,poly,add_sub_cancel_left]

end YM.Integration.ManuscriptQLocalActualLog
end
