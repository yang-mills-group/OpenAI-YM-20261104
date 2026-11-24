import YM.Integration.WilsonSpectatorReadout
import YM.RG02.Actual.Selected

/-! Reflection of the actual normalized signed Wilson spectator. There is
one physical density outside the product and the original density divisor
at each of its genuine chamber factors. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSpectatorReflection

open Function Set Filter Finset MeasureTheory Lattice Wilson RG Marker Source Labels Cells
open Extra.Histories Relay Bid RG3.Script.Picnic RG3.Forms
open Comparison.RG02 LocalComparison LocalComparison.Global FullQLocal FullQLocal.RenderedStep
open FullQLocal.RenderedStep.Numeric FullQLocal.RenderedStep.Numeric.Retained
open Trace.Physical Trace.Physical.GermGraph PhysicalNext.Repeat.Legato OPE.Therm
open ActualWilsonAxisSpectator WilsonSpectatorReadout
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side}

private theorem reflected_envelope (T : Tiling n) (f : T.Cell → Config G n → ℂ)
    (hf : ∀ i, Envelope (f i)) : Envelope (T.fullAt f) := by
  exact Envelope.prodC Finset.univ (fun i => T.copy i (f i))
    (fun i _ => Push.GridApprox.replica_env T i (hf i))

variable (R : Run G) (hG : G.Simple)
    {V : Type} [Fintype V] [DecidableEq V] {B : Census V} {J : Request V}
    {A : NumericSchedule R.family J} {datum : LocalFormal.Datum R.family B}
    {caps : Handoff.OutputCapacities} {Y : Bulk.Chain R.family.path} {K : NumericPrices A}
    {F : AnalyticInput J A datum} {eta : ℝ} {I : FullPreparedInputAt F eta}
    {M : AnalyticOutput caps Y K F} {δ : ℝ} {a : ℕ}

local notation "W" => R.family.path.rep datum.cutoff datum.period datum.level
local notation "n₀" => R.family.side datum.level datum.period
local notation "μ₀" => prior G n₀
local notation "π₀" => scene R.family.path datum.cutoff datum.period datum.level
local notation "Z₀" => partition G (R.family.side datum.cutoff datum.period)
  (R.family.path.β datum.cutoff datum.period datum.cutoff)

/-- Every physical coarse field has a positive native denominator. Its
reciprocal is bounded at fixed volume. -/
theorem denominator (N p m : ℕ) (hm : m < N) :
    let Q := R.family.path.rep N p m
    let z := partition G (R.family.side N p) (R.family.beta N p)
    let L := SectorNext.Vacuum.wires (R.family.side m p) *
      (2*SectorNext.Vacuum.kick (R.family.path.levels.clock.op m p) (R.family.path.rep N p (m+1)).beta)
    ∀ U, 0 < Q.eval U ∧ (Q.eval U)⁻¹ ≤ Real.exp L / z := by
  intro Q z L U
  have h := RG02.Actual.den_floor R.makes.wilson (p:=p) hm U
  rw [RG02.Actual.den_eval R.makes.wilson hm U] at h
  have hpos := RG02.Actual.eval_pos R.makes.wilson hm.le U
  refine ⟨hpos,?_⟩
  have hz : 0 < z := partition_pos _
  have ha : Real.exp (-L) * z ≤ Q.eval U := h
  have hh := inv_anti₀ (mul_pos (Real.exp_pos _) hz) ha
  simpa only [mul_inv_rev,←Real.exp_neg,neg_neg,div_eq_inv_mul] using hh

/-- An envelope for the actual normalized insertion on every finite run,
including every original dirty configuration. -/
theorem normalized_envelope (S : Chosen K I M) (H : Bounds S δ a)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (x : IndependentTests J.tests) (v : V) :
    Envelope (normalized R hG S x v) := by
  have hW := (R.makes.wilson.represents datum.cutoff datum.period datum.level datum.below.le).good
  let c := forcedDivisor R.family datum.level * (F.kernelCosts v *
    (Pert.Asymptotics.regulatorRun R.family datum.cutoff datum.period (datum.level+1)) ^ a / F.outputRadii v)
  have he := ((ActualSelectedModelEnvelope.chosen_exponent_envelope R.makes S).exp.add
    ((W).exponentEnv hW).exp).mul (Envelope.const c)
  obtain ⟨b,hb⟩ := he.cost
  have hspec : Envelope (spectator R hG S x v) := by
    refine ⟨WilsonSpectatorReadout.measurable R hG S H x v hreserve,b,fun U => ?_⟩
    exact (ActualWilsonSpectatorBudget.selected R hG S H hLate hreserve x v U).2.trans
      ((le_abs_self _).trans (hb U))
  have hcont := Complex.continuous_ofReal.comp
    (RG02.Actual.eval_cont R.makes.wilson (N:=datum.cutoff) (p:=datum.period) datum.below.le)
  have hinv : Continuous (fun U => ((W).eval U : ℂ)⁻¹) :=
    hcont.inv₀ (fun U => Complex.ofReal_ne_zero.mpr (RG02.Actual.eval_pos R.makes.wilson datum.below.le U).ne')
  exact WardBin.bound_product (WardBin.envelope_continuous hinv) hspec

private theorem full_density {N p m : ℕ} (hm : m ≤ N) (T : Tiling (R.family.side m p))
    (f : T.Cell → Config G (R.family.side m p) → ℂ) (U : Config G (R.family.side m p)) :
    let Q := R.family.path.rep N p m
    T.fullAt (fun i A => (Q.eval A : ℂ)⁻¹ * f i A) U =
      ((Q.eval U : ℂ)⁻¹)^Fintype.card T.Cell * T.fullAt f U := by
  intro Q
  have h (i : T.Cell) : T.copy i (fun A => (Q.eval A : ℂ)⁻¹ * f i A) U =
      (Q.eval U : ℂ)⁻¹ * T.copy i (f i) U := by
    have ht := WardBin.Wheels.rep_spins (T.omega i) R.makes.wilson hm U (T.translateBy i)
    change Q.eval (pull _ _ U) = Q.eval U at ht
    by_cases hh : T.hand i
    · simp [Tiling.copy,hh,ht,mul_comm]
    simp [Tiling.copy,hh,ht]
  simp only [Tiling.fullAt,h,Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ]

/-- The reflected word of the exact signed normalized insertions is
integrable on the original physical Wilson scene. Clearing its denominators
leaves one copy of the actual vacuum over the original fine partition. -/
theorem reflected (S : Chosen K I M) (H : Bounds S δ a)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (T : Tiling n₀) (x : T.Cell → IndependentTests J.tests) (v : T.Cell → V) :
    let f := fun i => normalized R hG S (x i) (v i)
    let d := fun i => spectator R hG S (x i) (v i)
    Integrable (T.fullAt f) π₀ ∧
      (∫ U, T.fullAt f U ∂π₀) = (Z₀ : ℂ)⁻¹ * ∫ U,
        ((W).eval U : ℂ) * ((((W).eval U : ℂ)⁻¹)^Fintype.card T.Cell * T.fullAt d U) ∂μ₀ := by
  intro f d
  letI : IsProbabilityMeasure π₀ := probability (H:=R.family.path) (p:=datum.period) R.makes.wilson datum.below.le
  refine ⟨(reflected_envelope T f (fun i => normalized_envelope R hG S H hLate hreserve (x i) (v i))).integrableC _,?_⟩
  rw [violet (H:=R.family.path) (p:=datum.period) R.makes.wilson datum.below.le,div_eq_inv_mul]
  congr 1
  apply integral_congr_ae
  exact Eventually.of_forall fun U => congrArg (fun z => ((W).eval U : ℂ) * z)
    (full_density R datum.below.le T d U)

/-- If the actual normalized spectator is a local test in the indicated
window, the native Wilson reflection inequality compares its singleton
with the entire reflected word on the same run. -/
theorem singleton (S : Chosen K I M) (H : Bounds S δ a)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    {k : ℕ} (hk : k ≤ datum.level) (d : ℕ) (x : IndependentTests J.tests) (v : V)
    (hi : Interior (Push.GridApprox.window 0 d) (normalized R hG S x v))
    (hr : Push.GridApprox.room R.family.path.levels k datum.level d) :
    let T := Push.GridApprox.tilesAt R.family.S datum.period hk
    ‖(Z₀ : ℂ)⁻¹ * ∫ U, spectator R hG S x v U ∂μ₀‖ ^ Fintype.card T.Cell ≤
      ‖(Z₀ : ℂ)⁻¹ * ∫ U,
        ((W).eval U : ℂ) * ((((W).eval U : ℂ)⁻¹)^Fintype.card T.Cell *
          T.fullAt (fun _ => spectator R hG S x v) U) ∂μ₀‖ := by
  intro T
  have h := repeated R.makes.wilson hk datum.below.le (normalized R hG S x v) d hi hr
  have hsingle := projection R hG S x v (fun _ => 1)
  simp only [one_mul] at hsingle
  rw [←hsingle, ← (reflected R hG S H hLate hreserve T (fun _ => x) (fun _ => v)).2]
  exact h

private theorem fine_scene {N p m : ℕ} (hm : m ≤ N) (f : Config G (R.family.side m p) → ℂ)
    (hf : Envelope f) :
    R.family.omega N p (Push.GridApprox.backTo R.family.path N p hm f) =
      ∫ U, f U ∂scene R.family.path N p m := by
  have hi : Integrable (Push.GridApprox.backTo R.family.path N p hm f)
      (law G (R.family.side N p) (R.family.beta N p)) :=
    (Push.GridApprox.backTo_env R.family.path N p hm hf).integrableC _
  exact (onstage (H:=R.family.path) (p:=p) R.makes.wilson _ hi).symm.trans
    (retro (H:=R.family.path) (p:=p) R.makes.wilson hm le_rfl f hf)

/-- The true fine Wilson moment of the iterated native transfer of the
tested normalized spectator equals its signed Haar numerator divided by
the original fine partition. -/
theorem physical_projection (S : Chosen K I M) (H : Bounds S δ a)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (x : IndependentTests J.tests) (v : V) (φ : Config G n₀ → ℂ) (hφ : Envelope φ) :
    R.family.omega datum.cutoff datum.period
      (Push.GridApprox.backTo R.family.path datum.cutoff datum.period datum.below.le
        (fun U => φ U * normalized R hG S x v U)) =
      (Z₀ : ℂ)⁻¹ * ∫ U, φ U * spectator R hG S x v U ∂μ₀ :=
  (fine_scene R datum.below.le _ (hφ.mulC (normalized_envelope R hG S H hLate hreserve x v))).trans
    (projection R hG S x v φ)

/-- The native transfer of the full reflected word has the same original
cutoff Wilson moment as the coarse formula with its original divisors. -/
theorem physical_reflection (S : Chosen K I M) (H : Bounds S δ a)
    (hLate : ActualSelectedCofactorFunding.start R.family hG R.makes (Fintype.card V) ≤ datum.level)
    (hreserve : (R.family.path.levels.budget datum.level).supportExponent ≤ J.outputSupport)
    (T : Tiling n₀) (x : T.Cell → IndependentTests J.tests) (v : T.Cell → V) :
    let f := fun i => normalized R hG S (x i) (v i)
    let d := fun i => spectator R hG S (x i) (v i)
    R.family.omega datum.cutoff datum.period
      (Push.GridApprox.backTo R.family.path datum.cutoff datum.period datum.below.le (T.fullAt f)) =
      (Z₀ : ℂ)⁻¹ * ∫ U, ((W).eval U : ℂ) *
        ((((W).eval U : ℂ)⁻¹)^Fintype.card T.Cell * T.fullAt d U) ∂μ₀ := by
  intro f d
  exact (fine_scene R datum.below.le _ (reflected_envelope T f
    (fun i => normalized_envelope R hG S H hLate hreserve (x i) (v i)))).trans
    (reflected R hG S H hLate hreserve T x v).2

end YM.Integration.WilsonSpectatorReflection
