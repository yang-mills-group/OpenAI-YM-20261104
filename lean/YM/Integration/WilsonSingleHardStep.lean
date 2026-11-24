import YM.Integration.WilsonSingleHardRelease
import YM.QuadraticLocal.Tariff.Measure
import YM.Integration.ActualTrajectoryTransport
import YM.MergeProof.Wicket

/-! The physical single-marker exceptional input is heard by the exact same measured
Wilson kernel. Its new exceptional source retains every old quiet partner. -/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.Integration.WilsonSingleHardRadius
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open scoped BigOperators Classical
variable {G:Gauge} (R:Run G) {N per m k i:ℕ}
   (way:WayStation R.kit)
   (D:Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel) (Q:D.Tab R.rolls)
   (ticket:TicketP R.alloy R.kit D Q)
   (π:ℕ→Layout G) (Γ:ℕ→Pace.Coin) (Ψ:∀j,RG.Rep G (R.family.side j per))
   (course:Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
   (floor : m ≤ i) (cut : i < N)
   {T:Type} [Nonempty T] {J:Census (Fin 1)} (o:Fin 1→Site (R.family.side (i+1) per))
local notation "P" => Ψ (i+1)
local notation "lower" => Ψ i
local notation "atRoot" => ((R.family.path.levels.clock.op i per).ratio.parent ∘ o)
local notation "ht" => R.alloy.B.a.clock.hatBeta (i+1)
local notation "fee" => Time.quoteHard R.alloy.B.a i R.kit.book (P).beta
local notation "fire" => J.fire 0
local notation "source" K:max => (gallery K).density

include way ticket course floor cut in
/-- Rooted release and honest successor on the unmodified incoming representation.
The order of the physical or hard test is free after election of the same output. -/
theorem advance (K:Hard T (P).p (P).activities.forced (P).activities.K o J)
    {w:ℝ} (wp:0<w) (paid:K.Paid (fun _=>w) (P).p.B (P).p.supportExponent 1)
    (activated:1≤R.alloy.B.a.clock.J i) (large:1≤ht) :
    ∃ (I:Type) (L:Gallery T I atRoot lower J), Countable I ∧
    L.K.Paid (fun _=>w) (lower).p.B (lower).p.supportExponent fee ∧
    (∀t:T,Integrable ((source K) t) (prior G _)) ∧
    ∀t U,
      (LocalComparison.actualPush R.family N per i ((source K) t) U).part fire=
        ((lower).eval U:ℂ)*(L.E.log t U).part fire+((source L.K) t U).part fire ∧
      w*‖(L.E.log t U).part fire‖≤ht := by
  let X:=gallery K
  have unit:=intake K paid le_rfl
  have arity (s:J.Mode) : s.val.card≤1 := by simpa using card_le_univ s.val
  obtain ⟨I,L,count,receipt,real⟩ :=
    Advent.growth R way D Q π Γ Ψ course ticket floor cut (fun _=>w) (fun _=>wp)
      X unit activated arity
  refine ⟨I,L,count,receipt.wages,?_,?_⟩
  · intro t
    exact QuadraticLocal.Tariff.integrable J o (fun _=>w) (fun _=>wp) X t unit (P).p.exponent_pos.le
      (course.1.walk (i+1) (floor.trans i.le_succ) cut).truep.valid
  · intro t U
    constructor
    · rw [←real t]
      exact release L wp receipt t U
    · have half : Beaming.grain (R.alloy.B.a.clock.J i) ≤1 := by
        unfold Beaming.grain
        apply (div_le_one₀ (by positivity)).mpr
        linarith only [Nat.cast_nonneg (α:=ℝ) (R.alloy.B.a.clock.J i)]
      exact (light L wp receipt t U).trans
        ((min_le_right _ _).trans ((Real.rpow_le_rpow_of_exponent_le large half).trans_eq (Real.rpow_one _)))

/-- Finite measured Wilson marginal of an integrable unnormalized field, tested
against the original vacuum. -/
theorem marginal {j:ℕ} (live:j<N) (F:Config G (R.family.side (j+1) per)→Poly J)
    (integral:Integrable F (prior G _)) (s:J.Mode) (V:Config G (R.family.side j per)) :
    actualAverage R.family (N:=N) (fun U=>((R.family.path.rep N per (j+1)).eval U)⁻¹ • (F U).part s) V
      = ((R.family.path.rep N per j).eval V)⁻¹ • (LocalComparison.actualPush R.family N per j F V).part s := by
  rw [actualAverage_push]
  have strip (U:Config G (R.family.side (j+1) per)) :
      (R.family.path.rep N per (j+1)).eval U •
        (((R.family.path.rep N per (j+1)).eval U)⁻¹ • (F U).part s)=(F U).part s := by
    have pos : (R.family.path.rep N per (j+1)).eval U ≠ 0 := (Multi.AxisShift.chosen_positive R.makes.wilson live U).ne'
    rw [smul_smul,mul_inv_cancel₀ pos,one_smul]
  simp_rw [strip]
  exact congrArg (((R.family.path.rep N per j).eval V)⁻¹ • ·)
    (congrFun (MergeProof.Accent.push_get (R.family.path.levels.transition_mass ..) integral s) V).symm

/-- The error from a previously emitted regular field passes through the same
positive normalized kernel at unchanged supremum cost. -/
theorem difference {j:ℕ} (live:j<N) (F H:Config G (R.family.side (j+1) per)→ℂ)
    (rawF:Integrable F (prior G _)) (rawH:Integrable H (prior G _)) (c:ℝ)
    (price:∀U,‖((R.family.path.rep N per (j+1)).eval U)⁻¹ • F U-
               ((R.family.path.rep N per (j+1)).eval U)⁻¹ • H U‖≤c)
    (V:Config G (R.family.side j per)) :
    ‖actualAverage R.family (N:=N) (fun U=>((R.family.path.rep N per (j+1)).eval U)⁻¹ • F U) V-
      actualAverage R.family (N:=N) (fun U=>((R.family.path.rep N per (j+1)).eval U)⁻¹ • H U) V‖≤c := by
  have f := actualDensityRatio_integrable R.family R.makes live rawF V
  have h := actualDensityRatio_integrable R.family R.makes live rawH V
  unfold actualAverage
  rw [←integral_sub f h]
  simpa only [actualAverage,smul_sub] using (actualAverage_norm_le R.family R.makes live price V)

end YM.Integration.WilsonSingleHardRadius
