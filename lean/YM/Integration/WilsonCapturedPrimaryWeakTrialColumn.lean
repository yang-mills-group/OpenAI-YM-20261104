import YM.Integration.WilsonCapturedPrimaryWeakTrialEngineering

/-! The clockface estimator and the intrinsic projected page are read on the
same returned trial. Only the former uses a finite inverse of tile values. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
noncomputable section
namespace YM.Integration.WilsonCapturedPrimaryWeakTrialColumn
open Function Finset Filter MeasureTheory Lattice Wilson RG Marker QuadraticLocal Ac Source Labels
open PhysicalNext PhysicalNext.Repeat Legato Org AllOrder AllOrder.Floe AllOrder.Floe.Step
open AllOrder.Floe.Step.PlanV AllOrder.Transit WheelP AnalyticBridge VerifiedReset
open Pressure ConnectedActivityE6 Push.AbsoluteSums MergeProof.Accent QuadraticLocal.Advent
open QuadraticLocal.Earn QuadraticLocal.Affinity Push Push.Local Push.PriceCompiler RemainderComparison Tree
open WilsonPhysicalMarkedDefect.RegularProjection WilsonMeasuredCoefficientTransport
open WilsonReceivedQuietCrownOwner OPE.Therm Multi Push.AbsoluteSums.Animals
open WilsonRootedKioskOccupiedSlip WilsonOriginalOrdinaryFlatHulls Comparison.Density.Transport
open Extra.Histories Extra.Multi WilsonOriginalNullPlacedGermMap WilsonOriginalNullCorridor
open RG17 Next.Rank.Spindle Trace.Physical Trace.Physical.Germ Trace.Physical.GermGraph
open WilsonCapturedPrimaryWeakTileColumn WilsonCapturedPrimaryReading WilsonOriginalMicroscopicGuardedTrial
open WilsonPositionProgramOriginalBlockedTrial WilsonPositionProgramBlockedTrialAddBack
open WilsonCapturedPrimaryWeakTrialEngineering WilsonPositionProgramBlockedTrialNodes
open scoped BigOperators Classical
variable {G : Gauge} (R : Run G)
local notation "Fr" => R.family.labels.level 4
local notation "Sec" => R.family.localSection 4

def failure (N per b p : ℕ) (α tol : ℝ) (v : R.family.label 4) : ℝ :=
  let rent := 2 * (‖v 0‖ + BasisCost.price Sec * (Fr).coeffSize (names R 4 N per b v))
  rent * (((Sec).footprint (0 : Site (R.family.side b per))).card : ℝ) *
    (4 * Real.exp (α+2)) * tol / R.alloy.B.a.clock.hatBeta b ^ p

def full (N per i n : ℕ) (w : R.family.label 4) (U : Config G (R.family.side i per)) : ℂ :=
  gain R 4 i n * actualTransport R.family (N:=N) (uncut R 4 N per (i+n) 0 w) (Nat.le_add_right i n) U

def Registered {N per i n : ℕ} (live : i+n ≤ N) (D : ClockFace R 4 i N per) (target : ℕ)
    (e w : R.family.label 4) (q : Coefficient (Fr) (R.family.side i per)) (δ : ℝ) : Prop :=
  let W := R.family.path.rep N per i
  let read := reading Sec W 0 q
  q.Format 0 R.family.params W ∧
  q.remBound 0 W (safety R.family i) (2 * stock R.family i * (Fr).coeffSize e) ∧
  q.density 0 Sec W = carried R 4 (p:=per) live 0 w ∧
  projection (Fr) R.family.params W.p.threshold 0 q = e ∧ Invoice R 4 N per i target e q ∧
  (∀ V, read V = gain R 4 i n * actualTransport R.family (N:=N)
    (fun U => part Sec 0 (R.family.path.rep N per (i+n)) U w) (Nat.le_add_right i n) V) ∧
  (∀ a, watchman R 4 i N per (column R D read) (D.tiles a) = read (node R D a) ∧
    ‖full R N per i n w (node R D a) - read (node R D a)‖ ≤ ‖gain R 4 i n‖*(2*δ)) ∧
  paid R.family 4 i N per (column R D (full R N per i n w) - column R D read) ≤
    44*(R.family.path.levels.clock.hatBeta i)^27*(‖gain R 4 i n‖*(2*δ))

variable {N per m k i n : ℕ} (π : ℕ → Layout G) (Γ : ℕ → Pace.Coin)
  (Ψ : ∀ j, RG.Rep G (R.family.side j per)) (course : Concourse R.alloy R.kit R.T π Γ m N per k Ψ)
  {d : ℕ} {F : Frame G d} (S : SectionData F) (A : Hol G)
  (simple : G.Simple) (way : WayStation R.kit) (D : Roots (G:=G) R.metals.p.profile R.metals.K R.metals.p.kernel)
  (Q : D.Tab R.rolls) (ticket : TicketP R.alloy R.kit D Q) {u : ℕ} (floor : m ≤ u)
  (fixed : WilsonSingleHardRadius.first R simple ≤ u)

include course floor fixed way ticket S A in
theorem original (columns : ∀ᶠ j in atTop, (R.family.path.levels.params j).columns ≤
    R.family.path.levels.clock.hatBeta j) (shop : RG05Preconstruction.ReadoutPurchase R.b)
    (wide : ∀ j, 1 ≤ (R.family.path.levels.budget j).supportExponent)
    (target p : ℕ) {η tol : ℝ} (ep : 0 < η) (tp : 0 < tol)
    (ui : u ≤ i) (ib : i+1 ≤ i+n) (cut : i+n < N)
    (capture : WilsonCenteredCaptureClock.first R simple ≤ i+n)
    (late : (eventually_atTop.mp (WilsonOriginalFlatHaloRate.calendar R simple p tp)).choose ≤ i+n)
    (stage : (eventually_atTop.mp ((WilsonCapturedPrimaryWeakTileColumn.four R simple columns).and
      (WilsonOriginalClockFacePosterior.original R simple))).choose ≤ i)
    (trial : (eventually_atTop.mp (WilsonPositionProgramBlockedTrialNodes.original R 4 simple
      shop wide target ep)).choose ≤ i) (D₄ : ClockFace R 4 i N per) :
    ∃ J : R.family.label 4 ≃ₗ[ℂ] R.family.label 4, ∀ e : R.family.label 4, let w := J.symm e
      (Fr).coeffSize w ≤ 2*Real.exp (η*(R.family.S.scale (i+n)-R.family.S.scale i))*(Fr).coeffSize e ∧
      ∃ q, Registered R cut.le D₄ target e w q (failure R N per (i+n) p (Ψ (i+n)).p.supportExponent tol w) := by
  obtain ⟨J,issued⟩ := (eventually_atTop.mp (WilsonPositionProgramBlockedTrialNodes.original R 4 simple
    shop wide target ep)).choose_spec i trial N per n cut.le (ib.trans cut.le)
  refine ⟨J,?_⟩
  intro e w
  obtain ⟨salary,q,shape,rem,word,projection,invoice⟩ := issued e
  let W := R.family.path.rep N per i
  let δ := failure R N per (i+n) p (Ψ (i+n)).p.supportExponent tol w
  let read := reading Sec W 0 q
  have exactRead (V) : read V = gain R 4 i n * actualTransport R.family (N:=N)
      (fun U => part Sec 0 (R.family.path.rep N per (i+n)) U w) (Nat.le_add_right i n) V := by
    dsimp only [read,reading]
    rw [word,div_eq_mul_inv,mul_comm]
    exact WilsonCapturedPrimaryWeakTrialEngineering.normalized R 4 N per i cut.le 0 w V
  have hear := WilsonCapturedPrimaryGuardedWeakTrial.original R π Γ Ψ course cut S A simple way D Q ticket
    floor (ui.trans (Nat.le_add_right i n)) fixed columns capture p tp late (fun _ => 4) (fun _ => 0)
    (fun _ => w) {0} ui ib D₄ stage
  have oneFace {X : Type} (F : Fin 3 → X → ℂ) : WilsonOriginalMicroscopicGuardedTrial.face F {0} = F 0 := by
    funext U
    simp [WilsonOriginalMicroscopicGuardedTrial.face]
  have guardEq : WilsonOriginalMicroscopicGuardedTrial.guarded R (fun _ => 4) N per (i+n) (fun _ => 0) (fun _ => w) 0 = (fun U => part Sec 0 (R.family.path.rep N per (i+n)) U w) := by rfl
  have baseline (a) : ‖actualTransport R.family (N:=N) (uncut R 4 N per (i+n) 0 w)
      (Nat.le_add_right i n) (node R D₄ a) - actualTransport R.family (N:=N)
      (fun U => part Sec 0 (R.family.path.rep N per (i+n)) U w) (Nat.le_add_right i n) (node R D₄ a)‖ ≤ 2*δ := by
    simpa [oneFace,guardEq,WilsonOriginalMicroscopicGuardedTrial.raw,footprint,cap,δ,failure] using hear.2.1 a
  have nodes (a) : ‖full R N per i n w (node R D₄ a) - read (node R D₄ a)‖ ≤ ‖gain R 4 i n‖*(2*δ) := by
    rw [full,exactRead,←mul_sub,norm_mul]
    exact mul_le_mul_of_nonneg_left (baseline a) (norm_nonneg _)
  have fitted := ((eventually_atTop.mp ((WilsonCapturedPrimaryWeakTileColumn.four R simple columns).and
    (WilsonOriginalClockFacePosterior.original R simple))).choose_spec i stage).1 ((Nat.le_add_right i n).trans cut.le) D₄
  exact ⟨salary,q,shape,rem,word,projection,invoice,exactRead,
    fun a => ⟨WilsonCapturedPrimaryWeakTileColumn.registered R D₄ read a,nodes a⟩,
    fitted _ _ _ nodes⟩

end YM.Integration.WilsonCapturedPrimaryWeakTrialColumn
