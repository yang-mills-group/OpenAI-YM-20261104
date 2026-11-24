import YM.Integration.QLocalOriginalQHistory
import YM.Integration.WilsonReportingPrescribedOldSource
import YM.Integration.WilsonReportingPrescribedOldHolding

/-! The chronological independent Q source inside a genuinely enrolled nonbare old holding. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReportingPrescribedOldHistory

open Lattice Wilson RG Marker Precision Source LocalComparison LocalComparison.Global
open PhysicalNext.Repeat.Legato FullQLocal FullQLocal.RenderedStep FullQLocal.RenderedStep.Numeric
open ComparisonDensity.Address Comparison.RG02 FullQLocal.PreRun.SuccessiveRequests WilsonLimitConstruction
open MergeProof MergeProof.Accent MergeProof.Replicums RG3.Held RG3.Script.Picnic
open Extraction Table Spec RG17 MS MS.Menus MS.Local.Physical
open scoped Classical BigOperators

variable {G : Gauge} (R : Run G) {f : Extraction.Order} {S : Table R.family.book}
  (F₀ : Spec.Final R.family f S) (L : Layout F₀) {B : Deck G}
  {V : Type} [DecidableEq V] [Fintype V] [Nonempty V] (Q : MS.Land.Prescription B)
  (u : V → MS.Rake.Label B)

def entered {n m N per : ℕ} {hn : n ≤ m} (r : ℝ) (atDate : m = L.level r)
    (D : ActualRunQlocalNativeTuple.Datum R per m n hn V) (μ : ℝ) (ks : V → ℕ)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D)) :
    Config G (R.family.side m per) → Poly (Stock.census V) := by
  subst m
  exact birth (Stock.census V) (R.family.path.rep N per (L.level r))
    (fun i W => ActualRunQlocalNativeTuple.reader D i (x i) *
      WilsonReportingPrescribedOldSource.column R F₀ L Q (u i) μ (ks i) r N per
        (ActualRunQlocalNativeTuple.root D i) W)

private theorem enrolled (hG : G.Simple) {n m N per : ℕ} {hn : n ≤ m} (r : ℝ) (hr : 0 < r)
    (atDate : m = L.level r) (D : ActualRunQlocalNativeTuple.Datum R per m n hn V) (μ : ℝ) (ks : V → ℕ)
    (x : TestSpace (ActualRunQlocalNativeTuple.orbit D))
    (age : ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ m) (upper : m ≤ N) :
    ((ActualOriginalQInput.input Q D u μ ks hG N upper).leaf x).density =
      entered R F₀ L Q u (N:=N) r atDate D μ ks x := by
  subst m
  funext U
  exact WilsonReportingPrescribedOldSource.original R F₀ L Q hG u μ ks r hr N per D age upper x U

def calendar {m p q : ℕ} (eq : p = q) (Y : Config G (R.family.side m q) → Poly (Stock.census V)) :
    Config G (R.family.side m p) → Poly (Stock.census V) := eq.symm ▸ Y

omit [Nonempty V] in
private theorem calendar_eq {m p q : ℕ} (eq : p = q) (Y : Config G (R.family.side m q) → Poly (Stock.census V)) :
    HEq Y (calendar R eq Y) := by
  subst q
  rfl

open private scaled from YM.Integration.QLocalOriginalQHistory

variable (hG : G.Simple) (J₀ : Request V) (A₀ : NumericSchedule R.family J₀)
    (d₀ : LocalFormal.Datum R.family (Stock.census V))
    (o : V → Site (R.family.side (d₀.level+1) d₀.period)) (μ : ℝ) (ks : V → ℕ)
    {J : Request V} {d : LocalFormal.Datum R.family (Stock.census V)}
    {A : NumericSchedule R.family J} {F : AnalyticInput J A d}
    {η : ℝ} (I : FullPreparedInputAt F η)

local notation "norm" => ActualOriginalQInitialInput.normalizer R hG u J₀ A₀ d₀ Q o μ ks
local notation "pt" => ActualOriginalQPointSetup.pointDatum R J₀ d₀.period (d₀.level+1) o
local notation "g₁" => Pert.Asymptotics.regulatorRun R.family d.cutoff d.period (d.level+1)

/-- The birth field in the selected physical history, using its native
test normalization, original cutoff/period and all marked coordinates together. -/
theorem received
    (origin : QLocalOriginalQHistory.Origin R hG u J₀ A₀ d₀ Q o μ ks I)
    (r : ℝ) (hr : 0 < r) (atDate : d₀.level+1 = L.level r)
    (age : ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ d₀.level+1)
    (t : TestSpace J.tests) (t₀ : TestSpace (ActualOriginalQPointSetup.request R u J₀).tests)
    (test : HEq t t₀) :
    let x := VariableScaling.tests (fun _ => (norm : ℂ)) t
    let amp := entered R F₀ L Q u (N:=d₀.cutoff) r atDate pt (μ-R.family.S.scale d₀.cutoff) ks t₀
    ∃ source : TestSpace J.tests → Config G (R.family.side (d₀.level+1) d.period) → Poly (Stock.census V),
      QLocalReceivedWilsonState.State I (d₀.level+1) source ∧ source x = calendar R origin.period amp := by
  dsimp only
  obtain ⟨source, state, same⟩ := origin.replay
  let a : V → ℂ := fun _ => (norm : ℂ)
  have identification := same _ _ (scaled origin.tests a test)
  have restored := funext (QLocalOriginalQEnvelope.original R hG u J₀ A₀ d₀ Q o μ ks t₀)
  have filed := enrolled R F₀ L Q u hG r hr atDate pt (μ-R.family.S.scale d₀.cutoff)
    ks t₀ age d₀.below
  have calibrated := identification.trans ((heq_of_eq restored).trans (heq_of_eq filed))
  have rebased := eq_of_heq (calibrated.trans (calendar_eq R origin.period _))
  exact ⟨source,state,rebased⟩

/-- For the actual originated chronological input on the nonbare angular carrier,
the full old field equals the original joint Wilson descent of the independently
prescribed, physically filed, corrected columns. The two rebookings are explicit. -/
theorem original
    (origin : QLocalOriginalQHistory.Origin R hG u J₀ A₀ d₀ Q o μ ks I)
    (hi : Retained.NativeIntake I) (r : ℝ) (hr : 0 < r) (atDate : d₀.level+1 = L.level r)
    (age : ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ d₀.level+1)
    (t : TestSpace J.tests) (t₀ : TestSpace (ActualOriginalQPointSetup.request R u J₀).tests)
    (test : HEq t t₀) :
    let x := VariableScaling.tests (fun _ => (norm : ℂ)) t
    let amp := entered R F₀ L Q u (N:=d₀.cutoff) r atDate pt (μ-R.family.S.scale d₀.cutoff) ks t₀
    ∃ live : d.level+1 ≤ d₀.level+1, ∀ U,
      WilsonReportingPrescribedOldHolding.retained R A d F I x U =
        (Real.exp (I.calibration.amount U) : ℂ) • (Poly.pass (-(F.packets.read x g₁ U)) *
          gust R.family.path d.cutoff d.period (d₀.level+1) (calendar R origin.period amp)
            (d.level+1) live U) := by
  dsimp only
  obtain ⟨source,state,rebased⟩ :=
    received R F₀ L Q u hG J₀ A₀ d₀ o μ ks I origin r hr atDate age t t₀ test
  refine ⟨state.before, fun U => ?_⟩
  rw [WilsonReportingPrescribedOldHolding.original R A d F I hi, state.current, rebased]

/-- The complete output on the actual next Wilson field. Every partial
derivative and every old hard term is still inside this single descent. -/
theorem output
    (origin : QLocalOriginalQHistory.Origin R hG u J₀ A₀ d₀ Q o μ ks I)
    (M : FundedRenderedBank.Catalogue J d) (S : FundedRenderedBank.Bank I M)
    (r : ℝ) (hr : 0 < r) (atDate : d₀.level+1 = L.level r)
    (age : ∀ s : ActualOriginalQReaders.Slot u, R.family.ref s.2.size ≤ d₀.level+1)
    (t : TestSpace J.tests) (t₀ : TestSpace (ActualOriginalQPointSetup.request R u J₀).tests)
    (test : HEq t t₀) :
    let x := VariableScaling.tests (fun _ => (norm : ℂ)) t
    let amp := entered R F₀ L Q u (N:=d₀.cutoff) r atDate pt (μ-R.family.S.scale d₀.cutoff) ks t₀
    ∃ before : d.level ≤ d₀.level+1, (S.output.output.leaf x).density =
      gust R.family.path d.cutoff d.period (d₀.level+1) (calendar R origin.period amp) d.level before := by
  dsimp only
  obtain ⟨source,state,rebased⟩ :=
    received R F₀ L Q u hG J₀ A₀ d₀ o μ ks I origin r hr atDate age t t₀ test
  refine ⟨(Nat.le_succ _).trans state.before,?_⟩
  rw [QLocalReceivedWilsonState.output state M S,rebased]

end YM.Integration.WilsonReportingPrescribedOldHistory
