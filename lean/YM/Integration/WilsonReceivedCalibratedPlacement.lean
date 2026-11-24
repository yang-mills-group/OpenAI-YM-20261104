import YM.Integration.WilsonReceivedCalibratedTest
import YM.Integration.WilsonOriginalMixedTestTableau

/-! The two enrolled sets of tests at the original calibrated upper intake. -/
set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonReceivedCalibratedPlacement
open Lattice Wilson RG Source Labels Marker LocalComparison LocalComparison.Global RG3.Script.Picnic
open FullQLocal FullQLocal.RenderedStep QuadraticLocal.Affinity PhysicalNext.Repeat.Legato
open scoped Classical

variable {G:Gauge} {B:MS.Local.Physical.Deck G} {V:Type} [DecidableEq V] [Fintype V] [Nonempty V]
  (R:Run G) (simple:G.Simple) (u:V→MS.Rake.Label B)
  (J:Request V) (A:NumericSchedule R.family J)
  (d:LocalFormal.Datum R.family (Stock.census V)) (Q:MS.Land.Prescription B)
  (o:V→Site (R.family.side (d.level+1) d.period)) (μ:ℝ) (orders:V→ℕ)
  {E:V→Type} [∀v,AddCommGroup (E v)]
  (next:∀v,Set (E v)) (neutral:∀v,0∈next v) (old fresh:Finset V)
local notation "req" => ActualOriginalQPointSetup.request R u J
local notation "D" => ActualOriginalQPointSetup.pointDatum R J d.period (d.level+1) o
local notation "source" => ActualOriginalQInitialPreparation.input R simple u J A d Q o μ orders
local notation "raw" => ActualOriginalQInput.input Q D u (μ-R.family.S.scale d.cutoff) orders simple d.cutoff d.below
local notation "upper" => WilsonOriginalProjectedCurvatureTableau.actors D
local notation "z₀" => WilsonOriginalMixedTestTableau.zero D
local notation "left" => WilsonMixedTestTableau.left upper next old z₀
local notation "right" => WilsonMixedTestTableau.right upper next fresh neutral
local notation "call" => WilsonReceivedCalibratedTest.submit R simple u J A d Q o μ orders

/-- A joined independent test on the all-field physical appointment, with the exact
normalized bare test on the old face and the submitted fresh test on its own face. -/
theorem original (x:Wallet (WilsonMixedTestTableau.actors upper next))
    {P:Rep G (R.family.side (d.level+1) d.period)}
    (inlet:Taste (TestSpace (req).tests) o P (Stock.census V))
    (physical:P=(ActualOriginalQInitialPreparation.carrier R d).rep) (same:HEq inlet source) :
    ∃ y:Wallet (WilsonMixedTestTableau.actors upper next),
      left y=call (left x) ∧ right y=right x ∧
      ∀ U, ((raw).leaf (testInclusion (ActualRunQlocalNativeTuple.orbit D) (left y))).density U =
        (inlet.leaf (testInclusion (req).tests (left x))).density U := by
  subst P
  have coincide:inlet=source:=eq_of_heq same
  let y:=WilsonMixedTestTableau.pair upper next (call (left x)) (right x)
  have paid:left y=call (left x):=by
    funext v
    apply Subtype.ext
    by_cases member : v∈old
    · simp [y,WilsonMixedTestTableau.left,WilsonMixedTestTableau.leftAt,WilsonMixedTestTableau.pair,member]
    · simp [WilsonMixedTestTableau.left,WilsonMixedTestTableau.leftAt,
        WilsonReceivedCalibratedTest.submit,member]
  have planted:right y=right x:=by
    funext v
    apply Subtype.ext
    by_cases member:v∈fresh <;> simp [y,WilsonMixedTestTableau.right,WilsonMixedTestTableau.rightAt,
      WilsonMixedTestTableau.pair,member]
  refine ⟨y,paid,planted,fun U=>?_⟩
  rw [paid,coincide]
  exact (WilsonReceivedCalibratedTest.original R simple u J A d Q o μ orders (left x) U).symm

end YM.Integration.WilsonReceivedCalibratedPlacement
