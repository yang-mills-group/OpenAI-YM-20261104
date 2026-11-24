import YM.Integration.WilsonPhysicalHistorySignedWindow
import YM.Integration.WilsonPhysicalHistoryPositiveConditional
import YM.Integration.WilsonOffsetPhysicalPair

/-! The two genuine microscopic offsets and their entire detector arrive from
the same top cutoff across the physical first-crossing window. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryTestedPairWindow
open Function Filter Finset Set MeasureTheory Lattice RG YM.Wilson OPE OPE.Therm
open WilsonCoeffUV PhysicalNext.Repeat.Legato WilsonPhysicalHistorySignedWindow
open Precision Tree Exterior Push.Uniform MSbar MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage
open MSbar.Cacao MSbar.Mosaic MSbar.Rolling MSbar.Bulk MSbar.Lis MSbar.Bakery.Film MSbar.Midpoint MSbar.Measuring
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature RG01.Kernel
open RG16 RG16.Literal Pert.Asymptotics WilsonPhysicalExteriorMeshStops WilsonCumulantCommonOffset
open scoped BigOperators Classical
variable {G : Gauge}

/-- Both actual UV placements of one insertion, with an unchanged finite
roster of original Wilson detectors in their genuine microscopic sites. -/
def source (R : Run G) {N per q d : ℕ} (dims : Fin q → ℕ)
    (v : (l:Fin q) → R.family.label (dims l)) (y : Fin q → Site (R.family.side N per))
    (w : R.family.label d) (z e : Site (R.family.side N per)) (U : Config G (R.family.side N per)) : ℂ :=
  (∏ l, R.family.O N per (v l) (y l) U) *
    (R.family.O N per w z U-R.family.O N per w e U)

theorem integrable (R : Run G) {N per q d : ℕ} (dims : Fin q → ℕ)
    (v : (l:Fin q) → R.family.label (dims l)) (y : Fin q → Site (R.family.side N per))
    (w : R.family.label d) (z e : Site (R.family.side N per)) :
    Integrable (source R dims v y w z e) (scene R.family.path N per N) := by
  letI : IsProbabilityMeasure (scene R.family.path N per N) := probability R.makes.wilson (le_refl N)
  have ct : Continuous (source R dims v y w z e) :=
    (continuous_finsetProd _ fun l _=>R.family.continuousO N per (dims l) (v l) (y l)).mul
      ((R.family.continuousO N per d w z).sub (R.family.continuousO N per d w e))
  exact ct.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- Actual signed two-position estimate at every physical subwindow. At the
upper end the WHOLE original source is retained through all stages from N,
including the covariance between the fine detector and the moving insertion.
The local residuals are true old-vacuum conditionals of the two signed,
independently prescribed complete chart fields. -/
theorem tested (R : Run G) (p : ℕ) {N per k t q d : ℕ} (kt : k ≤ t) (top : t ≤ N)
    (dims : Fin q → ℕ) (v : (l:Fin q) → R.family.label (dims l)) (y : Fin q → Site (R.family.side N per))
    (w : R.family.label d) (z e : Site (R.family.side N per))
    (Tz Te : (j:ℕ) → Bool → Nesting G (R.family.side j per)) :
    let X := source R dims v y w z e
    let B := fun j U=>filed R N per j p (Tz j) U-filed R N per j p (Te j) U
    debt R (N:=N) (WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) (kt.trans top) X) (B k) ≤
    debt R (N:=N) (WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) top X) (B t) +
      ∑ j∈Finset.Ico k t,debt R (N:=N) (FVA1Physical.conditionalPush R.family.path N per j (B (j+1))) (B j) := by
  let X := source R dims v y w z e
  let B := fun j U=>filed R N per j p (Tz j) U-filed R N per j p (Te j) U
  let XU := WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) top X
  have hX := integrable R dims v y w z e
  have hU : Integrable XU (scene R.family.path N per t) :=
    (WilsonReportForwardTransfer.contract (C:=R.family) R.makes top (le_refl N) X hX).1
  have hB (j) (hj : j ≤ N) : Integrable (B j) (scene R.family.path N per j) :=
    (filed_integrable R hj p (Tz j)).sub (filed_integrable R hj p (Te j))
  have paid := accumulate R kt top XU hU B hB
  have tower : WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) kt XU =
      WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) (kt.trans top) X :=
    WilsonPhysicalHistoryPositiveTower.cascade R kt top (le_refl N) X
  rw [tower] at paid
  apply paid.trans_eq
  apply congrArg (_+·)
  apply Finset.sum_congr rfl
  intro j hj
  have live := lt_of_lt_of_le (Finset.mem_Ico.mp hj).2 top
  have eq : WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) j.le_succ (B (j+1)) =
      FVA1Physical.conditionalPush R.family.path N per j (B (j+1)) :=
    funext fun V=>WilsonPhysicalHistoryPositiveConditional.original R live _ V
  exact congrArg (fun F=>debt R (N:=N) F (B j)) eq

/-- The top in this estimate is the physical first crossing, and the common
cutoff N may be arbitrarily farther out. -/
theorem first (R : Run G) (simple : G.Simple) (pace : WilsonWindowReportingPace.Slow R.kit) (c : ℝ) (p : ℕ) :
    ∀ᶠ k : ℕ in atTop, ∃ kt : k ≤ ultraviolet R.family c k,
      ∀ {N per q d : ℕ} (top : ultraviolet R.family c k ≤ N)
        (dims : Fin q → ℕ) (v : (l:Fin q) → R.family.label (dims l)) (y : Fin q → Site (R.family.side N per))
        (w : R.family.label d) (z e : Site (R.family.side N per))
        (Tz Te : (j:ℕ) → Bool → Nesting G (R.family.side j per)),
      let X := source R dims v y w z e
      let B := fun j U=>filed R N per j p (Tz j) U-filed R N per j p (Te j) U
      debt R (N:=N) (WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) (kt.trans top) X) (B k) ≤
      debt R (N:=N) (WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) top X) (B (ultraviolet R.family c k)) +
        ∑ j∈Finset.Ico k (ultraviolet R.family c k),
          debt R (N:=N) (FVA1Physical.conditionalPush R.family.path N per j (B (j+1))) (B j) := by
  filter_upwards [ultraviolet_window R.family simple pace.2 c] with k hk
  refine ⟨hk.1.le,?_⟩
  intro N per q d top dims v y w z e Tz Te
  exact tested R p hk.1.le top dims v y w z e Tz Te

end YM.Integration.WilsonPhysicalHistoryTestedPairWindow

