import YM.Integration.WilsonPhysicalHistoryMixedChain
import YM.Integration.WilsonOffsetPhysicalPairWick
import YM.Integration.WilsonMovingIssuedInlet

/-! The actual two-position physical cofactor and its independently prescribed
recursive whole-source Wick comparison on one original existence run. -/
noncomputable section
set_option autoImplicit false
namespace YM.Integration.WilsonPhysicalHistoryMixedCofactor
open Function Filter Finset Set MeasureTheory Lattice Exterior Wilson RG Precision Tree Matrix Bloch Push.Uniform
open Source Labels Next.Foundations Comparison.RG02 FreeResolvent WilsonCoeffUV PhysicalNext.Repeat.Legato
open RGComparison.Core16 RGComparison.Core16.Spool RGComparison.Core16.Lumen
open FormalBulk08 Flat Reef Orb Next.Free Jets MSbar.Rolling MSbar.Cacao PowerSeries
open Stationary Lotus Shore Mesa Gorge City Cork Rift Lava Kemp
open Pose Glide Bank Dawn Wine Rial Roof Dove Series Trellis Aster Borough Elm Dove.Lab
open Planned.PrimaryIntegral295 Place Film Carrier WilsonRunFormalMarkedStep
open Source.Drops RG16.Literal RG16.Guarding MSbar.Heath MSbar.Heath.Stock MSbar.Heath.Cottage MSbar.Mosaic
open FVA1Physical.Wilson FVA1Physical.Round2.Curvature WilsonConditionalTaylorLabels
open WilsonMovingPolynomialPull WilsonMovingGaussianCoordinates WilsonPhysicalHistoryMixedChain
open WilsonPhysicalHistorySignedWindow WilsonPhysicalExteriorMeshStops WilsonOffsetPhysicalPair
open scoped Classical Topology Matrix BigOperators
variable {G : Gauge} {a b : ℕ}

/-- Independently filed real and imaginary UV input for the whole signed
physical pair with the exact original terminal coordinate coefficients. -/
def terminal (R : Run G) (N per : ℕ) (v : R.family.label a) (w : R.family.label b)
    (x y : Site (R.family.side N per)) (part : Bool) : Pap (wire G (R.family.side N per)) :=
  place (link G (R.family.side N per)) (∑ i : ((frames G).level a).Index, ∑ j : ((frames G).level b).Index,
    let c := atom R N per v i*atom R N per w j
    let Z : Bool → Nesting G (R.family.side N per) := stencilInlet (lamps (two i j)) (seats i j x y)
    if part then c.im • Z false + c.re • Z true else c.re • Z false - c.im • Z true)

/-- Both numerical marks entering the physical comparison are the exact
finite signed original Wilson basis sum, and every corresponding filed
inlet is the actual Taylor germ of that same real or imaginary planted mark. -/
theorem issued (R : Run G) {N per : ℕ} (v : R.family.label a) (w : R.family.label b)
    (x z e : Site (R.family.side N per)) (U : Config G (R.family.side N per)) :
    R.family.O N per v x U*(R.family.O N per w z U-R.family.O N per w e U) =
      ∑ i, ∑ j, (atom R N per v i*atom R N per w j)*(planted i j x z U-planted i j x e U) ∧
    ∀ (i : ((frames G).level a).Index) (j : ((frames G).level b).Index) (y : Site (R.family.side N per)) (part : Bool),
      stencilInlet (lamps (two i j)) (seats i j x y) part =
        Jets.paste (fun A : Positions (Primary (R.family.side N per) G)=>
          look part (planted i j x y (represent (tint G (Body 1 (R.family.side N per)) A)))) := by
  refine ⟨WilsonOffsetPhysicalPair.relative R v w x z e U,?_⟩
  intro i j y part
  exact WilsonMovingIssuedInlet.full (lamps (two i j)) (seats i j x y) part

/-- Every dated counterterm is specified before the physical posterior is
read. In particular it is one whole previous response to one true Dove
vacuum at each intervening date and lives on that date's genuine period. -/
def comparison (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (color : hue G)
    (N per p : ℕ) (tag : Tags R N per) (v : R.family.label a) (w : R.family.label b)
    (x z e : Site (R.family.side N per)) (j : ℕ) (U : Config G (R.family.side j per)) : ℂ :=
  filed R N per j p (recorded R L color N per tag (terminal R N per v w x z) j) U -
    filed R N per j p (recorded R L color N per tag (terminal R N per v w x e) j) U

theorem original (R : Run G) (L : ∀ i, Lodge ((R.family.path.levels.clock.op i 0).patch)) (color : hue G)
    (p : ℕ) {N per k t : ℕ} (kt : k ≤ t) (top : t ≤ N) (tag : Tags R N per)
    (v : R.family.label a) (w : R.family.label b) (x z e : Site (R.family.side N per)) :
    let X := fun U=>R.family.O N per v x U*(R.family.O N per w z U-R.family.O N per w e U)
    let B := comparison R L color N per p tag v w x z e
    debt R (N:=N) (WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) (kt.trans top) X) (B k) ≤
      debt R (N:=N) (WilsonReportForwardTransfer.exterior (C:=R.family) (N:=N) top X) (B t) +
        ∑ j∈Finset.Ico k t,debt R (N:=N) (FVA1Physical.conditionalPush R.family.path N per j (B (j+1))) (B j) := by
  have h := WilsonPhysicalHistoryTestedPairWindow.tested R p kt top (fun _ : Fin 1=>a) (fun _=>v) (fun _=>x) w z e
    (recorded R L color N per tag (terminal R N per v w x z)) (recorded R L color N per tag (terminal R N per v w x e))
  have root : WilsonPhysicalHistoryTestedPairWindow.source R (N:=N) (per:=per)
      (fun _ : Fin 1=>a) (fun _=>v) (fun _=>x) w z e =
      fun U=>R.family.O N per v x U*(R.family.O N per w z U-R.family.O N per w e U) := by
    funext U; simp [WilsonPhysicalHistoryTestedPairWindow.source]
  dsimp only at h ⊢
  rw [root] at h
  exact h

end YM.Integration.WilsonPhysicalHistoryMixedCofactor

