import YM.Integration.WilsonMaxwellThermometerSurveyCopy
import YM.Integration.WilsonPositionProgramArithmeticMaterial

/-! Finite W survey on the same commissioned notebook as the physical Run.
The unmarked oracle, old scalar, geometric wage and actual fine sites precede
the choice of an occupied W basis row and its numerical inverse. -/
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSurveyAtlas
open WilsonPositionProgramSubmittedFaces
open WilsonMaxwellThermometerSurveyCopy (registry planted)
open Set Filter Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision
open RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2
open Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick WilsonPositionProgramSubmittedGeometry
open scoped Classical Topology ENNReal
variable {G : Gauge} (C : Run G) (W : XSpace.Initialize G) (D : XSpace.Run) {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
variable (first : WilsonPositionProgramArithmetic.course simple a ε C.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested C.kit) (slow : WilsonWindowReportingPace.Slow C.kit)
    (Z : ∀ P : RG.Patch, P.Branches C.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books C.family.path.levels.clock.kernel
include first paid slow in
/- All proper and full rosters of one compact preparation share the original calendar, table and book.
The lone analytic room probe belongs to the original compact set and remains available on the empty face. -/
theorem original {n : ℕ} (nonempty : 0 < n) (K : Set (Points n)) (compact : IsCompact K) : ∃ H : ℝ, 0 ≤ H ∧
    ∃ start : ℕ, ∀ (m j i : X → ℕ) (w : X → ℕ → ℕ)
      (blocks : ∀ x k, (C.family.S.block (m x+k)).val=D.ratio^(w x k))
      (_reach : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
      (∀ x, start ≤ m x) → ∀ (z : X → Fin n → Cover) (c : X → Four ℝ),
      (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
      let S := WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
      let L := WilsonPositionProgramInfraredMeter.wallet C D m j w i H
      ∀ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p →
        ∀ (I : Type) [Fintype I] [LinearOrder I] (child : I → Fin n)
          (d : I → ℕ) (v : (b : I) → (C.family.labels.level (d b)).Index)
          (tree : ∀ x, (D.step (i x)).p.Tree) (q : ℕ), q ≤ p →
          Carry L (Rocket.wage S Y Z F (final j) (1/2)) (fun x =>
            ‖PowerSeries.coeff q (WilsonThermometerPositionTunedCorrection.surveyed C W d (D.step (i x)).p
              ((z x) ∘ child) (tree x) v) -
              (Rocket.stopped S Y Z F (registry C W) Finset.univ d v (final j) (fun x => (z x) ∘ child) x q : ℂ)‖ₑ) := by
  obtain ⟨H,hH,sites⟩ := WilsonPositionProgramSubmittedGeometry.roster K compact
  obtain ⟨start,fund⟩ := WilsonPositionProgramArithmeticInfraredAtlas.purchased (X:=X) C D first paid slow Z p
  refine ⟨H,hH,start,?_⟩
  intro m j i w blocks reach old z c box support S L
  let B := WilsonPositionProgramInfraredAtlas.budget C D m j w blocks
  let room := fun x => center (D.step (i x)) (c x)
  intro F file I _ _ child d v tree q hq
  obtain ⟨unit,small⟩ := WilsonPositionProgramInfraredCircuit.units C D m j w blocks
  have zero (x : X) : B.peak (Page.opening j x)=0 := by change Real.log (S.l _)=0; rw [unit,Real.log_one]
  have top (x : X) := WilsonPositionProgramInfraredCircuit.fine D j w x (i x) (reach x)
  have hpos : (S.dialect Y G Z (sheet F)).cushion (1/8) room := by
    intro x
    change (1/8:ℝ)*(WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val ≤
      Spatial.singular (WilsonPositionProgramInfraredCircuit.count D j w (Page.opening j x)).val (room x)
    rw [top]
    exact pin _ (c x) (box x)
  have near (b : Fin n) : Nearest room L (fun x => z x b) :=
    WilsonPositionProgramInfraredMeter.displacements C D m j w i H z c (fun x => sites _ _ _ (support x)) b
  have cash := Rocket.soothe S Y Z F (registry C W) Finset.univ d v (final j) (chart_ok G)
    (fund m j w blocks old) file zero unit (WilsonPositionProgramInfraredMeter.age C D m j w blocks i H)
    small simple (show RegulatorIR.Taping.quantum 1 0 ≤ Lodge.through p by dsimp [RegulatorIR.Taping.quantum,Lodge.through]; omega)
    (show (0:ℝ)<1/8 by norm_num) hpos (fun x => (z x) ∘ child) (fun b _ => near (child b)) ⟨_,near ⟨0,nonempty⟩⟩ q hq
  apply cash.mono
  intro x
  dsimp only
  rw [WilsonMaxwellThermometerSurveyCopy.original C W _ d ((z x) ∘ child) v (chart G) (chart_ok G) (tree x) q]
  rw [←Complex.ofReal_sub]
  simp only [←ofReal_norm,Complex.norm_real]
  rw [top]
  rfl

end YM.Integration.WilsonMaxwellThermometerSurveyAtlas
end
