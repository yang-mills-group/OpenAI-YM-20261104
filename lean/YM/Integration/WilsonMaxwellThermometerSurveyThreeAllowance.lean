import YM.Integration.WilsonMaxwellThermometerSurveyThreePins
import YM.Integration.WilsonPositionProgramSubmittedRate

/-! Finite W survey on the same commissioned notebook as the physical Run.
The unmarked oracle, old scalar, geometric wage and actual fine sites precede
the choice of an occupied W basis row and its numerical inverse. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxRecDepth 4096
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonMaxwellThermometerSurveyThreeAllowance
open WilsonPositionProgramSubmittedFaces
open WilsonMaxwellThermometerSurveyCopy (registry)
open WilsonMaxwellThermometerSurveyThreeRoster (Pin read)
open WilsonMaxwellThermometerSurveyThreePins (slots heights columns)
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
theorem original (K:Set (Points 3))(compact:IsCompact K): ∃ H:ℝ,0  ≤  H ∧ ∃start:ℕ,
    ∀(m j i:X→ℕ)(w:X→ℕ→ℕ)
      (blocks:∀x k,(C.family.S.block (m x+k)).val=D.ratio^(w x k))
      (_ :∀x,WilsonPositionProgramCommonWindow.elapsed (w x) (j x)=D.reserve*(i x)*(i x)+i x),
    (∀x,start ≤ m x) → ∀(z:X→Fin 3→ Cover)(c:X→Four ℝ),
    (∀x,c x∈(D.step (i x)).Box) → (∀x,(D.step (i x)).rel (z x) (c x)∈K) →
    let S:=WilsonPositionProgramInfraredCircuit.circuit C D m j w blocks
    ∀F:Tent j,Notebook S Y G Z color (Rocket.native j) F p → ∀strength:ℕ,∃cut:ℕ,∀x,
       cut ≤ i x → 1 ≤ C.family.path.levels.clock.hatBeta (m x) →
       RG16.Lambda C.family.path.levels (m x) ≤ (i x:ℝ)*Real.log D.ratio →
    ∀(u:Pin C)(q:ℕ),q ≤ p →
      ‖PowerSeries.coeff q (read C W ⟨D.step (i x),z x,c x⟩ u)-
       (Rocket.stopped S Y Z F (registry C W) Finset.univ (heights C u) (columns C u)
         (final j) (fun x=>z x ∘ Subtype.val) x q:ℂ)‖ₑ  ≤  ENNReal.ofReal ((D.step (i x)).spacing^strength):=by
  obtain ⟨H,hH,start,school⟩:=WilsonMaxwellThermometerSurveyAtlas.original (X:=X) C W D first paid slow Z p color
    (by decide:0<3) K compact
  refine ⟨H,hH,start,?_⟩
  intro m j i w blocks reach old z c box support S F file strength
  let L:=WilsonPositionProgramInfraredMeter.wallet C D m j w i H
  let Q:=Rocket.wage S Y Z F (final j) (1/2)
  let amount (a:Pin C×Fin (p+1))(x:X):ℝ≥0∞:=
    ‖PowerSeries.coeff a.2.val (read C W ⟨D.step (i x),z x,c x⟩ a.1)-
       (Rocket.stopped S Y Z F (registry C W) Finset.univ (heights C a.1) (columns C a.1)
         (final j) (fun x=>z x ∘ Subtype.val) x a.2.val:ℂ)‖ₑ
  have rows (a:Pin C×Fin (p+1)):Carry L Q (amount a):=by
    have h:=school m j i w blocks reach old z c box support F file (slots C a.1) Subtype.val
      (heights C a.1) (columns C a.1) (fun x=>W.tree (D.step (i x)).p) a.2.val (Nat.le_of_lt_succ a.2.isLt)
    simpa only [amount,WilsonMaxwellThermometerSurveyThreePins.placed] using h
  choose cut rate using fun a:Pin C×Fin (p+1)=>
    WilsonPositionProgramSubmittedRate.original D C simple m j w i blocks reach Z F H (rows a) strength
  refine ⟨Finset.univ.sup cut,?_⟩
  intro x late mature room u q hq
  let a:Pin C×Fin (p+1):=(u,⟨q,Nat.lt_succ_of_le hq⟩)
  change amount a x ≤ _
  exact rate a x ((Finset.le_sup (f:=cut) (Finset.mem_univ a)).trans late) mature room
end YM.Integration.WilsonMaxwellThermometerSurveyThreeAllowance
end
