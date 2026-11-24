import YM.Integration.WilsonPositionProgramTrialRosterTariff
import YM.Integration.WilsonPositionProgramSharedInversionTariff

/-! The two separately registered compact source lists are run on the same
chronological oracle, finite geometry and notebook. All dates and error
thresholds precede the measured coefficients. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
namespace YM.Integration.WilsonPositionProgramTrialRegisteredReturn
open Set Filter Function Finset Lattice RG RG.Supply Org Input PhysicalNext PhysicalNext.Repeat Legato
open OPE OPE.Owl Precision RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform
open RegulatorIR.FVAAlt2 Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick
open WilsonPositionProgramSubmittedFaces WilsonPositionProgramSubmittedGeometry
open XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 XSpace.Cirrus
open WilsonPositionProgramTrialRosterTariff (originalSum originalBill proposed charge)
open WilsonPositionProgramInversionMaterial (Axes axis)
open WilsonPositionProgramTrialSurvey (source)
open WilsonMaxwellThermometerSurveyThreeRoster (Pin)
open WilsonMaxwellThermometerSurveyThreeLedger (invoice)
open WilsonMaxwellThermometerSurveyCopy (registry)
open WilsonMaxwellThermometerSurveyThreePins (heights columns)
open WilsonMaxwellThermometerPublicGalop (quotient)
open scoped BigOperators Classical ENNReal
variable {G : Gauge} (R : Legato.Run G) (W : Initialize G) (V : Store G) (D : XSpace.Run)
    {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
    (first : WilsonPositionProgramArithmetic.course simple a ε R.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested R.kit) (slow : WilsonWindowReportingPace.Slow R.kit)
    (Z : ∀ P : RG.Patch, P.Branches R.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books R.family.path.levels.clock.kernel

include first paid slow in
theorem original (d : Fin 3 → ℕ) (K : Set (Points 3)) (compact : IsCompact K) :
    ∃ start : ℕ, ∀ (m j i : X → ℕ) (w : X → ℕ → ℕ)
      (blocks : ∀ x k, (R.family.S.block (m x + k)).val = D.ratio^(w x k))
      (_ : ∀ x, WilsonPositionProgramCommonWindow.elapsed (w x) (j x) = D.reserve * (i x) * (i x) + i x),
    (∀ x, start ≤ m x) → ∀ (z : X → Fin 3 → Cover) (c : X → Four ℝ),
    (∀ x, c x ∈ (D.step (i x)).Box) → (∀ x, (D.step (i x)).rel (z x) (c x) ∈ K) →
    let S := WilsonPositionProgramInfraredCircuit.circuit R D m j w blocks
    ∀ F : Tent j, Notebook S Y G Z color (Rocket.native j) F p → ∀ strength : ℕ,
    ∃ cutoff : ℕ, ∀ x, cutoff ≤ i x → 1 ≤ R.family.path.levels.clock.hatBeta (m x) →
      RG16.Lambda R.family.path.levels (m x) ≤ (i x:ℝ) * Real.log D.ratio →
    ∀ (s : Badge) (q : Fin (p+1)) (v : (k:Fin 3) → (R.family.labels.level (d k)).Coeff) (fields : Tags G 6 3),
    let t : Sample 3 := ⟨D.step (i x),z x,c x⟩
    let h := (d ∘ Subtype.val : s → ℕ)
    let U := fun (a : Axes R h) (e : ℕ) => (Rocket.stopped S Y Z F (Lodge.basisR R) univ h
      (axis R h a) (final j) (fun x => z x ∘ Subtype.val) x e : ℂ)
    let A := fun (a : Pin R) (e : ℕ) => (Rocket.stopped S Y Z F (registry R W) univ (heights R a)
      (columns R a) (final j) (fun x => z x ∘ Subtype.val) x e : ℂ)
    let δ := invoice R W V t fields q s
    ‖PowerSeries.coeff (q:ℕ) (source R d v W t s) - quotient W (V:=V) t fields q s -
        (originalSum R q d s v U - proposed R q δ A)‖ₑ ≤
      ENNReal.ofReal ((D.step (i x)).spacing^strength) * (originalBill R q d s v + charge R q δ) := by
  obtain ⟨_,_,k₁,left⟩ := WilsonPositionProgramSharedInversionTariff.original (X:=X) R D
    first paid slow Z p color (by decide : 0 < 3) K compact
  obtain ⟨_,_,k₂,right⟩ := WilsonMaxwellThermometerSurveyThreeAllowance.original (X:=X) R W D
    first paid slow Z p color K compact
  refine ⟨max k₁ k₂,?_⟩
  intro m j i w blocks reach old z c box support S F file strength
  have lr := left m j i w blocks reach (fun x => (le_max_left _ _).trans (old x)) z c box support F file
  obtain ⟨cw,cost⟩ := right m j i w blocks reach (fun x => (le_max_right _ _).trans (old x))
    z c box support F file strength
  let cuts (b : Badge × Fin (p+1)) := lr b.1 Subtype.val (d ∘ Subtype.val)
    (fun x => W.tree (D.step (i x)).p) b.2.val (by omega) strength
  let cr (b : Badge × Fin (p+1)) := Classical.choose (cuts b)
  refine ⟨max cw (univ.sup cr),?_⟩
  intro x late mature room s q v fields t h U A δ
  apply WilsonPositionProgramTrialRosterTariff.balance R q d s v W V t fields U A
  · have here : cr (s,q) ≤ i x := (Finset.le_sup (f:=cr) (mem_univ (s,q))).trans
      ((le_max_right _ _).trans late)
    have receipt := Classical.choose_spec (cuts (s,q)) x here mature room (chart G) (chart_ok G)
      (WilsonOriginalPublicFigureCatalogue.filed R h (fun k:s => v k))
    rw [WilsonOriginalPublicFigureCatalogue.read R h (fun k:s => v k) _ _ _ (chart G) (chart_ok G),
      PowerSeries.coeff_X_pow_mul] at receipt
    exact receipt
  · intro b e eq
    exact cost x ((le_max_left ..).trans late) mature room b e (by omega)

end YM.Integration.WilsonPositionProgramTrialRegisteredReturn
end
