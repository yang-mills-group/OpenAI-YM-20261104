import YM.Integration.WilsonPositionProgramTrialOpticalBand
import YM.Integration.WilsonPositionProgramTrialRegisteredReturn

/-! Both registered sources are evaluated on the chronological program whose
last block is the prescribed physical planting block. The price is uniform
over the incoming field coefficients, the physical regulators and the sites. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCollarFile
open Filter Function Set Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Precision RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform
open RegulatorIR.FVAAlt2 Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick
open WilsonPositionProgramSubmittedFaces WilsonPositionProgramSubmittedGeometry
open XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 XSpace.Cirrus
open WilsonPositionProgramTrialOpticalBand (Band Bracket)
open WilsonPositionProgramTrialRosterTariff (originalSum originalBill proposed charge)
open WilsonPositionProgramInversionMaterial (Axes axis)
open WilsonPositionProgramTrialSurvey (source)
open WilsonMaxwellThermometerSurveyThreeRoster (Pin)
open WilsonMaxwellThermometerSurveyThreeLedger (invoice)
open WilsonMaxwellThermometerSurveyCopy (registry)
open WilsonMaxwellThermometerSurveyThreePins (heights columns)
open WilsonMaxwellThermometerPublicGalop (quotient)
open scoped Classical ENNReal
variable {G : Gauge} (R : Legato.Run G) (W : Initialize G) (V : Store G) (D : XSpace.Run)
    {X : Type} {simple : G.Simple} {a : Axis} {ε : ℝ}
    (first : WilsonPositionProgramArithmetic.course simple a ε R.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested R.kit) (slow : WilsonWindowReportingPace.Slow R.kit)
    (Z : ∀ P : RG.Patch, P.Branches R.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
local notation "Y" => Oracle.books R.family.path.levels.clock.kernel

include first paid slow in
theorem original {k:ℕ} (hk:0<k) (ratio:D.ratio=(3:ℕ)^k) (K:ℕ→ℕ) {A:ℝ} (pos:0≤A) (gas:Bracket R K A)
    (d : Fin 3 → ℕ) (compact : Set (Points 3)) (closed : IsCompact compact) :
    ∃ stage,∃ B:Band R D K stage,∀ (atDate:X→ℕ),
    let j:=B.span ∘ atDate
    let S:=WilsonPositionProgramInfraredCircuit.circuit R D (B.lower ∘ atDate) j (B.powers ∘ atDate)
      (fun x=>B.blocks (atDate x))
    ∃ F:Tent j, Notebook S Y G Z color (Rocket.native j) F p ∧
    ∀ (z : X → Fin 3 → Cover) (c : X → Four ℝ), (∀ x,c x∈(D.step (B.mesh (atDate x))).Box) →
      (∀ x,(D.step (B.mesh (atDate x))).rel (z x) (c x)∈compact) →
      ∀ strength:ℕ,∃ threshold:ℕ, ∀ x, threshold ≤ atDate x →
      ∀ (s:Badge) (q:Fin (p+1)) (v:(h:Fin 3)→(R.family.labels.level (d h)).Coeff) (fields:Tags G 6 3),
      let t:Sample 3:=⟨D.step (B.mesh (atDate x)),z x,c x⟩
      let h:=(d ∘ Subtype.val : s→ℕ)
      let U:=fun (a:Axes R h) (e:ℕ)=>(Rocket.stopped S Y Z F (Lodge.basisR R) univ h
        (axis R h a) (final j) (fun x=>z x ∘ Subtype.val) x e : ℂ)
      let P:=fun (a:Pin R) (e:ℕ)=>(Rocket.stopped S Y Z F (registry R W) univ (heights R a)
        (columns R a) (final j) (fun x=>z x ∘ Subtype.val) x e : ℂ)
      let δ:=invoice R W V t fields q s
      ‖PowerSeries.coeff (q:ℕ) (source R d v W t s)-quotient W (V:=V) t fields q s -
        (originalSum R q d s v U-proposed R q δ P)‖ₑ ≤
        ENNReal.ofReal ((R.family.S.a (K (B.reporter+atDate x))/R.family.S.a (B.reporter+atDate x))^strength) *
          (originalBill R q d s v+charge R q δ) := by
  obtain ⟨stage,ready⟩:=WilsonPositionProgramTrialRegisteredReturn.original (X:=X) R W V D first paid slow Z p color d compact closed
  obtain ⟨B⟩:=WilsonPositionProgramTrialOpticalBand.elected R simple D first hk ratio stage K pos gas
  refine ⟨stage,B,?_⟩
  intro atDate j S
  obtain ⟨F,file⟩:=Calibration.tomorrows S Y G Z color (Rocket.native j) p
  refine ⟨F,file,?_⟩
  intro z c inBox active strength
  obtain ⟨bound,hear⟩:=ready (B.lower ∘ atDate) j (B.mesh ∘ atDate) (B.powers ∘ atDate)
    (fun x=>B.blocks (atDate x)) (fun x=>B.extent (atDate x)) (fun x=>B.ready (atDate x)) z c inBox active F file strength
  obtain ⟨floor,enough⟩:=eventually_atTop.mp (B.cofinal.eventually_ge_atTop bound)
  refine ⟨floor,?_⟩
  intro x late s q v fields
  rw [B.spacing]
  exact hear x (enough (atDate x) late) (R.family.path.levels.fits.delayed _).le (B.room _) s q v fields

end YM.Integration.WilsonPositionProgramTrialCollarFile
end
