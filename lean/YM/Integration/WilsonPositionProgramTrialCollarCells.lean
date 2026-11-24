import YM.Integration.WilsonPositionProgramTrialCollarFile
import YM.Integration.WilsonPositionProgramTrialConnectedSalary

/-! The original compact test uses the actual separately located lattice cells.
Every tuple met by the test retains all its coordinates in the same notebook. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCollarCells
open Filter Function Set Finset Lattice RG RG.Supply Input Org PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl
open Precision RegulatorIR RegulatorIR.Oracle RegulatorIR.Ledger RegulatorIR.Uniform
open RegulatorIR.FVAAlt2 Next.Foundations RegulatorIR.Calibration RegulatorIR.FVAAlt2.Kick
open WilsonPositionProgramSubmittedFaces WilsonPositionProgramSubmittedGeometry
open XSpace XSpace.Normalize XSpace.Rose XSpace.Structure1 XSpace.Cirrus Metric
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

abbrev Visit := ℕ × pack 3

def used (M:Mesh) (radius:ℝ) (z:pack 3) : Prop :=
  ∃ c∈M.Box, ‖M.rel z c‖≤radius

def location (M:Mesh) (radius:ℝ) (z:pack 3) : pack 3 × Four ℝ :=
  if h : used M radius z then (z,h.choose) else (draw 0 M (river M),river M)

theorem actual {M:Mesh} {radius:ℝ} {z:pack 3} (h:used M radius z) : (location M radius z).1=z := by
  simp [location,h]

theorem price (D:XSpace.Run) (i:ℕ) {radius:ℝ} (pos:0≤radius) (z:pack 3) :
    let M:=D.step i
    let p:=location M radius z
    p.2∈M.Box ∧ M.rel p.1 p.2∈closedBall (0:Points 3) (radius+12) := by
  intro M p
  by_cases h:used M radius z
  · have pay:=h.choose_spec
    simp only [p,location,dif_pos h,mem_closedBall,dist_zero_right]
    exact ⟨pay.1,by linarith only [pay.2]⟩
  · have leave:=M.upper_corner (x:=draw (0:Points 3) M (river M)) (river M) rfl
    have hp:M.spacing≤1 := inv_le_one_of_one_le₀ (by exact_mod_cast (D.den_pos i))
    simp only [p,location,dif_neg h,mem_closedBall]
    exact ⟨sits M,leave.trans (by norm_num at *;linarith)⟩

variable {G : Gauge} (R : Legato.Run G) (W : Initialize G) (V : Store G) (D : XSpace.Run)
    {simple : G.Simple} {a : Axis} {ε : ℝ}
    (first : WilsonPositionProgramArithmetic.course simple a ε R.kit)
    (paid : WilsonPositionProgramStageInvoice.Requested R.kit) (slow : WilsonWindowReportingPace.Slow R.kit)
    (Z : ∀ P : RG.Patch, P.Branches R.family.path.levels.clock.kernel G) (p : ℕ) (color : G.ColorIndex)
    (K:ℕ→ℕ) {stage:ℕ} (B:Band R D K stage) (radius:ℝ) (d:Fin 3→ℕ)
local notation "Y" => Oracle.books R.family.path.levels.clock.kernel

def grid (x:Visit) : Mesh := D.step (B.mesh x.1)
def sites (x:Visit) : pack 3 := (location (grid R D K B x) radius x.2).1
def span (x:Visit) := B.span x.1
def program := WilsonPositionProgramInfraredCircuit.circuit R D (B.lower ∘ (Prod.fst:Visit→ℕ))
  (span R D K B) (B.powers ∘ Prod.fst) (fun x=>B.blocks x.1)
variable (F:Tent (span R D K B))

def report (x:Visit) (s:Badge) (q:ℕ) (v:(i:Fin 3)→(R.family.labels.level (d i)).Coeff) (fields:Tags G 6 3) : ℂ :=
  let z:=sites R D K B radius
  let S:=program R D K B
  let j:=span R D K B
  let h:=(d ∘ Subtype.val : s→ℕ)
  let U:=fun (a:Axes R h) (e:ℕ)=>(Rocket.stopped S Y Z F (Lodge.basisR R) univ h (axis R h a)
    (final j) (fun y=>z y ∘ Subtype.val) x e:ℂ)
  let P:=fun (a:Pin R) (e:ℕ)=>(Rocket.stopped S Y Z F (registry R W) univ (heights R a) (columns R a)
    (final j) (fun y=>z y ∘ Subtype.val) x e:ℂ)
  let t:Sample 3:=⟨grid R D K B x,x.2,0⟩
  originalSum R q d s v U-proposed R q (invoice R W V t fields q s) P

def bill (M:Mesh) (z:pack 3) (s:Badge) (q:ℕ) (v:(i:Fin 3)→(R.family.labels.level (d i)).Coeff)
    (fields:Tags G 6 3) : ℝ≥0∞ :=
  originalBill R q d s v+charge R q (invoice R W V ⟨M,z,0⟩ fields q s)

include first paid slow in
theorem original {e:ℕ} (coeff:0<e) (ratio:D.ratio=(3:ℕ)^e) {A:ℝ} (pos:0≤A) (gas:Bracket R K A)
    (vacant:0≤radius) :
    ∃ stage,∃ B:Band R D K stage,∃ F:Tent (span R D K B),
      Notebook (program R D K B) Y G Z color (Rocket.native (span R D K B)) F p ∧
      ∀ strength:ℕ,∀ᶠ n:ℕ in atTop,∀ z:pack 3,used (D.step (B.mesh n)) radius z →
      ∀ (s:Badge) (q:Fin (p+1)) (v:(k:Fin 3)→(R.family.labels.level (d k)).Coeff) (fields:Tags G 6 3),
      let M:=D.step (B.mesh n)
      let t:Sample 3:=⟨M,z,0⟩
      ‖PowerSeries.coeff (q:ℕ) (source R d v W t s)-quotient W (V:=V) t fields q s-
        report R W V D Z K B radius d F (n,z) s q v fields‖ₑ ≤
        ENNReal.ofReal (M.spacing^strength) * bill R W V d M z s q v fields := by
  obtain ⟨stage,B,openFile⟩:=WilsonPositionProgramTrialCollarFile.original (X:=Visit) R W V D first paid slow
    Z p color coeff ratio K pos gas d (closedBall 0 (radius+12)) (isCompact_closedBall ..)
  obtain ⟨F,file,read⟩:=openFile Prod.fst
  refine ⟨stage,B,F,file,?_⟩
  let c (x:Visit):=(location (grid R D K B x) radius x.2).2
  have paidLoc(x:Visit):=price D (B.mesh x.1) vacant x.2
  intro strength
  obtain ⟨floor,hear⟩:=read (sites R D K B radius) c (fun x=>(paidLoc x).1) (fun x=>(paidLoc x).2) strength
  filter_upwards [eventually_ge_atTop floor] with n late z atCell s q v fields
  let x:Visit:=(n,z)
  have exactSite : sites R D K B radius x=z:=actual atCell
  have h:=hear x late s q v fields
  dsimp only at h ⊢
  rw [B.spacing,exactSite] at h
  exact h

end YM.Integration.WilsonPositionProgramTrialCollarCells
end
