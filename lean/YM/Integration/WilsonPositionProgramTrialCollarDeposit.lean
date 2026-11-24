import YM.Integration.WilsonPositionProgramTrialCollarCells

/-! The actual center-smearing of the signed chronological result, with the
whole proper-face cofactors still evaluated on the two submitted programs. -/
noncomputable section
set_option autoImplicit false
set_option warningAsError true
namespace YM.Integration.WilsonPositionProgramTrialCollarDeposit
open Filter Set Function Finset PowerSeries MeasureTheory Lattice Wilson RG RG.Supply Input Org
open PhysicalNext PhysicalNext.Repeat Legato OPE OPE.Owl Precision RegulatorIR RegulatorIR.Oracle
open RegulatorIR.Ledger RegulatorIR.Uniform RegulatorIR.FVAAlt2 Next.Foundations RegulatorIR.Calibration
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus FVA2 FVA2.Register
open WilsonPositionProgramTrialOpticalBand (Band Bracket)
open WilsonPositionProgramTrialCollarCells (Visit used report bill program span)
open WilsonPositionProgramTrialRose (roster)
open WilsonPositionProgramTrialConnectedSalary (stopped payroll)
open WilsonPositionProgramTrialSurvey (source)
open WilsonMaxwellThermometerPublicGalop (quotient)
open scoped Classical BigOperators ENNReal
variable {G:Gauge} (R:Legato.Run G) (d:Fin 3→ℕ) (cap:∀i,d i<7)
    (v:(i:Fin 3)→(R.family.labels.level (d i)).Coeff)
    (W:Initialize G) (V:Store G) (M:Mesh) (φ:Test 3) (radius:ℝ)
    (q:ℕ) (E:pack 3→Badge→ℕ→ℂ) (fee:pack 3→Badge→ℕ→ℝ≥0∞)

def income : ℝ≥0∞ :=
  ‖(M.spacing:ℂ)^(4*3)‖ₑ * ∑u:M.Tuple, ‖M.smear (M.back u) φ‖ₑ *
    payroll R d v W V ⟨M,M.back u,0⟩ q (fee (M.back u))

def heard : ℂ := Deposit M (fun t=>stopped R d v W V t q (E t.layout)) φ

theorem unmet (z:pack 3) (cash:∀x∈tsupport φ,‖x‖≤radius) (h:¬used M radius z) :
    M.smear z φ=0 := by
  change M.vol⁻¹ • (∫c in M.Box,M.termView φ z c)=0
  have off : ∀c∈M.Box, M.termView φ z c=0 := by
    intro c inside
    change φ (M.rel z c)=0
    exact image_eq_zero_of_notMem_tsupport (fun support=>h ⟨c,inside,cash _ support⟩)
  rw [setIntegral_eq_zero_of_forall_eq_zero off,smul_zero]

theorem integrate (b:ℝ≥0∞) (cash:∀x∈tsupport φ,‖x‖≤radius)
    (rows:∀ z,used M radius z → ∀ s k,k≤q →
      let t:Sample 3:=⟨M,z,0⟩
      ‖coeff k (source R d v W t s)-quotient W (V:=V) t (tag G) k s-E z s k‖ₑ ≤ b*fee z s k) :
    ‖Deposit M (fun t=>coeff q (roster R d cap v W V t)) φ - heard R d v W V M φ q E‖ₑ ≤
    b*income R d v W V M φ q fee := by
  unfold heard Deposit income
  rw [←mul_sub,←sum_sub_distrib,enorm_mul,mul_left_comm]
  apply mul_le_mul_right
  refine (enorm_sum_le ..).trans ?_
  rw [Finset.mul_sum]
  refine sum_le_sum fun u _=>?_
  rw [←mul_sub,enorm_mul,mul_left_comm]
  by_cases active:used M radius (M.back u)
  · exact mul_le_mul_right (WilsonPositionProgramTrialConnectedSalary.original R d cap v W V
      ⟨M,M.back u,0⟩ q (E (M.back u)) (fee (M.back u)) b (rows _ active)) _
  · simp only [unmet M φ radius (M.back u) cash active,enorm_zero,zero_mul,le_refl]

variable (D:XSpace.Run) {simple:G.Simple} {a:Axis} {ε:ℝ}
    (first:WilsonPositionProgramArithmetic.course simple a ε R.kit)
    (paid:WilsonPositionProgramStageInvoice.Requested R.kit) (slow:WilsonWindowReportingPace.Slow R.kit)
    (Z:∀ P:RG.Patch,P.Branches R.family.path.levels.clock.kernel G) (p:ℕ) (color:G.ColorIndex)
    (K:ℕ→ℕ)
local notation "Y" => Oracle.books R.family.path.levels.clock.kernel

include first paid slow in
theorem original {e:ℕ} (coeff:0<e) (ratio:D.ratio=(3:ℕ)^e) {A:ℝ} (pos:0≤A) (gas:Bracket R K A)
    (vacant:0≤radius) :
    ∃ stage,∃ B:Band R D K stage,∃ F:Tent (span R D K B),
      Notebook (program R D K B) Y G Z color (Rocket.native (span R D K B)) F p ∧
      ∀ strength:ℕ,∀ᶠ n:ℕ in atTop,∀ (φ:Test 3), (∀x∈tsupport φ,‖x‖≤radius) →
      ∀ (q:Fin (p+1)) (v:(i:Fin 3)→(R.family.labels.level (d i)).Coeff),
      let M:=D.step (B.mesh n)
      let E:=fun z s k=>report R W V D Z K B radius d F (n,z) s k v (tag G)
      let fee:=fun z s k=>bill R W V d M z s k v (tag G)
      ‖Deposit M (fun t=>PowerSeries.coeff (q:ℕ) (roster R d cap v W V t)) φ-
        heard R d v W V M φ q E‖ₑ ≤
        ENNReal.ofReal (M.spacing^strength)*income R d v W V M φ q fee := by
  obtain ⟨stage,B,F,registered,active⟩:=WilsonPositionProgramTrialCollarCells.original R W V D
    first paid slow Z p color K radius d coeff ratio pos gas vacant
  refine ⟨stage,B,F,registered,fun strength=>?_⟩
  filter_upwards [active strength] with n paidCells φ support q v
  apply integrate R d cap v W V _ φ radius q _ _ _ support
  intro z inBall s k hk
  exact paidCells z inBall s ⟨k,Nat.lt_of_le_of_lt hk q.isLt⟩ v (tag G)

end YM.Integration.WilsonPositionProgramTrialCollarDeposit
end
