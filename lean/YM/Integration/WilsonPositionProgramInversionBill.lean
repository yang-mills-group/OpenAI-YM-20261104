import YM.Integration.WilsonPositionAuxiliaryReporterCalendar
import YM.Integration.WilsonPositionProgramInversion

/-! Charge the finite detector and spatial cutoff on the end of the actual elected
block interval. All choices take place before either physical regulator. -/

set_option autoImplicit false
noncomputable section
namespace YM.Integration.WilsonPositionProgramInversionBill
open Filter Lattice Wilson RG PhysicalNext.Repeat.Legato OPE OPE.Owl Trace.Pilot Pert.Asymptotics
open XSpace FVA2 FVA2.Register FVA2.Scale MS MS.Land
open WilsonPositionProgramCommonWindow
open scoped Topology
variable {G : Gauge} (R : Run G) (hG : G.Simple) {B : ℕ} (hB : 0<B) (pace : WilsonWindowReportingPace.Slow R.kit)
variable (t : ℝ→ℝ) (physical : Coupling G t) (Z : WilsonPrescription G)
    {M : MS_Data G (Position.OpenAxis.Plot (Press.portDeck G))}
    {σ : Prescription (Press.portDeck G)} {dial : Bool} (H : Main.Match Z hG M σ dial)
local notation "m" => WilsonMeasuredWindow.stop R.family.path.levels hG B
local notation "Λ" => WilsonPositionAuxiliaryReporterCalendar.scale R hG (B:=B)

include hB pace physical H in
theorem interval (q : ℕ) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in trail, ∀ i : ℕ,
      (Λ r)^((3:ℝ)/2) ≤ (i:ℝ)*Real.log Z.run.ratio →
      (i:ℝ)*Real.log Z.run.ratio ≤ (Λ r)^((3:ℝ)/2)+2*(Λ r) →
      WilsonPositionAuxiliaryMesh.floor Z.run q (t r) ≤ i ∧
      (Z.run.step i).spacing^Tide.mildG ≤ (t r)^(q+1) ∧
      (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q *|t r| ≤ δ := by
  have large : 1 < (Z.run.ratio:ℝ) := by
    exact_mod_cast (show 1<Z.run.ratio from (by decide : 1<3).trans_le Z.run.large)
  have lr := Real.log_pos large
  have base := WilsonPositionAuxiliaryReporterCalendar.original R hG hB pace t physical Z H q hd
  have bill := WilsonPositionAuxiliaryReporterCalendar.paid R hG hB pace t physical Z H q 2
    (3 / Real.log Z.run.ratio) (by positivity) hd
  filter_upwards [base,bill,physical.positive] with r first tariff hr i above below
  have hi : WilsonPositionAuxiliaryReporterCalendar.inversion R hG (B:=B) Z r ≤ i :=
    Nat.ceil_le.mpr ((div_le_iff₀ lr).mpr above)
  have floor := first.1.trans hi
  have x1 : 1≤Λ r := by
    change 1≤2+WilsonAdmissionScale.logarithm R.family.path.levels (m r)
    linarith [WilsonAdmissionScale.logarithm_pos R.family.path.levels (m r)]
  have cubic : (Λ r)^((3:ℝ)/2) ≤ (Λ r)^2 := by
    rw [←Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le x1 (by norm_num)
  have linear : Λ r≤(Λ r)^2 := by nlinarith [mul_nonneg (sub_nonneg.mpr x1) (zero_le_one.trans x1)]
  refine ⟨floor,WilsonPositionAuxiliaryMesh.cost Z.run q hr floor,tariff i floor ?_⟩
  have size : (i:ℝ) ≤ 3*(Λ r)^2/Real.log Z.run.ratio := (le_div_iff₀ lr).mpr (by linarith)
  calc (i:ℝ) ≤ 3*(Λ r)^2/Real.log Z.run.ratio := size
       _ = _ := by ring

include hB pace physical H in
theorem original {a : Axis} {ε : ℝ} (purchase : WilsonPositionProgramElection.course hG a ε R.kit)
    {d : ℕ} (powered : 0<d) (ratio : Z.run.ratio=3^d)
    (q : ℕ) {δ : ℝ} (hd : 0<δ) :
    ∀ᶠ r in trail, ∃ (w : ℕ→ℕ) (j : ℕ), let i:=elapsed w j
      0<j ∧ (∀ k,(R.family.S.block (m r+k)).val=Z.run.ratio^w k) ∧
      R.family.S.a (m r+j)/R.family.S.a (m r)=(Z.run.step i).spacing ∧
      WilsonPositionAuxiliaryMesh.floor Z.run q (t r) ≤ i ∧
      (Z.run.step i).spacing^Tide.mildG ≤ (t r)^(q+1) ∧
      (1+WilsonPositionRawMesh.mass Z (Z.run.step i) q)^q *|t r| ≤ δ := by
  have dates := (WilsonMeasuredWindow.stop_tendsto R.family.path.levels hG B hB).eventually
    (WilsonPositionProgramInversion.chosen R hG Z.run purchase powered ratio pace.2)
  filter_upwards [dates,interval R hG hB pace t physical Z H q hd] with r dates paid
  obtain ⟨w,j,hj,hs,spacing,lo,hi⟩ := dates
  exact ⟨w,j,hj,hs,spacing,paid (elapsed w j) lo hi⟩

end YM.Integration.WilsonPositionProgramInversionBill
