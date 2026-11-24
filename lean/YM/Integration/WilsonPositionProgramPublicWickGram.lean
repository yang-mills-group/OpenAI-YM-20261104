import YM.Integration.WilsonPositionProgramPublicQuadratic
import YangMills.WilsonProof.NativeSupport.YM.MS.Theater.Horizon
import YM.Extra.FREE_DETECTOR_ALGEBRA.LabelTurn
import YM.Next.MAXWELL.Battery
import YangMills.WilsonProof.NativeSupport.YM.XSpace.OnShell
import YM.XSpace.Furniture
import YM.XSpace.Automatic
import YM.XSpace.Forecast

/-! A determining reflected Maxwell Gram on the complete native public
catalogue, including the unit and all smaller engineering dimensions. -/
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicWickGram
open Function Set Filter MeasureTheory Lattice
open Source Labels
open Labels Maxwell Maxwell.Free Maxwell.Wick MS MS.Menus MS.Land MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 Local.Physical
open Extra Extra.FD
open WilsonPositionProgramPublicQuadratic WilsonPositionProgramPublicContrast
open scoped Topology ContDiff BigOperators Classical ComplexOrder
variable {G:Gauge} {d:ℕ} {I:Type} [Fintype I]
variable {B : Local.Physical.Deck G}
local notation "E"=> Theater.Daylight B d

def vertex (a:Axis) : E4 := (2:ℝ)⁻¹•basis a
def nodes (a:Axis) : Points 2 := FD.couple (vertex a) (-(vertex a))

theorem apart (a:Axis) : vertex a - (-(vertex a)) = basis a := by
  unfold vertex
  module

private theorem face_axis (a:Axis) : FD.face (basis a) = Signed.reflect a := by
  apply Subtype.ext
  ext i j
  change FD.faceM (basis a) i j=_
  rw [reflect_entry]
  have one : ‖basis a‖=1 := basis_norm _
  simp [FD.faceM,FD.rr,YM.basis,Free.parity]
  grind

private theorem pull (x:WickPol G) (t:Signed) : FD.pullSol t.ortho x = reflectPol t.ortho x := by
  conv_lhs => arg 2; rw [← On.lift_recover x]
  rw [← FD.watch_rot,← On.lift_signed,On.lift_recover]

def reading (a:Axis) (v:Points 2) (leg:I→Glyph B d) (i j:I) : ℂ :=
  scene v d ![E (leg j), τ (Signed.mirror a) d (E (leg i))]

omit [Fintype I] in
theorem observed (a:Axis) (leg:I→Glyph B d) (i j:I) :
    duplex (vertex a) (-(vertex a)) (Letters B (leg j)) (Letters B (leg i)) =
      reading a (nodes a) leg i j := by
  have clear : FD.barPol (Letters B (leg i)) = Letters B (leg i) := real_shell ..
  unfold reading duplex
  rw [FD.aligned_apply,clear,apart,face_axis,Signed.reflect,pull]
  rw [readHeight,readHeight,Normalize.screen]
  unfold FD.join
  apply congr_arg
  ext1 v
  fin_cases v <;> rfl

theorem original (a:Axis) (leg:I→Glyph B d) (entire:Injective leg) :
    ∃ k δ:ℝ, 0<k ∧ 0<δ ∧ ∀ (p:I→I→ℂ), ‖p-reading a (nodes a) leg‖≤δ →
      ∀ x:I→ℂ, k*‖x‖^2≤‖assay x x p‖ := by
  have distinct : vertex a ≠ -(vertex a) := by
    intro eq
    have zero := apart a
    have same : vertex a - (-(vertex a)) = 0 := sub_eq_zero.mpr eq
    rw [same] at zero
    have bad := congrArg norm zero
    simp [basis_norm] at bad
  have identity : Matrix.of (reading a (nodes a) leg) =
      Matrix.of (fun i j => duplex (vertex a) (-(vertex a)) (Letters B (leg j)) (Letters B (leg i))) := by
    ext i j
    exact (observed a leg i j).symm
  apply stable
  rw [identity]
  exact FD.reflected_pd distinct _ ((illumined B d).comp leg entire)

end YM.Integration.WilsonPositionProgramPublicWickGram
