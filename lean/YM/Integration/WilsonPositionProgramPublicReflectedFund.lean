import YM.Integration.WilsonPositionProgramPublicWickGram
import YM.XSpace.Diastole

/-! The actual solved Galop point matrix on the one public inversion mesh.
All basis slots, angular channels and unit/lower entries share the same
threshold before either field or numerical perturbation is read. -/
set_option autoImplicit false
set_option warningAsError true
noncomputable section
namespace YM.Integration.WilsonPositionProgramPublicReflectedFund
open Function Filter Set Source Labels Maxwell Maxwell.Free MS MS.Menus MS.Theater
open XSpace XSpace.Normalize XSpace.Structure1 XSpace.Rose XSpace.Cirrus XSpace.Retirement
open Local.Physical Extra Extra.FD
open WilsonPositionProgramPublicWickGram WilsonPositionProgramPublicContrast
open scoped Topology BigOperators Classical
variable {G:Gauge} {d:ℕ} {I:Type} [Fintype I] {B : Local.Physical.Deck G}
    (W:Initialize G) (V:Normalize.Store G) (a:Axis) (leg:I→Glyph B d)

def fields (i j:I) : Tags G d 2 :=
  ![Theater.Daylight B d (leg j),τ (Signed.mirror a) d (Theater.Daylight B d (leg i))]

def matrix (x:Sample 2) (i j:I) : ℂ := cooked W V d x 0 (fields a leg i j)

omit [Fintype I] in
theorem earned : Tendsto (matrix W V a leg) (Gate (nodes a)) (𝓝 (reading a (nodes a) leg)) := by
  have distinct : vertex a ≠ -(vertex a) := by
    intro eq
    have zero := apart a
    rw [sub_eq_zero.mpr eq] at zero
    have bad:=congrArg norm zero
    simp [basis_norm] at bad
  have sep := FD.couple_ok distinct
  exact tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
    scans0 W V d (fields a leg i j) (nodes a) sep

theorem original (each:Injective leg) :
    ∃ k δ ρ:ℝ, 0<k ∧ 0<δ ∧ 0<ρ ∧ ∀ᶠ M in Front, ∀ (u:pack 2) (c:Four ℝ), c∈M.Box →
      dist (M.rel u c) (nodes a)<ρ → ∀ (p:I→I→ℂ), ‖p-matrix W V a leg ⟨M,u,c⟩‖≤δ →
        ∀ v:I→ℂ, k*‖v‖^2≤‖WilsonPositionProgramPublicContrast.assay v v p‖ := by
  obtain ⟨k,t,hk,ht,cap⟩ := WilsonPositionProgramPublicWickGram.original a leg each
  have close := Metric.tendsto_nhds.mp (earned W V a leg) (t/2) (half_pos ht)
  obtain ⟨ρ,hρ,price⟩ := gate_senses (nodes a) close
  refine ⟨k,t/2,ρ,hk,half_pos ht,hρ,?_⟩
  filter_upwards [price] with M due u c hc near p hp
  apply cap
  have mid := due u c hc near
  rw [dist_eq_norm] at mid
  exact (norm_sub_le_norm_sub_add_norm_sub p (matrix W V a leg ⟨M,u,c⟩) _).trans (by linarith)

end YM.Integration.WilsonPositionProgramPublicReflectedFund
